import gcc
import pdb
import uuid

from typing import Callable

from os.path import basename

# We'll implement this as a custom pass, to be called directly after the
# builtin "cfg" pass, which generates the CFG.

# the object graph of gcc seems to be unbounded, for instance it contains an infinite
# number of pointer types (*a, **a, ***a, ...). WW

BLACKLIST = ["unsigned_equivalent", "signed_equivalent", "sizeof",
             "fullname", # only available in C++
             "callgraph_node", # workaround,  causes segmentation fault in one case
             "str_no_uid" # not relevant for rdf graph
             ]

# because using the blacklist we got a VERY big, verbose graph,
# we now try it using a whitelist
ALL = uuid.uuid4() # signs "export all properties"
WHITELIST = {gcc.BasicBlock: ALL,
             gcc.Edge: ALL,
             gcc.GimpleAssign: ["lhs", "loc", "rhs"],
             gcc.SsaName: ["def_stmt"],
             gcc.ArrayRef: ["array", "index", "location"],
             gcc.IntegerCst: ["constant"],
             gcc.MemRef: ["location", "operand"],
             gcc.ParmDecl: ["location", "name"],
             gcc.Location: ["file", "line"],
             gcc.GimpleCond: ["block", "lhs", "loc", "rhs"],
             gcc.AddrExpr: ["location", "operand"],
             gcc.GimpleCall: ["args", "block", "fn", "fndecl", "loc", "noreturn", "rhs"],
             gcc.GimpleReturn: ["block", "loc"],
             gcc.GimpleLabel: ["label"],
             gcc.LabelDecl: ["location"],
             gcc.VarDecl: ["location", "name"],
             gcc.FunctionDecl: ["arguments", "function", "location", "name", "result"],
             gcc.Function: ["cfg", "decl", "end", "local_decls"],
             gcc.Cfg: ALL
             }
TYPE_BLACKLIST = (gcc.PointerType, gcc.IntegerType, gcc.VoidType, gcc.RealType, gcc.BooleanType, gcc.TypeDecl)

def iter_triples(prefix:str, start):
    '''
    iterates over all triples for the object graph
    '''
    open = [start]
    closed = {} # iri -> obj
    hashes = {} # int -> int

    def make_uri(obj):
        '''
        creates uri for node by looking at specific property depending on the type
        '''
        # h is the hash value

        # we use GUIDs for functions because the nodes must identify
        # in order to merge local cfgs into a supergraph
        if isinstance(obj, gcc.FunctionDecl):
            return "functions:" + obj.name # TODO handle module namespace

        try:
            h = hash(obj.str_no_uid) # GIMPLE statements have these
        except AttributeError:
            try:
                propnames = {gcc.BasicBlock: ["index"],
                            gcc.FunctionDecl: ["name"],
                            gcc.Location: ["column", "line", "file"]}[type(obj)]
                h = hash(tuple((p, getattr(obj, p)) for p in propnames))
            except KeyError:
                h = id(obj)

        try:
            identifier = hashes[h]
        except KeyError:
            hashes[h] = len(hashes)+1
            identifier = hashes[h]

        name = "{}.{}".format(type(obj).__name__, identifier)
        return "_:{}.{}".format(prefix, name)

    def repr_literal(obj):
        '''
        returns string representation of literal or None, if this is a node
        '''
        if isinstance(obj, bool):
            return str(obj).lower()
        elif isinstance(obj, (int, float, str)):
            return repr(obj)
        elif obj is None:
            return None # null values cannot be represented explicitely in RDF (they are represented by omission)
        else:
            return None

    def repr_obj(obj):
        '''
        returns rdf representation of object
        '''
        r = repr_literal(obj)
        if r is not None:
            return r, "literal"
        elif isinstance(obj, (list, tuple)):
            return "({})".format(" ".join(str(repr_obj(e)[0]) for e in obj)), "list"
        else:
            return make_uri(obj), "node"

    def iter_relevant_props(obj):
        if isinstance(obj, dict):
            iterator = obj.items()
        else:
            iterator = ((p, getattr(obj, p)) for p in dir(obj) if not p.startswith("__") and p not in BLACKLIST)
        iterator = ((p, e) for p, e in iterator if not isinstance(e, Callable))
        iterator = ((p, e) for p, e in iterator if not e is None)

        for p, e in iterator:
            try:
                if WHITELIST[type(obj)] == ALL:
                    yield p, e
                elif p in WHITELIST[type(obj)]:
                    yield p, e
            except KeyError:
                pass

        return iterator

    def solve_node(obj):
        '''
        adds - if necessary - the neighbouring nodes of obj to the open list
        '''
        #print(type(obj), id(obj))
        if isinstance(obj, TYPE_BLACKLIST):
            return
        r, obj_type = repr_obj(obj)

        if obj_type == "literal":
            return # this is not a node
        elif obj_type == "list":
            for entry in obj:
                open.append(entry)
        elif obj_type == "node":
            if r in closed:
                return
            closed[r] = obj

            for prop, entry in iter_relevant_props(obj):
                #print(prop, type(entry))
                open.append(entry)
        else:
            assert False

    def is_rdf_none(value):
        if value is None:
            return True
        if isinstance(value, (list, tuple)) and len(value) == 0:
            return True
        else:
            return False

    def yield_triples(node):
        rn, _ = repr_obj(node)
        yield "{} rdf:a gcc:{}.".format(rn, type(node).__name__)
        for prop, value in iter_relevant_props(node):
            if not is_rdf_none(value): # None and empty list is expressed in RDF by omission
                r, obj_type = repr_obj(value)
                yield "{} gcc:{} {}.".format(rn, prop, r)

    while len(open) > 0:
        node = open.pop()
        solve_node(node)
        #if len(open) > 1000:
        #    pdb.set_trace()
        #print(len(open))

    #print(closed)
    for node in closed.values():
        yield from yield_triples(node)

    del closed

print("@prefix rdf:<http://www.w3.org/1999/02/22-rdf-syntax-ns#> .")
print("@prefix gcc:<http://www.gcc.org>.")
print("@prefix functions:<http://www.functions.com>.")

class ShowGimple(gcc.GimplePass):
    def execute(self, fun):

        prefix = "{}_{}".format(".".join(basename(fun.decl.location.file).split(".")[:-1]),
                                fun.decl.name)

        for line in iter_triples(prefix, fun):
            print(line)

ps = ShowGimple(name='show-gimple')
ps.register_after('cfg')
