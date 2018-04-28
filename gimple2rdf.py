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

# for development/debugging purposes
# it is convenient to be able to express
# "export ALL properties" of object to RDF
ALL = uuid.uuid4()

# because using the blacklist we got a VERY big, verbose graph,
# we now try it using a whitelist
# for each type all properties to expand the graph traversal on are
# listed. Those that should NOT be expressed in RDF (a minority) are
# given in brackets.
WHITELIST = {gcc.BasicBlock: ["gimple", "(succs)", "(preds)"],
             gcc.Edge: ["src", "dest"],
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
             gcc.Cfg: ["basic_blocks", "entry", "exit"]
             }
# we now analyse WHITELIST, find the cases where an RDF expression
# shall be suppressed and create a separate dict for them as well as
# overwriting WHITELIST with a bracket-less variant (to correctly match
# the actual properties)
def to_be_suppressed(w: str) -> bool:
    return w[0] == '(' and w[-1] == ')'
def filter_whitelist(wl):
    if wl is ALL:
        return wl
    else:
        return [w[1:-1] if to_be_suppressed(w) else w for w in wl]
# contains pairs (type, property) which should not be expressed in rdf
SHOULD_BE_SUPPRESSED = [(t, w[1:-1]) for t, wl in WHITELIST.items() if not WHITELIST[t] is ALL for w in wl if to_be_suppressed(w)]
WHITELIST = dict((t, filter_whitelist(wl)) for t, wl in WHITELIST.items())

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

        # - we use GUIDs for functions because the nodes must identify
        #   in order to merge local cfgs into a supergraph
        # - we use GUIDs for locations because in their nature they already
        #   describe globally unique identities
        if isinstance(obj, gcc.FunctionDecl):
            return "functions:{}".format(obj.name) # TODO handle module namespace
        elif isinstance(obj, gcc.Location):
            return "<file://{}#{}>".format(obj.file, obj.line)
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

        name = "{}_{}".format(type(obj).__name__, identifier)
        return "{}:{}".format(prefix, name)

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
            if len(obj) == 0:
                return "nil", "literal"
            else:
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
                if WHITELIST[type(obj)] is ALL or p in WHITELIST[type(obj)]:
                    express = not (type(obj), p) in SHOULD_BE_SUPPRESSED
                    yield p if express else p[1:-1], e, express
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

            for prop, entry, express in iter_relevant_props(obj):
                #print(prop, type(entry))
                open.append(entry)
        else:
            assert False

    def is_rdf_none(value):
        if value is None:
            return True
        else:
            return False

    def yield_triples(node):
        rn, _ = repr_obj(node)
        yield "{} a gcc:{}.".format(rn, type(node).__name__)
        for prop, value, express in iter_relevant_props(node):
            if express and not is_rdf_none(value): # None is expressed in RDF by omission
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

        print("@prefix {prefix}:<http://www.{prefix}.com>.".format(prefix=prefix))
        for line in iter_triples(prefix, fun):
            print(line)

ps = ShowGimple(name='show-gimple')
ps.register_after('cfg')
