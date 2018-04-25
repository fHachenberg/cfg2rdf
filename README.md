cfg2rdf
=======

gcc python plugin to export the control flow graph as a RDF turtle file
(containing triples).

The graph can then be queried and altered using SPARQL.

Usage
-----

	gcc -fplugin=<install location of gcc-python-plugin>/python.so -fplugin-arg-python-script=gimple2rdf.py -c <sourcefile>

Requirements
------------

- gcc-python-plugin
- Python >= 3.5
- gcc >= 4.8

