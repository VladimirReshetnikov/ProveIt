"""Compile the reviewed source copy (source_local.py) with Wade's TMBuilder and extract its program DAG.

Writes m254_wade.tm (Wade-framework TM: states named after subroutines) and prints DAG statistics.
The Wade-framework compilation is only a vehicle for the program graph: the third party's 254-state
table uses its own interpreter, but the program (decision DAG over the 9 registers) is the same source.

Usage: python build_dag.py            (from any directory)
Import: from build_dag import load_dag  ->  (nodes, regidx)
"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
ZF = os.path.normpath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, os.path.join(ZF, 'ext', 'turing_machine_explorer'))
sys.path.insert(0, os.path.join(ZF, 'tools'))
sys.path.insert(0, HERE)

TM_PATH = os.path.join(HERE, 'm254_wade.tm')

def build():
    import source_local
    z = source_local.ZF2()
    z.debug = False
    z.build_machine()
    z.tm.save(TM_PATH)
    return z

def load_dag():
    import dag
    if not os.path.exists(TM_PATH):
        build()
    start, tbl, nodes, regidx = dag.extract(TM_PATH)
    return nodes, regidx

if __name__ == '__main__':
    z = build()
    nstates = len(set(s[0] for s in z.tm.states))
    ndag = len(set(s[0] for s in z.tm.states if s[0][0] not in '0123456789'))
    print('states', nstates, 'dag', ndag, 'framework', nstates - ndag)
    nodes, regidx = load_dag()
    print('nodes', len(nodes), 'regidx', regidx)
    from collections import Counter
    print(Counter(e[0] for n in nodes.values() for e in n))
