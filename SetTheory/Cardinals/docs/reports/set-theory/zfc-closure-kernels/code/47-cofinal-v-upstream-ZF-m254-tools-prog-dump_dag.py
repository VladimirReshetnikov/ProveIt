import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.normpath(os.path.join(HERE, '..', '..', 'logic')))
from build_dag import load_dag
nodes, regidx = load_dag()
for n in sorted(nodes):
    print(n, nodes[n])
