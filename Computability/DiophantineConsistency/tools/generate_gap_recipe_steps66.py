#!/usr/bin/env python3
"""Emit local node equations and base-power identities for the pinned H2082 DAG."""
from pathlib import Path
import argparse,importlib.util,json
ROOT=Path(__file__).resolve().parents[1]
def module(name,path):
 s=importlib.util.spec_from_file_location(name,path);g=importlib.util.module_from_spec(s);s.loader.exec_module(g);return g
g=module('gap',ROOT/'tools/generate_gap_circuit66.py')
template=module('steps',ROOT/'tools/generate_split_recipe_steps59.py')
doc,_=g.read('natural');nodes=doc['nodes'];base=doc['named_nodes']['B'];labels=[0]*len(nodes)
for i,n in enumerate(nodes):
 if i==base:labels[i]=1
 elif n['kind']=='mul'and labels[n['left']]and labels[n['right']]:labels[i]=labels[n['left']]+labels[n['right']]

def render():
 template.g=g;template.doc=doc;template.nodes=nodes;template.base=base;template.labels=labels
 return template.render().replace('SplitCircuitSteps59','GapCircuitSteps66').replace('SplitCircuit59','GapCircuit66').replace('generate_split_recipe_steps59.py','generate_gap_recipe_steps66.py').replace('Fin 12','Fin 11').replace('split116 parent','H2082')

if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--check',action='store_true');a=ap.parse_args()
 p=ROOT/'Lean/DiophantineConsistency/GapCircuitSteps66.lean';s=render()
 if a.check:g.require(p.read_text(encoding='utf-8')==s,'generated local steps differ')
 else:p.write_text(s,encoding='utf-8',newline='\n')
 print(json.dumps({'status':'PASS'if a.check else'GENERATED','parent':g.PINS['natural'],'equations':len(nodes),'powers':sum(e!=0 for e in labels)-1,'base':base},sort_keys=True))
