#!/usr/bin/env python3
"""Check the source graph by two resolvers and export the finite abstraction input."""
from pathlib import Path
import argparse,json,sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'reference'))
import source_language as src
ap=argparse.ArgumentParser()
ap.add_argument('output',type=Path)
args=ap.parse_args()
names={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
sites=[[p if isinstance(p,str) else ''.join(map(str,p)),names[op],a]
       for p,op,a in json.loads((HERE/'input/sites.json').read_text())]
graph,checks=src.graph_arithmetic(sites)
assert graph==src.graph_intervals(sites)
instructions=json.loads((HERE/'input/instructions.json').read_text())
converted=[];coded=[]
for effect,targets in graph:
 if effect[0]=='increment':converted.append(['inc',effect[1],*targets]);coded.append([0,effect[1],targets[0],-1])
 elif effect[0]=='decrement':converted.append(['dec',effect[1],*targets]);coded.append([1,effect[1],*targets])
 elif effect[0]=='identity':converted.append(['jump',*targets]);coded.append([2,0,targets[0],-1])
 else:converted.append(['halt']);coded.append([3,0,0,0])
assert instructions==converted
assert len(coded)==3671
args.output.parent.mkdir(parents=True,exist_ok=True)
args.output.write_text(str(len(coded))+'\n'+''.join(' '.join(map(str,row))+'\n'for row in coded))
print('Source graph matches both independent resolvers:',len(coded),'sites,',checks,'successor checks')
