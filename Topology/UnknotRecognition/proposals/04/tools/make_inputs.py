"""Deterministic structured inputs, additional to the supplied fixtures."""
from pathlib import Path
import json
import sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.diagram import Diagram
from fastunknot.factor import connected_sum
OUT=ROOT/'benchmarks/inputs'
OUT.mkdir(parents=True,exist_ok=True)

def write(name,d):
    (OUT/name).write_text(json.dumps(d.to_json(),indent=2)+'\n')

for knot,filename,powers in [('conway','conway.json',(2,3,8,16)),
                             ('trefoil','trefoil.json',(4,8,16))]:
    factor=Diagram.from_json(json.loads((ROOT/'fast/examples'/filename).read_text()))
    d=Diagram.from_pd([])
    for k in range(1,max(powers)+1):
        d=connected_sum(d,factor)
        if k in powers:write(f'{knot}_sum{k}.json',d)
for n in (128,256,512,1024):
    (OUT/f'unknot_chain{n}.json').write_text(json.dumps({'braid':{'strands':n+1,'word':list(range(1,n+1))}})+'\n')
# Reproduce the exact stress braid words from the supplied benchmark record.
source=json.loads((ROOT/'baseline/results/benchmark.json').read_text())
for strands,length,name in [(4,41,'four_braid_41.json'),(5,36,'five_braid_36.json')]:
    item=next(row for row in source['scan_families']
              if row['family']==f'random {strands}-braid' and row['crossings']==length)
    diagram=Diagram.from_braid(strands,item['word'])
    write(name,diagram)
    if strands==5:
        from fastunknot.simplify import simplify
        write('five_braid_reduced24.json',simplify(diagram)[0])
print('Structured and original stress fixtures written to',OUT)
