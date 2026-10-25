#!/usr/bin/env python3
"""Verify sealed deliverable bytes and independently check the main SOS census.

This finite audit does not replace the ordinary mathematical proofs.
"""
from pathlib import Path
from collections import defaultdict
import gzip,hashlib,json

ROOT=Path(__file__).resolve().parent
def require(value,message):
    if not value:raise ValueError(message)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

manifest=json.loads((ROOT/'MANIFEST.json').read_text())
for row in manifest['files']:
    p=ROOT/row['path']
    require(p.is_file(),'Missing '+row['path'])
    require(p.stat().st_size==row['bytes'],'Size '+row['path'])
    require(sha(p)==row['sha256'],'Hash '+row['path'])

res=json.loads((ROOT/'direct/equation/equation.json').read_text())
poly=json.loads((ROOT/'direct/equation/expanded_polynomial.json').read_text())
counts=defaultdict(int)
live=set()
for row in res['residuals']:
    ts=row['terms']
    for c,m in ts:
        require(len(m)<=2,'Nonquadratic residual')
        live.update(m)
    for a,ma in ts:
        for b,mb in ts:counts[tuple(sorted(ma+mb))]+=a*b
counts={m:c for m,c in counts.items() if c}
emitted={tuple(m):c for c,m in poly['terms']}
require(counts==emitted,'Collected polynomial')
metrics={'variables':len(res['variables']),'residuals':len(res['residuals']),
         'degree':max(map(len,counts)),'monomials':len(counts),
         'coefficient_height':max(map(abs,counts.values()))}
require(metrics=={'variables':252,'residuals':182,'degree':4,'monomials':5340,'coefficient_height':128446},'Direct metrics')
require(live==set(range(252)),'Coordinate liveness')
appendix=json.loads((ROOT/'verification/appendix_generation.json').read_text())
require(appendix['equation_sha256']==sha(ROOT/'direct/equation/equation.json'),'Appendix source')
require(appendix['appendix_sha256']==sha(ROOT/'report/residuals.tex'),'Printed appendix')
native={}
for r,expected in [('47',207214),('49',216030)]:
    d=ROOT/('radix'+r)/('radix'+r)
    binding=json.loads((d/'construction_report.json').read_text())['binding']
    total=0
    for name,row in binding.items():
        p=d/row['file'];data=gzip.decompress(p.read_bytes())
        require(hashlib.sha256(data).hexdigest()==row['raw_sha256'],'Raw native coefficient '+r+'/'+name)
        require(len(data)==row['raw_bytes'],'Raw length')
        require(int.from_bytes(data,'little').bit_length()==row['bits'],'Native bit length')
        total+=len(data)
    require(total==expected,'Native storage')
    native[r]=total
inventory=json.loads((ROOT/'RESULTS.json').read_text())
require(inventory['direct']['metrics']==metrics,'Results metadata')
require(inventory['native47']['raw_coefficient_bytes']==native['47'],'Radix47 results')
require(inventory['native49']['raw_coefficient_bytes']==native['49'],'Radix49 results')
print(json.dumps({'status':'PASS','sealed_files':len(manifest['files']),
    'direct':metrics,'native_raw_bytes':native,'appendix_matches_equation':True,
    'scope':'Exact finite bytes and polynomial data; unbounded semantics are supplied by the ordinary proofs.'},indent=2))
