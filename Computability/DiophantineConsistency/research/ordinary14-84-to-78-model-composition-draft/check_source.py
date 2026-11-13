#!/usr/bin/env python3
"""Composition source inventory and receipt replay; never invokes Lean."""
from pathlib import Path
import hashlib,itertools,json,re,subprocess,sys
D=Path(__file__).resolve().parents[2];H=Path(__file__).resolve().parent
p1=D/'research/ordinary14-direct-first-root-positive-client-draft';p2=D/'research/ordinary14-aux-graph-equivalence-draft'
paths=[H/'ModelComposition.lean',p1/'PositiveClient.lean',p2/'AuxGraphEquivalence.lean']
s=paths[0].read_text()
for n in ('positive_zero_iff','positive_zero_iff_natural_ports'):
 assert re.search(r'\btheorem\s+'+n+r'\b',s)
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
assert '(hbeta : 0<beta)' in s and '(hport : (p 0 : DiffRing V)=ι beta)' in s and s.count(').trans')==2
for p in (p1,p2):
 t=(p/('PositiveClient.lean' if p==p1 else 'AuxGraphEquivalence.lean')).read_text()
 assert '(hbeta : 0<beta)' in t and '(hport : (p 0 : DiffRing V)=ι beta)' in t and 'P79DirectPell.graph' in t
 r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=60)
 assert not r.stderr and r.stdout==(p/'observation.json').read_bytes()
for x,y,z in itertools.product((False,True),repeat=3):
 if (x==y) and (y==z):assert x==z
print(json.dumps({'scope':'source inventory and component receipt replay only; no Lean invocation','components_replayed':2,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
