#!/usr/bin/env python3
"""Pin and verify the literal 77-row graph and fixed-port degree witness."""
import gzip
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
PINS={
 'research/fourteen-nonzero-spheres/polynomial72.json':'70d6bd4ab1f4d4a868a4718543502734d250fca6a38eb64a5b90dda8107b3280',
 'research/fourteen-nonzero-spheres/PROOF.md':'efade416bb7157651be664255745881982d60da1c613051454725694538d2437',
 'research/current2011-spheres-fresh-base/README.md':'79d9bbf8150ae502e91853dfba2ab4e8c23344bcdd20534b221398e48d7c767b',
 'Lean/DiophantineConsistency/ModelCarrierSpheres.lean':'25e3551c1fb014e958b23dbc944a230aa0db728de5e105aa510878b429a26087',
 'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json':'f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e',
}
for name,h in PINS.items():
 if hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=h: raise RuntimeError('source pin changed: '+name)
parent=json.loads((ROOT/'research/fourteen-nonzero-spheres/polynomial72.json').read_bytes())
graph=json.loads((HERE/'graph.json').read_bytes())
tail=[['Pminus','-','N0',1],['i2c2','*','i2','c2'],['corr','*','i2c2','Pminus'],['Zcorr','-','Z','corr'],['QW','*','N1','Nt'],['QWminus','-','QW',1],['Uminus','-','U',1],['Zminus','-','Zcorr',1],['Psq','*','Pminus','Pminus'],['QWsq','*','QWminus','QWminus'],['Usq','*','Uminus','Uminus'],['Zsq','*','Zminus','Zminus'],['sum1','+','Psq','QWsq'],['sum2','+','sum1','Usq'],['polynomial','+','sum2','Zsq']]
if graph['source']!=parent['source'][:62]+tail or len(graph['source'])!=77: raise RuntimeError('literal rows differ')
if graph['witnesses']!=parent['witnesses'] or graph['fixed_numerals']!=parent['fixed_numerals']: raise RuntimeError('coordinate or port mismatch')
rows={row[0]:row for row in graph['source']}; need={graph['output']}
for row in reversed(graph['source']):
 if row[0] in need: need.update(x for x in row[2:] if isinstance(x,str))
if len(need&set(rows))!=77 or not set(graph['witnesses']+graph['fixed_numerals'])<=need: raise RuntimeError('nonlive row/leaf')
counts={op:sum(row[1]==op for row in graph['source']) for op in ('*','+','-')}
old_path=ROOT/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json'
old=json.loads(old_path.read_bytes()); prime=1000000007; ports={}
for name,meta in old['coefficient_binding']['ports'].items():
 packed=(old_path.parent/'coefficients'/meta['file']).read_bytes(); raw=gzip.decompress(packed)
 if hashlib.sha256(packed).hexdigest()!=meta['gzip_sha256'] or hashlib.sha256(raw).hexdigest()!=meta['raw_sha256']: raise RuntimeError('port hash mismatch')
 ports[name]=int.from_bytes(raw,'big')%prime
if ports['beta']==0: raise RuntimeError('modular beta vanishes')

def add(x,y,sign=1):
 z=[((x[i] if i<len(x) else 0)+sign*(y[i] if i<len(y) else 0))%prime for i in range(max(len(x),len(y)))]
 while len(z)>1 and z[-1]==0: z.pop()
 return z
def mul(x,y):
 z=[0]*(len(x)+len(y)-1)
 for i,a in enumerate(x):
  for j,b in enumerate(y): z[i+j]=(z[i+j]+a*b)%prime
 while len(z)>1 and z[-1]==0: z.pop()
 return z
poly={**{k:[v] for k,v in ports.items()},**{w:[0,1] for w in graph['witnesses']}}
def val(x): return poly[x] if isinstance(x,str) else [x%prime]
for out,op,l,r in graph['source']:
 x,y=val(l),val(r); poly[out]=mul(x,y) if op=='*' else add(x,y,1 if op=='+' else -1)
degrees={k:len(poly[k])-1 for k in ('N0','N1','U','Z','Zcorr','polynomial')}
if degrees['Zcorr']!=32 or degrees['polynomial']!=64 or poly['polynomial'][-1]==0: raise RuntimeError('degree lower witness failed')
if poly['polynomial'][-1] != poly['Zcorr'][-1]**2%prime: raise RuntimeError('unexpected top-degree contribution')
if poly['Zcorr'][-1] != (-32*pow(ports['beta'],19,prime))%prime or poly['polynomial'][-1] != (1024*pow(ports['beta'],38,prime))%prime: raise RuntimeError('diagonal leading coefficient formula failed')
print(json.dumps({'graph_sha256':hashlib.sha256((HERE/'graph.json').read_bytes()).hexdigest(),
 'count':counts,'live_rows':77,'modulus':prime,'beta_mod_prime':ports['beta'],
 'diagonal_degrees':degrees,'degree64_coefficient_mod_prime':poly['polynomial'][-1],
 'scope':'source/graph and diagonal check; upper bound and zero equivalence require README proof; no Lean'},indent=2,sort_keys=True))
