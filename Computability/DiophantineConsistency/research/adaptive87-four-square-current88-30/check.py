#!/usr/bin/env python3
"""Current-port 87→88 finalizer cut, residues, topology and degree control."""
import gzip
import hashlib
import itertools
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]; HERE=Path(__file__).resolve().parent
PINS={
 'research/adaptive-first-root-factor87/candidate.json':'da6b88365da3ec9db6040373c25de20b30baf63edc9fdf742de2aa4b2c06e6e8',
 'research/adaptive-direct-ordinate86/DEGREE-87-PARENT.md':'55661bba60da190c5b0a2bfe746daca2d7fbb7fe9253bdb11cfed8dd374eb55f',
 'Lean/DiophantineConsistency/ArithmeticAdaptiveFactorUnits2011.lean':'9e80ae52f5dddd21d50684ebb6ca6556e95ac37905277bc476d251b7bf59f5a4',
 'Lean/DiophantineConsistency/AdaptiveFirstRootFactor87Literal.lean':'c870a43ab38e37d0985c5a57a3fd090f2e64efed479d81b4665623802e8928e3',
 'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json':'f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e',
 'research/adaptive87-four-square-current88-30/graph.json':'293dac5175d4924812177a1e73a316bf5cc16bf1b5cef636388d9e110eebb7ed',
}
for path,h in PINS.items():
 if hashlib.sha256((ROOT/path).read_bytes()).hexdigest()!=h: raise RuntimeError('pin changed: '+path)
old=json.loads((ROOT/'research/adaptive-first-root-factor87/candidate.json').read_bytes());g=json.loads((HERE/'graph.json').read_bytes())
remove={'Fs','F0','F1','g86','g87','g88','P13'}
tail=[['fa_minus','-','Fa',1],['a0_sq','*','A0','A0'],['a1_sq','*','A1','A1'],['fa_sq','*','fa_minus','fa_minus'],['strong_sq','*','g72','g72'],['sum0','+','a0_sq','a1_sq'],['sum1','+','sum0','fa_sq'],['output','+','sum1','strong_sq']]
if g['source']!=[r for r in old['source'] if r[0] not in remove]+tail: raise RuntimeError('graph cut mismatch')
if g['witnesses']!=old['witnesses'] or g['fixed_numerals']!=old['fixed_numerals']: raise RuntimeError('leaf mismatch')
oldrows={r[0]:r for r in old['source']}
for row in [['q','+',1,'qm'],['q3','*','q','q2'],['M','*','q3','qm'],['g72','-','g71','Q'],['Fs','+',1,'g72'],['F0','+',1,'A0'],['F1','+',1,'A1']]:
 if oldrows.get(row[0])!=row: raise RuntimeError('factor identity mismatch: '+row[0])
known=set(g['witnesses']+g['fixed_numerals']);rows={}
for row in g['source']:
 out,op,a,b=row
 if out in known or op not in ('+','-','*') or any(isinstance(x,str) and x not in known for x in (a,b)): raise RuntimeError('topology error')
 known.add(out);rows[out]=row
need={g['output']}
for row in reversed(g['source']):
 if row[0] in need: need.update(x for x in row[2:] if isinstance(x,str))
if len(need&set(rows))!=88 or not set(g['witnesses']+g['fixed_numerals'])<=need: raise RuntimeError('liveness error')
counts={op:sum(row[1]==op for row in g['source']) for op in ('*','+','-')}
residue_counts={}
for q,z,n in itertools.product(range(4),repeat=3):
 if (1+z*z-(q**3*(q-1))**2*n)%4==3: raise RuntimeError('first exclusion false')
residue_counts['first']=4**3
for u,a,c,d in itertools.product(range(4),repeat=4):
 if (1+d*d-u*u*(1+(a*a+4*a+3)*c*c))%4==3: raise RuntimeError('main exclusion false')
residue_counts['main']=4**4
for a,f,i in itertools.product(range(4),repeat=3):
 if (1+i*i-(a*a+4*a+3)*(f*f-1))%4==3: raise RuntimeError('strong exclusion false')
residue_counts['strong']=4**3
for a,f,v,y in itertools.product(range(4),repeat=4):
 Q=(a*a+4*a+3)*(f*f-1)
 if (y*y-Q*(y*y-v*v))%4==3: raise RuntimeError('aux exclusion false')
residue_counts['auxiliary']=4**4

port_path=ROOT/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';portmeta=json.loads(port_path.read_bytes())['coefficient_binding']['ports'];ports={};prime=1000000007
for name,meta in portmeta.items():
 packed=(port_path.parent/'coefficients'/meta['file']).read_bytes();raw=gzip.decompress(packed)
 if hashlib.sha256(packed).hexdigest()!=meta['gzip_sha256'] or hashlib.sha256(raw).hexdigest()!=meta['raw_sha256'] or len(raw)!=meta['raw_bytes']: raise RuntimeError('port byte mismatch: '+name)
 ports[name]=int.from_bytes(raw,'big')%prime
def trim(x):
 while len(x)>1 and x[-1]==0: x.pop()
 return x
def plus(x,y,s):return trim([((x[j] if j<len(x) else 0)+s*(y[j] if j<len(y) else 0))%prime for j in range(max(len(x),len(y)))])
def mul(x,y):
 out=[0]*(len(x)+len(y)-1)
 for j,a in enumerate(x):
  for k,b in enumerate(y):out[j+k]=(out[j+k]+a*b)%prime
 return trim(out)
poly={**{x:[v] for x,v in ports.items()},**{x:[0,1] for x in g['witnesses']}}
def val(x):return poly[x] if isinstance(x,str) else [x%prime]
for name,op,a,b in g['source']:
 x,y=val(a),val(b);poly[name]=mul(x,y) if op=='*' else plus(x,y,1 if op=='+' else -1)
degrees={x:len(poly[x])-1 for x in ('A0','A1','Fa','g72','output')}
if degrees['output']!=30 or degrees['A0']!=15 or poly['output'][-1]==0: raise RuntimeError('actual-port diagonal lower witness failed')
print(json.dumps({'scope':'exact row cut and all mod-4 cases; degree upper bound and zero argument in README; no Lean',
 'graph_sha256':PINS['research/adaptive87-four-square-current88-30/graph.json'],
 'parent_sha256':PINS['research/adaptive-first-root-factor87/candidate.json'],'live_rows':len(rows),
 'counts':counts,'residue_cases':residue_counts,'diagonal_degrees':degrees,
 'modulus':prime,'degree30_coefficient_mod_prime':poly['output'][-1],
 'port_raw_bytes':sum(v['raw_bytes'] for v in portmeta.values())},indent=2,sort_keys=True))
