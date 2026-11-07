#!/usr/bin/env python3
"""Read-only audit of the 32-witness substitution; no Lean replay."""
import hashlib, gzip, json, pathlib
D=pathlib.Path(__file__).resolve().parents[2]
C=D/'research/nine-sharing-sign32-sextic-candidate-v2'
O=D/'research/nine-sharing-quartic65-sign33-candidate/seed.json'
G=D/'candidates/one-page-padding-staircase-carrier65-2011'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
expected={'build.py':'046c6f4ced5c677cce7b1af6ba8dca194f459abad1b5719fff451ed62c13b8be','check.py':'c6b5b5415d66f5ee3e14ed980880d34c394edf1fe4f9f78404c998bd6988b063','seed.json':'f26172a2cad6e6a8fda042c67821f2fa7651426a62e980173eb5fac07cd835ab','result.json':'713122ce49cee5d820ba7362a74f3ec3175bc947644e4939c9ac102ca1e123ce'}
for f,h in expected.items(): assert sha(C/f)==h, f
assert sha(O)=='a8cd4d01962b9380065ebbd3d7b75db3ffcadf18969099398bd151c4e2219e75'
assert sha(G/'polynomial.json')=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
o=json.loads(O.read_bytes()); n=json.loads((C/'seed.json').read_bytes());g=json.loads((G/'polynomial.json').read_bytes())
assert len(o['residuals'])==24 and len(n['residuals'])==23
assert n['source_sha256']==sha(O) and (C/n['source']).resolve()==O
assert (n['witness_count'],n['total_coordinates'],n['distinguished_input_coordinate'])==(32,33,0)
assert o['jones_witness_count']==33 and o['input_coordinate']==0
assert n['fixed_ports']==o['fixed_ports']==g['fixed_numerals']
assert o['coefficient_binding']==g['coefficient_binding']
binding=dict(n['coefficient_binding']); binding['path']=g['coefficient_binding']['path']; assert binding==g['coefficient_binding']
assert (C/n['coefficient_binding']['path']).resolve()==(G/g['coefficient_binding']['path']).resolve()
q=['add',['mul',['port','beta'],['add',['var',1],['num',1]]],['num',1]]
q2=['mul',q,q]
assert n['substituted_q2']==q2
assert o['residuals'][0]=={'expr':['sub',['var',15],q2],'gate':'q2','kind':'positive'}
def transform(t):
 op=t[0]
 if op=='var':
  i=t[1]; assert type(i)==int and 0<=i<=33
  return q2 if i==15 else ['var',i-1 if i>=16 else i]
 if op in ('num','port'): return list(t)
 assert op in ('add','sub','mul') and len(t)==3
 return [op,transform(t[1]),transform(t[2])]
for i,(old,new) in enumerate(zip(o['residuals'][1:],n['residuals'])):
 assert set(old)==set(new)
 assert all(old[k]==new[k] for k in old if k!='expr'), i
 assert transform(old['expr'])==new['expr'], i
def deg(t):
 if t[0]=='var':return 1
 if t[0] in ('num','port'):return 0
 a,b=deg(t[1]),deg(t[2]);return a+b if t[0]=='mul' else max(a,b)
def coords(t):
 if t[0]=='var':return {t[1]}
 if t[0] in ('num','port'):return set()
 return coords(t[1])|coords(t[2])
degrees=[deg(r['expr']) for r in n['residuals']]
assert max(degrees)==3 and set.union(*(coords(r['expr']) for r in n['residuals']))==set(range(1,33))
assert [(r['gate'],d) for r,d in zip(n['residuals'],degrees) if d==3]==[('q3',3),('tau',3),('cTminusR',3)]
# Exact q3 univariate expansion with beta indeterminate: (x, beta) -> coefficient.
def plus(a,b,sgn=1):
 d=a.copy()
 for k,v in b.items():d[k]=d.get(k,0)+sgn*v
 return {k:v for k,v in d.items() if v}
def times(a,b):
 d={}
 for (i,j),v in a.items():
  for (k,l),w in b.items():d[i+k,j+l]=d.get((i+k,j+l),0)+v*w
 return {k:v for k,v in d.items() if v}
def polynomial(t):
 op=t[0]
 if op=='num':return {(0,0):t[1]} if t[1] else {}
 if op=='port':
  assert t[1]=='beta';return {(0,1):1}
 if op=='var':return {(1,0):1} if t[1]==1 else {}
 a,b=polynomial(t[1]),polynomial(t[2]);return times(a,b) if op=='mul' else plus(a,b,1 if op=='add' else -1)
qp={(1,1):1,(0,1):1,(0,0):1}; cube=times(times(qp,qp),qp)
assert polynomial(n['residuals'][0]['expr'])=={k:-v for k,v in cube.items()}
assert polynomial(n['residuals'][0]['expr'])[(3,3)]==-1
ports={}
for name,m in g['coefficient_binding']['ports'].items():
 p=G/g['coefficient_binding']['path']/m['file']; z=p.read_bytes(); raw=gzip.decompress(z);v=int.from_bytes(raw,'big')
 assert hashlib.sha256(z).hexdigest()==m['gzip_sha256'] and hashlib.sha256(raw).hexdigest()==m['raw_sha256'] and len(raw)==m['raw_bytes'] and v.bit_length()==m['bits'] and v>0
 ports[name]={'bits':v.bit_length(),'raw_sha256':hashlib.sha256(raw).hexdigest()}
assert n['coefficient_binding']['path']=='../../candidates/one-page-padding-staircase-carrier65-2011/coefficients/'
print(json.dumps({'status':'PASS_SOURCE_ONLY','old_residuals':24,'new_residuals':23,'witnesses':32,'coordinate_mapping':'old 15 = q^2; old 16..33 -> new 15..32','cubic_residuals':[r['gate'] for r,d in zip(n['residuals'],degrees) if d==3],'degree_upper':6,'degree_lower_argument':'q3 on x1-axis has x1^3 coefficient -beta^3; sum of squared leading coefficients is positive since beta > 0','ports':ports,'coefficient_path_scope':'v2 path resolves from candidate to source graph coefficient directory; MF_source is high mask, effective model high+beta separately bound','lean_bridge':'not checked','ipra_endpoint':'not checked'},sort_keys=True,indent=2))
