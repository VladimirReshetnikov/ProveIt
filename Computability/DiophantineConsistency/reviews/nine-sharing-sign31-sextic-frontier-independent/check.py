#!/usr/bin/env python3
"""Independent source/degree audit of f²-coordinate elimination; no Lean."""
import hashlib,gzip,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign31-sextic-candidate';O=D/'research/nine-sharing-sign32-sextic-candidate-v2/seed.json';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'build.py':'dc2ab36a55f32f5603d5ea32d3856e661a0f69b4d788471a033800bad65f38b8','check.py':'a41fe2f4e0b04ae789cc133fed5d9482319bbddf218edda174a28417894e36a0','seed.json':'827740a7f65961bd1a04ae424f4c8873a636285d2b1410bb72d0bee7e3e9e6c1','result.json':'1da9cad5e0ddcba02dfe8ba895174d1302c4c54b250ebc809897038547b77413'}.items():assert sha(P/n)==h
assert sha(O)=='f26172a2cad6e6a8fda042c67821f2fa7651426a62e980173eb5fac07cd835ab';old=json.loads(O.read_bytes());new=json.loads((P/'seed.json').read_bytes())
assert (new['witness_count'],new['total_coordinates'],new['distinguished_input_coordinate'])==(31,32,0) and old['witness_count']==32 and len(old['residuals'])==23 and len(new['residuals'])==22
assert (P/new['source']).resolve()==O and new['source_sha256']==sha(O) and new['fixed_ports']==old['fixed_ports'] and new['coefficient_binding']==old['coefficient_binding']
f=['add',['var',5],['num',1]];f2=['mul',f,f];assert new['substituted_f2']==f2
removed=[(i,r) for i,r in enumerate(old['residuals']) if r['gate']=='f2'];assert len(removed)==1 and removed[0][1]=={'expr':['sub',['var',27],f2],'gate':'f2','kind':'positive'}
def occurs(t,k):
 if t[0]=='var':return t[1]==k
 if t[0] in ('num','port'):return False
 return occurs(t[1],k) or occurs(t[2],k)
assert [r['gate'] for r in old['residuals'] if occurs(r['expr'],27)]==['f2','V','scaled_Ns']
def transform(t):
 op=t[0]
 if op=='var':
  i=t[1];assert type(i)==int and 0<=i<=32
  return f2 if i==27 else ['var',i-1 if i>=28 else i]
 if op in ('num','port'):return list(t)
 assert op in ('add','sub','mul') and len(t)==3
 return [op,transform(t[1]),transform(t[2])]
for a,b in zip([r for r in old['residuals'] if r['gate']!='f2'],new['residuals']):
 assert set(a)==set(b) and all(a[k]==b[k] for k in a if k!='expr') and transform(a['expr'])==b['expr']
def degree(t):
 if t[0]=='var':return 1
 if t[0] in ('num','port'):return 0
 a,b=degree(t[1]),degree(t[2]);return a+b if t[0]=='mul' else max(a,b)
def coords(t):
 if t[0]=='var':return {t[1]}
 if t[0] in ('num','port'):return set()
 return coords(t[1])|coords(t[2])
degrees={r['gate']:degree(r['expr']) for r in new['residuals']};assert max(degrees.values())==3 and {k for k,v in degrees.items() if v==3}=={'q3','tau','cTminusR','V','scaled_Ns'}
assert set.union(*(coords(r['expr']) for r in new['residuals']))==set(range(1,32))
# q3 is exactly -(beta*(x1+1)+1)^3 on the x1 axis (formal beta).
def add(a,b,sgn=1):
 d=a.copy()
 for k,v in b.items():d[k]=d.get(k,0)+sgn*v
 return {k:v for k,v in d.items() if v}
def mul(a,b):
 d={}
 for (i,j),v in a.items():
  for (k,l),w in b.items():d[i+k,j+l]=d.get((i+k,j+l),0)+v*w
 return {k:v for k,v in d.items() if v}
def poly(t):
 op=t[0]
 if op=='num':return {(0,0):t[1]} if t[1] else {}
 if op=='port':assert t[1]=='beta';return {(0,1):1}
 if op=='var':return {(1,0):1} if t[1]==1 else {}
 a,b=poly(t[1]),poly(t[2]);return mul(a,b) if op=='mul' else add(a,b,1 if op=='add' else -1)
q={(1,1):1,(0,1):1,(0,0):1};cube=mul(mul(q,q),q);assert new['residuals'][0]['gate']=='q3' and poly(new['residuals'][0]['expr'])=={k:-v for k,v in cube.items()} and poly(new['residuals'][0]['expr'])[(3,3)]==-1
binding=new['coefficient_binding'];assert (P/binding['path']).is_dir()
for k in ('certificate','ordinary_proof'):assert sha((P/binding[k]).resolve())==binding[k+'_sha256']
for n,m in binding['ports'].items():
 p=(P/binding['path']/m['file']).resolve();z=p.read_bytes();raw=gzip.decompress(z);v=int.from_bytes(raw,'big');assert hashlib.sha256(z).hexdigest()==m['gzip_sha256'] and hashlib.sha256(raw).hexdigest()==m['raw_sha256'] and len(raw)==m['raw_bytes'] and v.bit_length()==m['bits'] and v>0
for script,args in [('build.py',['--check']),('check.py',[])]:
 x=subprocess.run([sys.executable,'-I','-S','-B',str(P/script),*args],capture_output=True,timeout=30,check=True);assert not x.stderr
 if script=='check.py':assert x.stdout==(P/'result.json').read_bytes()
 else:assert json.loads(x.stdout)['status']=='PASS_REPRODUCIBLE_AST_ONLY'
print(json.dumps({'status':'PASS_SOURCE_ONLY','old_residuals':23,'new_residuals':22,'witnesses':31,'eliminated_old_coordinate':27,'other_affected_residuals':['V','scaled_Ns'],'degree_upper':6,'degree_lower_argument':'q3 x1^3 coefficient -beta^3, so sum of squares x1^6 coefficient >= beta^6 > 0','coefficient_paths':'all four gzip/raw pins, certificate and proof paths resolve','scope':'external AST and mathematical argument only; no Lean bridge or iPRA endpoint'},indent=2,sort_keys=True))
