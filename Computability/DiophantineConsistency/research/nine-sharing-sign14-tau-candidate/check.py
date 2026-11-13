#!/usr/bin/env python3
"""External signed-tau substitution and fixed-port degree witness; no equivalence claim."""
import gzip,hashlib,json,random,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
here=Path(__file__).resolve().parent;oldp=here.parent/'nine-sharing-sign15-inner-candidate/seed.json';newp=here/'seed.json';sha=lambda b:hashlib.sha256(b).hexdigest();assert sha(oldp.read_bytes())=='bdd841f25618a01e659d6f2f802f0420501b00c5270df9fa56b9589733ecbd59';assert sha(newp.read_bytes())=='7048a10d409ab5ff8031a444cd32117ba772b3834425c17a066188338e189ea9';old,new=(json.loads(p.read_bytes()) for p in (oldp,newp));assert old['witness_count']==15 and new['witness_count']==14 and new['total_coordinates']==15 and new['distinguished_input_coordinate']==0;assert old['fixed_ports']==new['fixed_ports'] and old['coefficient_binding']==new['coefficient_binding'];row,=[r for r in old['residuals'] if r['gate']=='tau'];assert row['expr'][:2]==['sub',['var',15]];replacement=row['expr'][2];assert new['lift_expression']==replacement
def count_var(t,index):
 if t[0]=='var':return int(t[1]==index)
 if t[0] in ('num','port'):return 0
 return count_var(t[1],index)+count_var(t[2],index)
assert count_var(replacement,15)==0
assert [(r['gate'],count_var(r['expr'],15)) for r in old['residuals']]==[('Dc2',0),('tau',1),('N0',2),('Nt',0),('Na',0),('scaled_Ns',0)]
def matches(a,b):
 if a[0]=='var':return b==(replacement if a[1]==15 else ['var',a[1]-(a[1]>15)])
 if a[0] in ('num','port'):return a==b
 return a[0] in ('add','sub','mul') and len(a)==len(b)==3 and a[0]==b[0] and matches(a[1],b[1]) and matches(a[2],b[2])
remaining=[r for r in old['residuals'] if r['gate']!='tau'];assert len(remaining)==len(new['residuals'])==5
for a,b in zip(remaining,new['residuals']):
 assert a.keys()==b.keys()
 for k in a:assert matches(a[k],b[k]) if k=='expr' else a[k]==b[k]
def degree(t):
 if t[0]=='var':assert 0<=t[1]<15;return 1
 if t[0] in ('num','port'):return 0
 a,b=degree(t[1]),degree(t[2]);return a+b if t[0]=='mul' else max(a,b)
degrees={r['gate']:degree(r['expr']) for r in new['residuals']};assert degrees=={'Dc2':22,'N0':22,'Nt':2,'Na':62,'scaled_Ns':46}
def plus(a,b,sign=1):
 out=dict(a)
 for k,v in b.items():out[k]=out.get(k,0)+sign*v
 return {k:v for k,v in out.items() if v}
def poly(t):
 op=t[0]
 if op=='num':return {(0,0,0,0):t[1]} if t[1] else {}
 if op=='var':return {(1,0,0,0):1} if 1<=t[1]<=14 else {}
 if op=='port':return {{'beta':(0,1,0,0),'MC':(0,0,1,0),'MF':(0,0,0,1)}[t[1]]:1}
 a,b=poly(t[1]),poly(t[2])
 if op=='add':return plus(a,b)
 if op=='sub':return plus(a,b,-1)
 out={}
 for k,x in a.items():
  for l,y in b.items():
   m=tuple(i+j for i,j in zip(k,l));out[m]=out.get(m,0)+x*y
 return {k:v for k,v in out.items() if v}
na,=[r for r in new['residuals'] if r['gate']=='Na'];assert count_var(na['expr'],0)==0;q=poly(na['expr']);assert max(k[0] for k in q)==62 and {k:v for k,v in q.items() if k[0]==62}=={(62,34,0,0):64}
files={};binding=new['coefficient_binding'];assert (newp.parent/binding['path']).resolve()==(oldp.parent/old['coefficient_binding']['path']).resolve()
for name,rec in binding['ports'].items():
 packed=(newp.parent/binding['path']/rec['file']).read_bytes();raw=gzip.decompress(packed);assert sha(packed)==rec['gzip_sha256'] and sha(raw)==rec['raw_sha256'] and len(raw)==rec['raw_bytes']
 if name=='beta':assert int.from_bytes(raw,'big')>0
 files[name]=sha(packed)
def ev(t,v,p):
 if t[0]=='var':return v[t[1]]
 if t[0]=='num':return t[1]
 if t[0]=='port':return p[t[1]]
 a,b=ev(t[1],v,p),ev(t[2],v,p);return a+b if t[0]=='add' else a-b if t[0]=='sub' else a*b
rng=random.Random(1514);cases=[([rng.randrange(4) for _ in range(15)],{name:rng.randrange(3) for name in new['fixed_ports']}) for _ in range(16)];negative_case=[0]*15;negative_case[3]=1000;cases.append((negative_case,{'beta':10,'K0':0,'MC':0,'MF':0}));natural=0;negative=0
for v,ports in cases:
 gap=ev(replacement,v,ports);lift=v+[gap];natural+=gap>=0;negative+=gap<0;assert ev(row['expr'],lift,ports)==0;assert [ev(x['expr'],lift,ports) for x in remaining]==[ev(x['expr'],v,ports) for x in new['residuals']]
assert natural and negative
assert json.loads(subprocess.run([sys.executable,'-I','-S','-B',str(here/'build.py'),'--check'],capture_output=True,text=True,check=True,timeout=120).stdout)['status']=='PASS'
print(json.dumps({'status':'PASS_EXTERNAL_CONDITIONAL_CHECK','source_sha256':sha(oldp.read_bytes()),'candidate_sha256':sha(newp.read_bytes()),'residuals':5,'residual_syntactic_degrees':degrees,'Na_t62_coefficient':'64*beta^34','exact_seed_degree_if_beta_nonzero':124,'coefficient_gzip_sha256':files,'finite_integer_lifts':len(cases),'finite_natural_lifts':natural,'finite_negative_lifts':negative,'scope':'Signed substitution only; nonnegative tau lift, equivalence, Lean and iPRA endpoint unproved.'},indent=2,sort_keys=True))
