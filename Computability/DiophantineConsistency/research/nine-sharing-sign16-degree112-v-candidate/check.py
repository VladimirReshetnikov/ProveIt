#!/usr/bin/env python3
"""Check conditional signed-V AST substitution and external degree witness."""
import gzip,hashlib,json,random,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
here=Path(__file__).resolve().parent;oldp=here.parent/'nine-sharing-sign17-degree96-vdifference-candidate/seed.json';newp=here/'seed.json';sha=lambda b:hashlib.sha256(b).hexdigest();assert sha(oldp.read_bytes())=='0323ee371aac07604617495952c6a5e0b7ead5e66697a485a05358fb447689ac';assert sha(newp.read_bytes())=='564ac66abad0fb5e286e5c0c05b5c3cbd05de13e68c9c9ac0b7c3a20a0c0b624';old,new=(json.loads(p.read_bytes()) for p in (oldp,newp));assert old['witness_count']==17 and new['witness_count']==16 and new['total_coordinates']==17 and new['distinguished_input_coordinate']==0;assert old['fixed_ports']==new['fixed_ports'] and old['coefficient_binding']==new['coefficient_binding'];row,=[r for r in old['residuals'] if r['gate']=='V'];assert row['expr'][:2]==['sub',['var',17]];replacement=row['expr'][2];assert new['lift_expression']==replacement
# The retained Na equation uses the removed witness only as its square.
naold,=[r for r in old['residuals'] if r['gate']=='Na']
def count_var(t, index):
 if t[0]=='var':return int(t[1]==index)
 if t[0] in ('num','port'):return 0
 return count_var(t[1],index)+count_var(t[2],index)
def count_square(t, index):
 if t[0] in ('var','num','port'):return 0
 return int(t==['mul',['var',index],['var',index]])+count_square(t[1],index)+count_square(t[2],index)
assert count_var(naold['expr'],17)==2 and count_square(naold['expr'],17)==1
assert all(count_var(r['expr'],17)==0 for r in old['residuals'] if r['gate'] not in ('V','Na'))
def matches(a,b):
 if a[0]=='var':return b==(replacement if a[1]==17 else ['var',a[1]-(a[1]>17)])
 if a[0] in ('num','port'):return a==b
 return a[0] in ('add','sub','mul') and len(a)==len(b)==3 and a[0]==b[0] and matches(a[1],b[1]) and matches(a[2],b[2])
remaining=[r for r in old['residuals'] if r['gate']!='V'];assert len(remaining)==len(new['residuals'])==7
for a,b in zip(remaining,new['residuals']):
 assert a.keys()==b.keys()
 for key in a:assert matches(a[key],b[key]) if key=='expr' else a[key]==b[key]
def degree(t):
 if t[0]=='var':assert 0<=t[1]<17;return 1
 if t[0] in ('num','port'):return 0
 a,b=degree(t[1]),degree(t[2]);return a+b if t[0]=='mul' else max(a,b)
degrees={r['gate']:degree(r['expr']) for r in new['residuals']};assert max(degrees.values())==56
def plus(a,b,sign=1):
 out=dict(a)
 for k,v in b.items():out[k]=out.get(k,0)+sign*v
 return {k:v for k,v in out.items() if v}
def poly(t):
 op=t[0]
 if op=='num':return {(0,0):t[1]} if t[1] else {}
 if op=='var':return {(1,0):1} if 1<=t[1]<=16 else {}
 if op=='port':assert t[1]=='beta';return {(0,1):1}
 a,b=poly(t[1]),poly(t[2])
 if op=='add':return plus(a,b)
 if op=='sub':return plus(a,b,-1)
 out={}
 for (i,j),x in a.items():
  for (k,l),y in b.items():out[(i+k,j+l)]=out.get((i+k,j+l),0)+x*y
 return {k:v for k,v in out.items() if v}
na,=[r for r in new['residuals'] if r['gate']=='Na']
def uses_input(t):return t[0]=='var' and t[1]==0 if t[0] in ('var','num','port') else uses_input(t[1]) or uses_input(t[2])
assert not uses_input(na['expr']);q=poly(na['expr']);assert max(i for i,_ in q)==56 and {k:v for k,v in q.items() if k[0]==56}=={(56,34):64}
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
rng=random.Random(1716);cases=[]
for _ in range(16):cases.append(([rng.randrange(4) for _ in range(17)],{name:rng.randrange(3) for name in new['fixed_ports']}))
v=[0]*17;v[16]=100;cases.append((v,{name:1 for name in new['fixed_ports']}));natural=0
for v,ports in cases:
 gap=ev(replacement,v,ports);lift=v+[gap];natural+=gap>=0;assert ev(row['expr'],lift,ports)==0;assert [ev(x['expr'],lift,ports) for x in remaining]==[ev(x['expr'],v,ports) for x in new['residuals']]
assert natural>0
assert json.loads(subprocess.run([sys.executable,'-I','-S','-B',str(here/'build.py'),'--check'],capture_output=True,text=True,check=True,timeout=120).stdout)['status']=='PASS'
print(json.dumps({'status':'PASS_EXTERNAL_CONDITIONAL_CHECK','source_sha256':sha(oldp.read_bytes()),'candidate_sha256':sha(newp.read_bytes()),'residuals':7,'residual_syntactic_degrees':degrees,'Na_t56_coefficient':'64*beta^34','exact_seed_degree_if_beta_nonzero':112,'coefficient_gzip_sha256':files,'finite_integer_lifts':len(cases),'finite_natural_lifts':natural,'scope':'Signed substitution only; nonnegative lift, equivalence, Lean and iPRA endpoint unproved.'},indent=2,sort_keys=True))
