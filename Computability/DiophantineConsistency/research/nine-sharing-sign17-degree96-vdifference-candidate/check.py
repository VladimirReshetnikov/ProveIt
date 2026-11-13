#!/usr/bin/env python3
"""External structural, degree, and positive-factor checks for sign17."""
import gzip,hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
here=Path(__file__).resolve().parent
old_path=here.parent/'nine-sharing-sign18-degree94-root-candidate/seed.json';new_path=here/'seed.json'
sha=lambda b:hashlib.sha256(b).hexdigest()
old_raw,new_raw=old_path.read_bytes(),new_path.read_bytes()
assert sha(old_raw)=='d3fd0a00ed9f803a5c002481dbfb22aafe9a5ba34ac89c90069cefbdcaada3fb'
assert sha(new_raw)=='0323ee371aac07604617495952c6a5e0b7ead5e66697a485a05358fb447689ac'
old,new=json.loads(old_raw),json.loads(new_raw)
assert old['witness_count']==18 and new['witness_count']==17 and new['total_coordinates']==18
assert old['distinguished_input_coordinate']==new['distinguished_input_coordinate']==0
assert old['fixed_ports']==new['fixed_ports'] and old['coefficient_binding']==new['coefficient_binding']
f=['add',['var',13],['num',1]];v=['var',17];d=['sub',['mul',f,f],['mul',v,v]]
removed,=[r for r in old['residuals'] if r['gate']=='V2minusY2']
assert removed['kind']=='signed' and removed['expr']==['sub',['var',18],d] and new['lift_expression']==d

def subst(e):
 op=e[0]
 if op=='var':return d if e[1]==18 else e[:]
 if op in ('num','port'):return e[:]
 assert op in ('add','sub','mul')
 return [op,subst(e[1]),subst(e[2])]
old_rows=[r for r in old['residuals'] if r['gate']!='V2minusY2']
assert len(old_rows)==len(new['residuals'])==8
for a,b in zip(old_rows,new['residuals']):
 assert {k:v for k,v in a.items() if k!='expr'}=={k:v for k,v in b.items() if k!='expr'}
 assert subst(a['expr'])==b['expr']

# The remaining Na equation gives F² - S²*D - 1 = 0. Verify the exact
# unshifted reconstructed R and its positive beta*(v1+1) summand.
na,=[r['expr'] for r in old_rows if r['gate']=='Na']
assert na[0]=='sub' and na[2]==['num',1] and na[1][0]=='sub'
assert na[1][1]==['mul',f,f] and na[1][2][0]=='mul' and na[1][2][2]==['var',18]
sq=na[1][2][1];assert sq[0]=='mul' and sq[1]==sq[2]
s=sq[1];assert s[0]=='mul' and s[1]==['add',['var',6],['num',1]]
assert s[2][0]=='mul';root=s[2][1];assert s[2][2]==['add',root,['num',2]]
assert root==old['lift_expression']
A=['add',['mul',['port','beta'],['add',['var',1],['num',1]]],['num',1]]
assert root[0]=='add' and root[1][0]=='add' and root[1][1][0]=='add'
assert root[1][1][1]==['mul',['var',9],A]
assert root[1][1][2]==['mul',['port','beta'],['add',['var',1],['num',1]]]
def nonnegative(e):
 if e[0]=='num':return type(e[1]) is int and e[1]>=0
 if e[0] in ('var','port'):return True
 return e[0] in ('add','mul') and nonnegative(e[1]) and nonnegative(e[2])
assert nonnegative(root)

def deg(e):
 if e[0]=='var':assert 0<=e[1]<18;return 1
 if e[0] in ('num','port'):return 0
 a,b=deg(e[1]),deg(e[2]);return a+b if e[0]=='mul' else max(a,b)
degrees={r['gate']:deg(r['expr']) for r in new['residuals']}
assert max(degrees.values())==48
# Assign all witness coordinates except V=old/new 17 to t, with V=0;
# Na uses no input coordinate zero. Coefficients are in Z[t,beta].
def uses0(e):
 if e[0]=='var':return e[1]==0
 if e[0] in ('num','port'):return False
 return uses0(e[1]) or uses0(e[2])
def add(a,b,sgn=1):
 c=a.copy()
 for k,v in b.items():c[k]=c.get(k,0)+sgn*v
 return {k:v for k,v in c.items() if v}
def poly(e):
 op=e[0]
 if op=='num':return {(0,0):e[1]} if e[1] else {}
 if op=='var':return {(1,0):1} if 1<=e[1]<=16 else {}
 if op=='port':assert e[1]=='beta';return {(0,1):1}
 a,b=poly(e[1]),poly(e[2])
 if op=='add':return add(a,b)
 if op=='sub':return add(a,b,-1)
 c={}
 for (i,j),x in a.items():
  for (k,l),y in b.items():c[(i+k,j+l)]=c.get((i+k,j+l),0)+x*y
 return {k:v for k,v in c.items() if v}
na_new,=[r['expr'] for r in new['residuals'] if r['gate']=='Na']
assert not uses0(na_new);z=poly(na_new)
assert {k:v for k,v in z.items() if k[0]>=48}=={(48,28):-16}
# Abstract finite sanity controls, not the proof: F,S positive and Na=0 imply D>=0.
for F in range(1,9):
 for S in range(1,7):
  for V in range(9):
   D=F*F-V*V
   if F*F-S*S*D-1==0:assert D>=0
# S=0 loses this implication: do not claim the beta=0 case.
assert 1-0*(1-4)-1==0 and 1-4<0
binding=new['coefficient_binding'];records={}
for name,rec in binding['ports'].items():
 packed=(new_path.parent/binding['path']/rec['file']).read_bytes();raw=gzip.decompress(packed)
 assert sha(packed)==rec['gzip_sha256'] and sha(raw)==rec['raw_sha256'] and len(raw)==rec['raw_bytes']
 if name=='beta':assert int.from_bytes(raw,'big')>0
 records[name]={'gzip_sha256':sha(packed),'raw_sha256':sha(raw),'bytes':len(raw)}
assert json.loads(subprocess.run([sys.executable,'-I','-S','-B',str(here/'build.py'),'--check'],capture_output=True,text=True,check=True,timeout=120).stdout)['status']=='PASS_BUILD'
print(json.dumps({'status':'PASS_EXTERNAL_CONDITIONAL_CANDIDATE','source_sha256':sha(old_raw),'candidate_sha256':sha(new_raw),
 'residual_degrees':degrees,'axis':'v1..v16=t, v17=0; input 0 fixed 1','Na_t48_coefficient':'-16*beta^28',
 'external_fixed_beta_degree':96,'ports':records,'lift_condition':'beta>0; Na=0 forces F^2-V^2>=0',
 'scope':'external conditional candidate; no Lean/model/iPRA bridge'},indent=2,sort_keys=True))
