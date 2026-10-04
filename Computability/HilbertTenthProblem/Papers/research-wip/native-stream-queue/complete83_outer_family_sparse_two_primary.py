#!/usr/bin/env python3
"""Fresh sparse-clause corroboration; no predecessor/helper execution."""
import argparse,hashlib,json
from pathlib import Path
BASE=Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers')
PINS={
'1980/FIXED_RAW_UNIVERSAL_77_PROOF.md':'292acdfe5ff598201c3dd9cd7defff07b45d743637c1f3836a21065888053a41',
'1980/FIXED_RAW_UNIVERSAL_78_PROOF.md':'b28ddb9aec5225cda7dabc85fb952daf49de4041cf35910f62dabf3893749d39',
'1980/FIXED_RAW_UNIVERSAL_76_PROOF.md':'75a13b5fd0c44c3ec91366306fb5876a3ea2f867e464b84cebd46ca08d060f87',
'research-wip/native-stream-queue/complete75_half_binomial_compiler.md':'68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117',
'research-wip/native-stream-queue/complete83_outer_family_two_primary.md':'fe9378a51f61d35147ec11dfed0aae8c0d0fc795d7e3afcec5cd22a01df9906b',
'research-wip/native-stream-queue/complete83_outer_family_uniform_two_primary.md':'3ad273d152dbb7a6acc2d312c9963e373adc0e194f6f9c8e685b2cebcb548e12',
'research-wip/native-stream-queue/complete83_shared_projection_scout.json':'dd9e105d295bf2fb3e3b0246234bb68cb78487ee919405bc052f2b67a9def34c'}
def ck(ok,msg):
 if not ok:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def vp2(n):
 ck(n>0,'positive valuation');return (n&-n).bit_length()-1
def nextfive(bound):
 b=1
 while b<=bound:b*=5
 return b

def fixture(a,k,extra,optional):
 w=max(2,(k+1).bit_length());A=1<<w;t=extra
 while 2*(w+9*a+3+t)+12*a+3<k+9*a+5:t+=1
 mu=A-2+sum(A**j for j in range(1,9*a+5+t))
 N=2*mu.bit_count()+12*a+3;dummy_count=N-k-9*a-4
 ck(dummy_count>=1 and mu.bit_count()==w+9*a+3+t,'mask clause census')
 exps=list(range(k));cs={e:1 for e in exps}
 for slot in range(9):
  r,c=divmod(slot,3)
  for tile in range(a):
   e=k+3*a+(2-r)*3*a+(2-c)*a+tile
   coefficient=A**(1+slot*a+tile);cs[e]=coefficient;exps.append(e)
   for selector in range(k):
    if (selector+slot)%a==tile:cs[selector]+=coefficient
 for e in range(k+12*a,k+12*a+dummy_count):exps.append(e);cs[e]=0
 E0=max(exps);M=E0+3*a+1
 for j,e in enumerate((M,3*M,9*M,27*M)):
  coefficient=A**(1+9*a+j);cs[e]=coefficient;exps.append(e)
  for selector in range(k):cs[selector]+=coefficient
 ck(len(exps)==len(set(exps))==N and M==2*w+36*a+5+2*t,'native geometry census')
 ck(M>=k+15*a and sum(c.bit_count() for c in cs.values())==14*k+9*a+4,'coefficient population census')
 lower=max(4*(N+2)*(2*sum(cs.values())+6)+8,2*mu+4,16)
 b=nextfive((lower-1).bit_length()-1)
 ck((1<<b)>=lower and b>=125 and M<3*b,'actual radix census bounds')
 H=51*M+3*a+1;T1=105*M+4*a+2;T2=159*M+4*a+3;g=186*M+4*a+4
 L=nextfive(213*M+4*a+4);d=b*L
 DC=sum(1<<(b*e) for e in (3*a,H+a,8*M,24*M))
 for e,c in cs.items():DC+=c*((1<<(b*(T1-e)))+(1<<(b*(T2-e))))
 if optional:DC+=1<<(b*g)
 K=DC+(1<<(d+b*H))
 ck(K.bit_count()<=2*(14*k+9*a+4)+6<=30*M and vp2(K)==3*a*b,'literal sparse K bounds')
 dummy=k+12*a
 missing=sum(1<<(b*e) for e in exps if e!=1)+(2<<(b*dummy))
 ck(missing.bit_count()==N,'modified native complement')
 pcMC=d-N;ck(5*pcMC>4*d,'density')
 records=[]
 for z in (1,5,4*d-3):
  F=K*z;P=F.bit_count();v=vp2(F)
  ck(v==3*a*b and P<=K.bit_count()*z.bit_count(),'F population/valuation')
  lg=d.bit_length() # strict upper bound for log2(d), since d is not a power of two.
  upper=151*M*lg+456*M+3*b*M//5
  ck(2*upper<d,'integer upper bound below d/2')
  for eps in range(-1,10):
   plus=[6*F+4*z+2-eps,6*F-4,2*F-6]
   loss=sum(vv.bit_count() for vv in plus)
   ck(all(vv>0 for vv in plus) and loss<=5*P+3*v+lg+6<=upper,'plus deficit bound')
   ck(3*5*d-loss+2*pcMC-1>3*5*d+1,'n5 lower bound')
   records.append(['plus',z,eps,loss])
   if eps<=8:
    minus=[6*F+4*z+2-eps,8*F-25,32];loss=sum(vv.bit_count() for vv in minus)
    ck(all(vv>0 for vv in minus) and loss<=5*P+3*v+lg+6<=upper,'minus deficit bound')
    ck(3*5*d-loss+2*pcMC-1>3*5*d+1,'n5 minus lower bound')
    records.append(['minus',z,eps,loss])
 return {'a':a,'k':k,'zero_clauses':t,'optional_high_term':optional,'w':w,'b':b,'M':M,'L':L,'d':d,'native_count':N,'K_bits':K.bit_length(),'K_population':K.bit_count(),'K_v2':vp2(K),'MC_population':pcMC,'deficit_cases':records,'synthetic_windows_only':True}

def build():
 deps=[]
 for name,pin in PINS.items():
  raw=(BASE/name).read_bytes();ck(sha(raw)==pin,'dependency '+name);deps.append({'path':name,'bytes':len(raw),'sha256':pin})
 ck((639*125**2)**2<2**125,'log bound base')
 ck(2*125**4>126**4,'log bound ratio')
 ck(10*(151*125)+20*456+12*125<10*213*125,'final rational margin')
 tiny=0
 for h in range(1,10):
  for odd in (1,3,5,11):
   T=(1<<h)*odd
   for c in range(1,1<<h):
    ck((T-c).bit_count()==T.bit_count()-1+h-(c-1).bit_count(),'subtraction population identity');tiny+=1
 fixtures=[fixture(a,k,e,opt) for a,k,e,opt in [(1,2,0,False),(1,3,1,True),(2,4,0,False),(2,5,2,True)]]
 return {'schema':'sparse compiler n5 two-primary v1','helper_sha256':sha(Path(__file__).read_bytes()),'dependencies':deps,'subtraction_identity_cases':tiny,'fixtures':fixtures,'scope':{'synthetic_selector_assignments':True,'actual_compiler_programs':0,'predecessor_executed':False,'R_or_X_or_Y_or_Pell_materialized':False,'odd_primary_success':False,'complete_zero_claim':False,'universal83_claim':False},'status':'PASS'}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--expect',type=Path);a=p.parse_args();result=build();raw=(json.dumps(result,sort_keys=True,indent=2)+'\n').encode()
 if a.expect:ck(a.expect.read_bytes()==raw,'exact receipt equality')
 else:Path('/tmp/complete83_outer_family_sparse_two_primary.json').write_bytes(raw)
 print(json.dumps({'status':'PASS','fixtures':len(result['fixtures']),'subtraction_cases':result['subtraction_identity_cases'],'deficit_cases':sum(len(f['deficit_cases']) for f in result['fixtures']),'max_K_bits':max(f['K_bits'] for f in result['fixtures'])}))
