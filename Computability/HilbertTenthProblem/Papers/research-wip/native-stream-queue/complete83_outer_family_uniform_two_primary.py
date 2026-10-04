#!/usr/bin/env python3
"""Fresh bounded corroboration. Every predecessor is read only as inert bytes."""
import argparse
import hashlib
import json
from pathlib import Path

BASE=Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers')
PINS={
 '1980/FIXED_RAW_UNIVERSAL_76_PROOF.md':'75a13b5fd0c44c3ec91366306fb5876a3ea2f867e464b84cebd46ca08d060f87',
 '1980/FIXED_RAW_UNIVERSAL_78_PROOF.md':'b28ddb9aec5225cda7dabc85fb952daf49de4041cf35910f62dabf3893749d39',
 'research-wip/native-stream-queue/complete75_half_binomial_compiler.md':'68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117',
 'research-wip/native-stream-queue/complete83_nondyadic_outer_family.md':'42281ee2c1cf99851d4fe67fcfe6f61322fd721d8ebd8ec539983a6edcc44d23',
 'research-wip/native-stream-queue/complete83_outer_family_two_primary.md':'fe9378a51f61d35147ec11dfed0aae8c0d0fc795d7e3afcec5cd22a01df9906b',
 'research-wip/native-stream-queue/complete83_outer_family_two_primary.py':'f595bb59d34f3ce0bb3a469ab7ea93feefe373ac5642ca0be5a78a1eb3b374d6',
 'research-wip/native-stream-queue/complete83_outer_family_two_primary.json':'0ec74608dfd8550c7478a39ff902351304e66ecc2d06f011f5cfdaab5e4d6e35',
 'research-wip/native-stream-queue/complete83_shared_projection_scout.json':'dd9e105d295bf2fb3e3b0246234bb68cb78487ee919405bc052f2b67a9def34c',
}

def ensure(test,message):
 if not test:raise ValueError(message)
def digest(data):return hashlib.sha256(data).hexdigest()
def valuation2(value):
 ensure(value>0,'positive valuation input');return (value & -value).bit_length()-1

def authenticate():
 records=[]
 for name,pin in PINS.items():
  data=(BASE/name).read_bytes();ensure(digest(data)==pin,'dependency '+name)
  records.append({'path':name,'bytes':len(data),'sha256':pin})
 return records

def literal_rows():
 data=json.loads((BASE/'research-wip/native-stream-queue/complete83_shared_projection_scout.json').read_text())
 rows=data['packet']['source'];lookup={row[0]:row for row in rows}
 expected=[['repunit','*','Bm1','Jrep'],['q','+','repunit',1],['Lbig','*','q','q'],
 ['q_minus_F','-','q','F'],['q_minus_FZ','-','q_minus_F','Z'],
 ['gap_product','*','repunit','q_minus_F'],['gap','+','gap_product','q_minus_FZ'],
 ['Lm1','-','Lbig',1],['rproduct','*','gap','Lm1'],['qMF','*','q','MF'],
 ['mask_factor','+','MC','qMF'],['mask','*','mask_factor','Jrep'],['r_lhs','+','rproduct','mask']]
 ensure(len(rows)==len(lookup)==83,'complete source size')
 for row in expected:ensure(lookup[row[0]]==row,'outer binding '+row[0])
 return {'source_rows':len(rows),'checked_rows':expected,'array_executed':False}

def scalar_inequalities():
 ensure((1024*65)**4<2**65,'exact base inequality at65')
 ensure(66**4<2*65**4,'exact monotone ratio at65')
 for d in range(65,513):ensure((1024*d)**4<2**d,'bounded inequality corroboration')
 for M in range(1,65):
  for a in range(1,9):ensure(213*M+4*a+4>5*(27*M+1),'layout margin')
 return {'base_d':65,'base_left':(1024*65)**4,'base_right':2**65,
         'ratio_left':66**4,'ratio_right':2*65**4,'corroborated_d_interval':[65,512],
         'corroborated_geometry_pairs':64*8,'minimum_actual_d_bound':3125}

def mask_layout(M,a,b,dense):
 emax=27*M;H=51*M+3*a+1;g=186*M+4*a+4
 L=1
 while L<=213*M+4*a+4:L*=5
 V=1<<b;d=b*L;B=1<<d
 # Relaxed synthetic native supports: these are not compiled window tables.
 E=set(range(emax+1)) if dense else {0,1,2,M,3*M,9*M,27*M}
 dummy=2
 missing=sum(1<<(b*e) for e in E if e!=1)+(2<<(b*dummy))
 MC=B-1-missing
 ensure(L>5*(emax+1) and d>=3125 and M>3*a,'layout margins')
 ensure(0<missing<1<<(b*(emax+1)),'support size')
 ensure(missing.bit_count()==len(E),'exact missing-mask population')
 ensure(MC.bit_count()==d-len(E) and 5*MC.bit_count()>4*d,'exact complement and density')
 ensure(MC%4==2 and 0<MC<B-1,'mask scalar domain')
 DC=(1<<(3*a*b))+(1<<(g*b));K=DC+(B<<(b*H))
 ensure(0<DC<B and K>B and (K+2)**4<256*B**5,'synthetic coefficient bounds')
 Astar=64*(4*d*K+4*d+1);width=Astar.bit_length()
 ensure(Astar**2<B**3 and 2*width<3*d+2,'sharper size/bitlength')
 return {'M':M,'a':a,'b':b,'L':L,'d':d,'dense_support':dense,'support_count':len(E),
         'Dmask_population':missing.bit_count(),'MC_population':MC.bit_count(),'ell':width},B,K,MC,Astar

def digit_instance(layout,B,K,MC,Astar,n,shape,z):
 d=layout['d'];D=d*n;Q=1<<D;F=K*z;MF=B
 q=Q*(Q+1)//2 if shape=='plus' else Q*(2*Q-1)
 J=(q-1)//(B-1);S=(MC+q*MF)*J
 R=(q*q-z-q*F)*(q*q-1)+S
 ensure((B-1)*J==q-1 and n%4==1 and n>=9,'family shape')
 ensure(0<R<q**4 and R%4==3 and 0<S<2*q*q and Q>Astar,'digit hypotheses')
 V=R*16 if shape=='plus' else R
 if shape=='plus':
  high=Q**4+4*Q**3+(6-2*F)*Q**2+(4-6*F)*Q-6*F-4*z-3
  eps=V//Q**4-high;deficits={4:6*F+4*z+3-eps,5:6*F-3,6:2*F-5}
  ensure(-1<=eps<=9,'plus tail')
 else:
  high=16*Q**4-32*Q**3+(24-8*F)*Q**2+(12*F-8)*Q-6*F-4*z-3
  eps=V//Q**4-high;deficits={4:6*F+4*z+3-eps,6:8*F-24,7:33}
  ensure(-1<=eps<=8,'minus tail')
 for pos,deficit in deficits.items():
  digit=(V>>(D*pos))&(Q-1)
  ensure(0<deficit<Astar and digit==Q-deficit,'complement block')
  ensure(digit.bit_count()>=D-layout['ell'],'complement population')
 low=sum(((R>>(d*j))&(B-1)).bit_count() for j in range(2,n-1))
 ensure(all((R>>(d*j))&(B-1)==MC for j in range(2,n-1)),'actual repeated low cells')
 ensure(low==(n-3)*MC.bit_count(),'weighted low contribution')
 p=((R-1)//2).bit_count();lower=3*D-3*layout['ell']+low-1
 ensure(p>=lower>3*D+1 and p>=3*valuation2(q)+1,'uniform threshold')
 r=(R-1)//2;alpha=2*D+5
 vals=[(r-j).bit_count()+(r+j).bit_count()-(2*r).bit_count()+j*alpha for j in range(4)]
 ensure(vals[0]==p and all(v>p for v in vals[1:]) and p<=8*D+3<4*alpha,'unique full-polynomial minimum')
 return {'layout_M':layout['M'],'dense_support':layout['dense_support'],'shape':shape,'n':n,'z':z,
         'd':d,'D':D,'ell':layout['ell'],'epsilon':eps,'central_population':p,
         'weighted_lower_bound':lower,'target':3*valuation2(q)+1,'R_bits':R.bit_length()}

def make():
 deps=authenticate();bindings=literal_rows();inequalities=scalar_inequalities();layouts=[];cases=[]
 for M in (5,8):
  for dense in (False,True):
   info,B,K,MC,Astar=mask_layout(M,1,5,dense);layouts.append(info)
   for n in (9,13):
    for shape in ('plus','minus'):
     for z in (1,4*info['d']-3):cases.append(digit_instance(info,B,K,MC,Astar,n,shape,z))
 return {'schema':'uniform-outer-family-two-primary-v1','source_sha256':digest(Path(__file__).read_bytes()),
 'dependencies':deps,'source_bindings':bindings,'exact_inequalities':inequalities,'synthetic_layouts':layouts,
 'digit_cases':cases,'scope':{'actual_compiler_outputs':0,'full_source_zeros':0,'Pell_witnesses':0,
 'earlier_program_execution':False,'odd_primary_claim':False,'optimal_threshold_claim':False},'status':'PASS'}

def main():
 p=argparse.ArgumentParser();g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=p.parse_args()
 result=make();raw=(json.dumps(result,indent=2,sort_keys=True)+'\n').encode()
 if a.output:
  with a.output.open('xb') as f:f.write(raw)
 else:ensure(raw==a.expect.read_bytes(),'exact receipt equality')
 print(json.dumps({'status':'PASS','cases':len(result['digit_cases']),'max_R_bits':max(c['R_bits'] for c in result['digit_cases']),'receipt_sha256':digest(raw)}))
if __name__=='__main__':main()
