#!/usr/bin/env python3
"""Native-only index alias and an all-q d=4 necessary-mask obstruction."""
import argparse
import hashlib
import json
import math
from pathlib import Path
PINS={
 'complete83_free_coefficient_scout.py':'a72a406021b96df8111c7f11d36e42241894f0834a660c9ed7c6a75cbfbe1485',
 'complete83_free_coefficient_scout.json':'682d37d4cedcd3c4a086ed3a2e55f272892670edb0424fc0fd8242337f1bf016',
 'complete83_free_coefficient_scout.md':'867e277a2ca09af392e81cf7e54f6eaa7677a939ea3717448cd89053b5690b31',
 'first_index_scaled_obstruction.md':'b67d208d4c18e45145cf91f272d72e2852c09d79be631da8f0a0ce5f377ba1fd',
 'first_index_scaled_obstruction.json':'52b04d7d47065b822d174f6d480fc31d40d908cc014d4fe517600f2b14ac1cea',
 'complete75_half_binomial_compiler.md':'68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117',
}
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def same(a,b):
 if type(a) is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(same(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(same(x,y) for x,y in zip(a,b))
 return a==b

def pell(A,n,mod=None):
 D=A*A-1;r=(1,0);b=(A,1)
 def mul(a,b):
  z=(a[0]*b[0]+D*a[1]*b[1],a[0]*b[1]+a[1]*b[0])
  return tuple(x%mod for x in z) if mod else z
 while n:
  if n&1:r=mul(r,b)
  b=mul(b,b);n//=2
 return r

def modular_case(t):
 p=t*(t+2);n=t*(t+1);R=2*n-1
 A=(pow(2,p+t+1,p)+pow(2,t+1,p)+2)%p
 cm=pell(A,p,p)[1];g=math.gcd(cm,p)
 need(math.gcd(p,R-p)==math.gcd(t+2,3),'compatibility simplification')
 return dict(t=t,p=p,n=n,R=R,c_mod_p=cm,gcd_c_p=g,auxiliary_CRT_compatible=(R-p)%g==0,
             q16_positive_packing_interval=31*255<R<16**4-16**3)

def exact_first_main(t):
 p=t*(t+2);n=t*(t+1);R=2*n-1;X=1<<p;Y=1<<(t+1)
 E=X*Y;a=Y*(X+1);A=a+2;Delta=A*A-1;H=4*a+3;P=2*X*Y*Y+1
 D,c=pell(A,p);tau,kn=pell(P,n);k=2*kn
 eta=c-k*Y;zeta=k-eta
 need(eta>0 and zeta>0,'strict ratio')
 need(D*D-Delta*c*c==1 and tau*tau-X*Y*Y*(X*Y*Y+1)*k*k==1,'both norms')
 need((D-a*c-X)%H==0,'main projection');gamma=(D-a*c-X)//H
 need(gamma>1 and X%16==0 and Y%16**3==0,'positive projection/scales')
 need((k-R-1)%E==0,'index divisibility');h=(k-R-1)//E;need(h>0,'positive h')
 need(p!=R and p%4==3 and c>A*Delta*Delta and c>2*p,'mismatch and rank margins')
 g=math.gcd(c,4*p);need((p-R)%g==0,'CRT compatibility')
 m=4*p//g;j=((p-R)//g)*pow(c//g,-1,m)%m;v=R+c*j
 need(v>0 and v%c==R%c and v%(4*p)==p and v%4==3,'auxiliary CRT')
 f=D;S=Delta*c
 need(Delta*f*f-S*S==Delta,'scaled strong')
 need(pell(A,2*p,f)==(f-1,0) and pell(A,4*p,f)==(1,0),'auxiliary period')
 need(S%c==0 and f*f%c==1 and math.gcd(c,f)==1,'c congruence hypotheses')
 values=dict(X=X,Y=Y,w=X//16,s=Y//16**3,E=E,a=a,A=A,Delta=Delta,H=H,P=P,
             D=D,c=c,tau_root=tau,k=k,eta=eta,zeta=zeta,rho=1,sigma=gamma-1,h=h,
             f=f,S=S,abstract_R=R,auxiliary_index=v)
 return dict(t=t,p=p,n=n,R=R,fields_hex={n:hex(x) for n,x in values.items()},
             bit_lengths={n:x.bit_length() for n,x in values.items()},
             first_main_strict_ratio_main_projection_and_index=True,
             auxiliary_extension='Proved from two congruences; V,y,T not materialized',full_compiler_zero=False)

def mask_proof():
 masks=[(MC,MF0) for MC in range(1,15) for MF0 in range(1,15)
        if MC%4==2 and MF0%8==4 and MC.bit_count()+MF0.bit_count()==4]
 need(masks==[(6,12),(10,12),(14,4)],'entire d4 mask list')
 squares={x*x%17 for x in range(17)};rows=[]
 for parity in (0,1):
  q=1 if parity==0 else 16;J=0 if parity==0 else 1
  need((15*J-(q-1))%17==0 and (q*q-1)%17==0,'all-k parity interface')
  for MC,MF0 in masks:
   R=(MC+q*(MF0+15))*J%17;rhs=(2*R+3)%17
   need(rhs not in squares,'mask nonsquare')
   rows.append(dict(k_parity=parity,q_mod17=q,J_mod17=J,MC=MC,MF0=MF0,
                    packed_R_mod17=R,impossible_square_residue=rhs))
 need([pow(2,j,15) for j in range(1,5)]==[2,4,8,1],'q power exponent multiple4')
 return dict(masks=[list(x) for x in masks],square_residues_mod17=sorted(squares),
             all_k_parity_cases=rows,scope='All k>=1, q=16^k, B=16, J=(q-1)/15; these necessary masks do not assert a valid compiler recipe.')

def verify(root,scout_root):
 for name,pin in PINS.items():
  base=scout_root if name.startswith('complete83_free_coefficient_scout.') else root
  need(sha((base/name).read_bytes())==pin,'pin '+name)
 # Saved-source shape is read as data, never executed.
 d=json.loads((scout_root/'complete83_free_coefficient_scout.json').read_text())
 rows={r[0]:r for r in d['packet']['source']}
 for row in [['norm_index','-','index_difference','r_lhs'],['index_difference','-','R10b','hpm1'],
             ['hpm1','*','h','UM'],['auxiliary_R_f2','*','r_lhs','L16'],
             ['norm_strong','-','scaled_f_square','R16'],['norm_aux','+','L17','aux_y2']]:
  need(rows.get(row[0])==row,'actual source interface')
 cases=[modular_case(t) for t in [11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,65,71,83,101]]
 return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),dependency_pins=PINS,
             modular_cases=cases,exact_case=exact_first_main(11),mask_obstruction=mask_proof(),
             scope='Scaled first/main/index and free-S strong/auxiliary subsystem only; no input/transport equation, packed compiler zero, or accepted-language conclusion.',
             theorem='Conditional on gcd(psi_A(p),p)|(R-p), native first-index restoration can be positive integral while main p differs from R. This family cannot satisfy the d4 necessary masks for any compatible q=16^k.')

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--scout-root',type=Path)
 ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args()
 need(not(a.output and a.expect),'output/expect conflict');r=verify(a.root,a.scout_root or a.root)
 need(same(r,json.loads(json.dumps(r))),'typed roundtrip')
 if a.expect:need(same(r,json.loads(a.expect.read_text())),'exact receipt')
 if a.output:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 print(json.dumps(dict(status='PASS',modular_cases=len(r['modular_cases']),exact_first_main_cases=1,mask_parity_cases=6,full_compiler_zero=False)))
if __name__=='__main__':main()
