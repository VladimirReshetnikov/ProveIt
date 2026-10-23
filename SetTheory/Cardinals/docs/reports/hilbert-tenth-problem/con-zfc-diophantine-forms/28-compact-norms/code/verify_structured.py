#!/usr/bin/env python3
"""Reproduce and audit the nine-variable signed-divisor specialization.

Standard library only. Fixed Jones index integers are evaluated modulo primes
from exact bounded recipes, without materializing them. No solvability claim is
inferred from these finite computations.
"""
from __future__ import annotations
import argparse
from collections import Counter
from hashlib import sha256
from itertools import combinations_with_replacement, product
import gzip
import json
from math import isqrt
from pathlib import Path
from random import Random
import nine_structured as nc

EXPECTED_HASHES = {
 'beta': '40cc309fcb5dd2942c371d18be6d955d472e6b4c3604034b316194037ac16a5d',
 'K': 'e79f794af9565a7d824beb423bd03ee9ac117811b9b0e3a83ffe18f8a084de99',
 'MC': '2e3107193f3b376fc3cfffdaa3ef547e6dd8dfdd4548519c0e33b5ffe2f2371d',
 'MF_source': '8851b54fffd93780996de5f8c69315448e1369c3eea142428d2225a5149d1825',
}

def require(value, message):
 if not value: raise RuntimeError(message)

def polynomial(records, values, modulus):
 total=0
 for row in records:
  v=row['coefficient']%modulus
  for x,e in zip(values,row['powers']):v=v*pow(x,e,modulus)%modulus
  total=(total+v)%modulus
 return total

def geometric(base,n,mod):
 if not n:return 1%mod,0
 p,s=geometric(base,n//2,mod)
 outp=p*p%mod; outs=s*(1+p)%mod
 if n%2:return outp*base%mod,(outs+outp)%mod
 return outp,outs

def all_exponents(nu):
 L=5**(nu+1);powers=[5**j for j in range(nu+1)]
 for degree in range(5):
  for indices in combinations_with_replacement(range(nu+1),degree):
   a=[0]*(nu+1)
   for j in indices:a[j]+=1
   yield tuple(a),L-sum(powers[j] for j in indices)

def direct_digit(B,z,coefficients,exponents,mod):
 return sum((z+coefficients.get(a,0))*pow(B,e,mod) for a,e in exponents)%mod

def independent_formula(nu,coefficients,z,y,unknowns,exponents,mod):
 p=mod
 eps,g0,h0,s0,w0,phi,i0,j0,n=unknowns
 g,h,s,w,i,j=g0+1,h0+1,s0+1,w0+1,i0+1,j0+1
 b=(y+1+eps)%p; BB=pow(b,5,p);LL=5**(nu+1)
 q=pow(BB,LL,p);ell=sum(pow(BB,5**r,p) for r in range(1,nu+1))%p
 lam=geometric(BB,4*LL,p)[1];e=direct_digit(BB,z,coefficients,exponents,p)
 NN=pow(q,16,p);cap=32*b*pow(BB,5**nu,p)%p
 RR=((g+e*q**3+ell*q**5+(2*(e-z*lam)*(1+BB+g)**4+lam*BB+lam*BB*q**4)*q**7)*(NN*NN-NN)
     +(q**3-b*ell+ell+(BB-2*z)*lam*q**3+(BB-2)*q**8)*(NN*NN-1))%p
 UU=NN*NN*w%p;YY=NN*NN*s%p;MM=RR*YY%p;PP=2*MM*MM*UU%p
 KK=(RR+1+h*(PP-1))%p;AA=MM*(UU+1)%p;WW=b*w%p
 CC=(2*RR+1+WW+phi)%p;JJ=(4*AA-5)%p
 QQ=(3*WW*CC-2*(WW*WW-1))%p;DD=((AA*AA-1)*CC*CC+1)%p
 EE=i*JJ*DD*CC*CC%p;FF=((AA*AA-1)*EE*EE+1)%p
 GG=(AA+FF*(CC*DD+1-AA))%p;HH=(2*RR+1+j*CC)%p
 II=((GG*GG-1)*HH*HH+1)%p
 a0=((PP*PP-1)*KK*KK+1)%p;a1=DD*FF*II%p
 m=(KK*KK*cap-4*(CC-KK*YY)**2*cap-8*g*KK*KK)%p
 div=JJ*FF%p;num=(QQ*FF+JJ*(HH-CC))%p;bound=(QQ*QQ+(HH-CC)**2+1)%p
 r=(WW+phi)%p;scale=YY*(UU+1)%p
 md=scale*(RR*RR+CC*CC)%p;mf=(AA*EE+1)%p
 ch=((j+2)*CC*CC+r*r)%p
 # Deliberately use the expanded sum of nonnegative terms, not emitter factoring.
 mi=(FF*DD*ch+2*FF*HH*HH+(FF-1)*AA*AA+1)%p
 v0=(PP*KK+1)%p;v1=(md*mf*mi+1)%p
 omega=div*(2*m-1)%p
 theta=(div*(n+bound)+num-omega*(2*bound+v0*v1))%p
 out=((theta*theta-omega*omega*(a0+v0*v0*a1))**2-4*omega**4*v0*v0*a0*a1)%p
 return out,{'R':RR,'P':PP,'K':KK,'A':AA,'C':CC,'D':DD,'E':EE,'F':FF,'Gp':GG,
             'H':HH,'I':II,'a0':a0,'a1':a1,'divisor':div,'dividend':num,
             'division_bound':bound,'margin':m,'majorant_D':md,'majorant_F':mf,
             'majorant_CH':ch,'majorant_I':mi,'V0':v0,'V1':v1,'W':omega,'T':theta,'output':out}

def head_add(p,q,k=1):
 out=dict(p)
 for mon,v in q.items():
  out[mon]=out.get(mon,0)+k*v
  if not out[mon]:del out[mon]
 return out

def head_mul(p,q):
 out={}
 for a,v in p.items():
  for b,w in q.items():
   mon=dict(a)
   for name,e in b:mon[name]=mon.get(name,0)+e
   key=tuple(sorted(mon.items()));out[key]=out.get(key,0)+v*w
 return {k:v for k,v in out.items() if v}

def exact_heads(body):
 heads=[];upper=[]
 for k,node in enumerate(body['nodes']):
  kind=node['kind']
  if kind=='literal':
   v=node['value'];out=(0,{():v}) if v else(-1,{})
  elif kind=='fixed':out=(0,{((node['name'],1),):1})
  elif kind=='variable':out=(1,{():1})
  else:
   require(node['left']<k and node['right']<k,'DAG is not topologically sorted')
   a,b=heads[node['left']],heads[node['right']]
   if kind=='mul':out=(a[0]+b[0],head_mul(a[1],b[1])) if a[1] and b[1] else(-1,{})
   else:
    factor=-1 if kind=='sub' else 1
    if a[0]>b[0]:out=a
    elif b[0]>a[0]:out=(b[0],{m:factor*c for m,c in b[1].items()})
    else:
     coeff=head_add(a[1],b[1],factor)
     require(bool(coeff) or a[0]<=0 or (kind=='sub' and node['left']==node['right']),
             'Unresolved positive-degree leading cancellation')
     out=(a[0],coeff) if coeff else(-1,{})
  heads.append(out)
 output=heads[body['output']]
 require(output==(93264*5**33+288,{():441*2**192}),'Incorrect exact leading certificate')
 named={name:{'degree':heads[idx][0],'diagonal_leading_coefficient':heads[idx][1].get(())}
        for name,idx in body['named_nodes'].items()}
 return named

def majorant_checks():
 count=0;edge=Counter()
 for R,U,Y,h,i,j,r in product([-4,-3,-2,-1,1,2,3,4],range(1,4),range(1,4),range(1,3),range(1,3),range(1,4),range(1,9)):
  scale=Y*(U+1);A=R*scale;C=2*R+r+1;J=4*A-5
  D=(A*A-1)*C*C+1;E=i*J*D*C*C;F=(A*A-1)*E*E+1
  G=A+F*(C*D+1-A);H=(j+1)*C-r;I=(G*G-1)*H*H+1
  P=2*R*R*Y*Y*U;K=R+1+h*(P-1);a0=(P*P-1)*K*K+1
  md=scale*(R*R+C*C);mf=A*E+1;ch=(j+2)*C*C+r*r
  mi=F*D*ch+2*F*H*H+(F-1)*A*A+1
  require(D>=1 and F>=1 and K>=1 and P>=2,'Positive intermediate fails')
  require(md>=1 and mf>=1 and mi>=1,'Nonpositive majorant')
  require(md*md>=D and mf*mf>=F and mi*mi>=abs(I),'Radicand majorant fails')
  require((P*K)**2>=a0 and (md*mf*mi)**2>=abs(D*F*I),'Combined majorant fails')
  if C==0:edge['C=0']+=1
  if H==0:edge['H=0']+=1
  if R<0:edge['R<0']+=1
  count+=1
 return {'assignments':count,'degenerate_cases':dict(edge)}

def finalizer_checks():
 def norm(a,b,v0,v1,u,v,M,m,n):
  o=u*(2*m-1);t=u*(n+M)+v-o*(2*M+v0*v1)
  return (t*t-o*o*(a+v0*v0*b))**2-4*o**4*v0*v0*a*b
 def square(n):return n>=0 and isqrt(n)**2==n
 found=0;tested=0;witnesses=0
 for a,b,u,v,m in product(range(-2,8),range(-2,8),[-3,-2,-1,1,2,3],range(-3,4),range(-1,3)):
  v0=a*a+2;v1=b*b+2;M=abs(v)+1
  valid=square(a) and square(b) and v%u==0 and m>0
  for n in range(8):
   zero=norm(a,b,v0,v1,u,v,M,m,n)==0
   require(not zero or valid,'Spurious finalizer zero')
   found+=zero;tested+=1
  if valid:
   Z=2*M+v0*v1+isqrt(a)+v0*isqrt(b)
   n=(2*m-1)*Z-M-v//u
   require(n>=2 and norm(a,b,v0,v1,u,v,M,m,n)==0,'Completeness witness fails')
   witnesses+=1
 return {'evaluations':tested,'bounded_zeros':found,'constructed_witnesses':witnesses}

def run(parent,generated,coefficients):
 constants=json.loads((generated/'constants.json').read_text());sdata=json.loads((generated/'index_bound_s.json').read_text())
 body=json.loads((generated/'nine_structured_dag.json').read_text())
 require(sha256(parent.read_bytes()).hexdigest()==constants['parent_sha256'],'Parent hash differs')
 _,_,_,_,weighted=nc.build_parent(json.loads(parent.read_text()))
 records={tuple(c['alpha']):c for c in constants['coefficient_records']}
 require(set(weighted)==set(records),'Weighted coefficient supports differ')
 for alpha,poly in weighted.items():
  got={tuple(t['powers']):t['coefficient'] for t in records[alpha]['coefficient_polynomial_in_fixed_ports']}
  require(poly==got,'Weighted quartic coefficient differs')
 keys=[(tuple(c['alpha']),c['name']) for c in constants['coefficient_records']]
 require(body==nc.make_body(32,keys,'structured'),'Delivered DAG differs from regeneration')
 live=set();pending=[body['output']]
 while pending:
  idx=pending.pop()
  if idx in live:continue
  live.add(idx);node=body['nodes'][idx]
  if node['kind'] in ('add','sub','mul'):pending.extend([node['left'],node['right']])
 require(live==set(range(len(body['nodes']))),'Dead node in delivered DAG')
 require(sum(x['kind']=='variable' for x in body['nodes'])==9,'Incorrect unknown-leaf count')
 require(sum(x['kind']=='fixed' for x in body['nodes'])==348,'Incorrect fixed-leaf count')
 counts={k:sum(n['kind']==k for n in body['nodes']) for k in ['add','sub','mul']}
 require(counts=={'add':668,'sub':23,'mul':19856},'Operation ledger differs')
 degree=exact_heads(body)
 ports={}
 for name,expected in EXPECTED_HASHES.items():
  path=coefficients/(name+'.bin')
  data=path.read_bytes() if path.exists() else gzip.decompress((coefficients/(name+'.bin.gz')).read_bytes())
  require(sha256(data).hexdigest()==expected,'Wrong Wang943 coefficient: '+name)
  ports[{'K':'K0','MF_source':'MF'}.get(name,name)]=int.from_bytes(data,'little')
 exponents=list(all_exponents(32));require(len(exponents)==66045,'Wrong bounded sum length')
 tuples=[[0]*9,[1]*9,list(range(9)),[3,2,0,1,4,0,2,1,7]]
 receipts=[];comparisons=0
 for p in [101,1009,1000003]:
  require(all(p%d for d in range(2,isqrt(p)+1)),'Not prime')
  ordered=[ports[name] for name in constants['fixed_port_order']]
  sres=polynomial(sdata['terms'],[v%(p-1) for v in ordered],p-1)
  z=pow(2,sres,p)
  coeffs={a:polynomial(c['coefficient_polynomial_in_fixed_ports'],[v%p for v in ordered],p) for a,c in records.items()}
  y=direct_digit(2*z%p,z,coeffs,exponents,p)
  leaves={'z_index':z,'y_index':y};leaves.update({records[a]['name']:v for a,v in coeffs.items()})
  samples=[]
  for xs in tuples:
   got,named=nc.evaluate_dag(body,leaves,dict(zip(body['variables'],xs)),p)
   want,independent=independent_formula(32,coeffs,z,y,xs,exponents,p)
   require(got==want,'Actual-coefficient DAG/formula output differs')
   for name,v in independent.items():
    require(named[name]==v,'Named intermediate differs: '+name);comparisons+=1
   samples.append({'unknowns':xs,'output':got})
  receipts.append({'prime':p,'ports_mod_prime':{k:v%p for k,v in ports.items()},'s_residue':sres,'z_residue':z,'y_residue':y,'samples':samples})
 return {'status':'PASS','domain':'nine nonnegative integers','degree':93264*5**33+288,
         'degree_formula':'93264*5^33+288','all_nodes_live':True,'node_count':len(body['nodes']),'diagonal_leading_coefficient':441*2**192,
         'operations':counts,'total_operations':sum(counts.values()),'coefficient_records':len(records),
         'finite_sum_terms':len(exponents),'dag_direct_output_comparisons':len(receipts)*len(tuples),
         'named_intermediate_comparisons':comparisons,'majorant_checks':majorant_checks(),
         'signed_finalizer_checks':finalizer_checks(),'actual_coefficient_modular_checks':receipts,
         'degree_ledger':degree,'parent_sha256':constants['parent_sha256'],
         'dag_sha256':sha256((generated/'nine_structured_dag.json').read_bytes()).hexdigest(),
         'scope':'Exact source/DAG regeneration and leading-degree certificate plus finite algebraic audits. Universal semantic claims rely on the stated ordinary mathematical proofs and inherited Jones/compiler/K215 theorems; no solvability conclusion or kernel checking is asserted.'}

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('parent',type=Path);ap.add_argument('generated',type=Path);ap.add_argument('coefficients',type=Path)
 args=ap.parse_args();result=run(args.parent.resolve(),args.generated.resolve(),args.coefficients.resolve())
 (args.generated/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items() if k not in ('degree_ledger','actual_coefficient_modular_checks')},indent=2))
