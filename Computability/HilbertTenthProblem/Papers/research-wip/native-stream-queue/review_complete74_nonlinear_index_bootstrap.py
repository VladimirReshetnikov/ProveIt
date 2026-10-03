#!/usr/bin/env python3
"""Bounded exact corroboration of the signed first-index bootstrap note.
No author/historical Python, compiler suites, or full positive child claim.
"""
import argparse,hashlib,json
from pathlib import Path
if not __debug__:raise RuntimeError('run without -O')
PINS={
  "complete74_nonlinear_index_projection_scout.py": "610739f1074ad792e8010287e8e162d509832c8d5e7444dc38ecae98e7710c71",
  "complete74_nonlinear_index_projection_scout.json": "ea982f9585eb4e16d756dfc33c73041e73e5e18a38ea37c2302d57c1fe104c92",
  "complete74_nonlinear_index_projection_scout.md": "2034e1343f9c4c059525445c6ef1ae287dec48c0da9d9d27123f1e5745c2c40d",
  "complete74_factored_first_norm.json": "7ebfa54d3846d1c3a6ff7b8e5cd143f3ac80f8299b51698a9f45681d3524eb28",
  "complete75_signed_projection_elimination101.md": "55b701410d05b515b6cbc4619a3f39fc290f469d21d03dfee9e291aa674fa31d",
  "complete75_half_binomial_compiler.md": "68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117",
  "../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md": "e381124c969087ffa867448177a9df693d81e7bd85dd3a8489d443220fba053d",
  "../../1980/FIXED_RAW_UNIVERSAL_76_PROOF.md": "75a13b5fd0c44c3ec91366306fb5876a3ea2f867e464b84cebd46ca08d060f87",
  "../../1980/FIXED_RAW_UNIVERSAL_78_PROOF.md": "b28ddb9aec5225cda7dabc85fb952daf49de4041cf35910f62dabf3893749d39",
  "../../1980/PELL_RELAXED_AUXILIARY_PROOF.md": "9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90",
  "../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md": "47a2c5b69f3c87b7a1ddc61ef84757023de291b63d1330e2c8dc9b40e811ab8b",
  "../../1980/HALF_PARAMETER_PELL_92_PROOF.md": "c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b"
}
def need(v,s):
 if not v:raise ValueError(s)
def digest(b):return hashlib.sha256(b).hexdigest()
def stable(v):return json.dumps(v,sort_keys=True,separators=(',',':'))
def pell(A,n,mod=None):
 D=A*A-1;u,v=1,0;x,y=A,1
 def prod(a,b,c,d):
  z=(a*c+D*b*d,a*d+b*c)
  return tuple(t%mod for t in z)if mod else z
 while n:
  if n&1:u,v=prod(u,v,x,y)
  x,y=prod(x,y,x,y);n//=2
 return u,v

def qpoly(T,h,mod):
 if h==0:return 1%mod
 # Q_(n+2)=(4T-2)Q_(n+1)-Q_n. Binary matrix evaluation.
 a,b,c,d=4*T-2,-1,1,0;u,v,w,z=1,0,0,1;n=h-1
 while n:
  if n&1:u,v,w,z=((u*a+v*c)%mod,(u*b+v*d)%mod,(w*a+z*c)%mod,(w*b+z*d)%mod)
  a,b,c,d=((a*a+b*c)%mod,(a*b+b*d)%mod,(c*a+d*c)%mod,(c*b+d*d)%mod);n//=2
 return (u*(4*T-3)+v)%mod

def source_map(packet):
 d={n:(op,a,b)for n,op,a,b in packet['source']};raw=packet['mode']=='raw30';a='a'if raw else'R12';c='c'if raw else'R10a';k='k'if raw else'R10b';D='d'if raw else'R14'
 requirements={'Lbig':('*','q','q'),'n2':('*','Lbig','q'),'wn2':('*','w','n2'),'sn2':('*','s','n2'),'UM':('*','wn2','sn2'),'R12':('+','UM','sn2'),'R10b':('+','eta','zeta'),'ksn2':('*',k,'sn2'),'first_root_base':('*','UM','ksn2'),'first_next':('+','first_root_base',k),'L9':('*','first_root_base','first_next'),'tau_square':('*','tau','tau'),'R9':('-','tau_square',1),'R10a':('+','ksn2','eta'),'index_partial':('-',k,'hpm1'),'hpm1':('*','h','UM'),'restored_r':('-','index_partial',1),'kinner':('+','Kconstant','wn2'),'qF':('*','q','F'),'packed':('+','Z','qF'),'gap':('-','Lbig','packed'),'Lm1':('-','Lbig',1),'rproduct':('*','gap','Lm1'),'qMF':('*','q','MF'),'mask_factor':('+','MC','qMF'),'mask':('*','mask_factor','Jrep'),'r_lhs':('+','rproduct','mask'),'a4':('*',4,a),'a4m5':('+','a4',3),'a_square':('*',a,a),'A':('+','a_square','a4m5'),'cam2':('*',c,a),'D1':('+','wn2','cam2'),'R14':('+','D1','gam'),'L15':('*',D,D),'c2':('*',c,c),'Ac2':('*','A','c2'),'R15':('+','Ac2',1),'ic2':('*','i','c2'),'ic22':('*','ic2','ic2'),'L16':('*','f','f'),'f_square_minus_one':('-','L16',1),'R16':('*','A','f_square_minus_one'),'jc':('*','j',c),'H17':('-','jc','restored_r'),'of':('*','o','f'),'aux_u_rhs':('-','of',c),'H2':('*','H17','H17'),'aux_y2':('*','y_aux','y_aux'),'aux_square_gap':('-','H2','aux_y2'),'L17':('*','ic22','aux_square_gap'),'P17':('-',1,'aux_y2')}
 need(all(d[n]==v for n,v in requirements.items()),'actual source premise producer')
 for pair in [['restored_r','r_lhs'],['L9','R9'],['L15','R15'],['ic22','R16'],['L17','P17'],['H17','aux_u_rhs']]:need(pair in packet['comparisons'],'retained native comparison')
 if raw:
  for pair in [['a','R12'],['c','R10a'],['k','R10b'],['d','R14'],['C','marked_rhs'],['raw_bound','q']]:need(pair in packet['comparisons'],'raw equality premise')
  need(d['gam']==('*','ga','a4m5')and d['marked_rhs']==('+','Z','W'),'raw positive graph premise')
 elif packet['mode']=='positive22':need(d['marked_rhs']==('+','Z','W')and['raw_bound','q']in packet['comparisons'],'positive marker bound')
 else:need(d['gamma_sum']==('+','rho','sigma')and d['gam']==('*','gamma_sum','a4m5')and d['W']==('-','marked_rhs','Z'),'signed source premise and boundary')
 return dict(mode=packet['mode'],checked_producers=len(requirements),supplied_witnesses=len(packet['witnesses']),same_source_sha256=digest(stable(packet['source']).encode()))

def run(root):
 for name,pin in PINS.items():need(digest((root/name).read_bytes())==pin,'source/proof pin '+name)
 author=json.loads((root/'complete74_nonlinear_index_projection_scout.json').read_text());sources=[source_map(f['packet'])for f in author['forms']]
 counts={'actual_source_interfaces':len(sources),'main_projection_prefixes':0,'outer_bound_cases':0,'odd_q_even_packing_cases':0,'double_index_identities':0,'negative_representative_cases':0,'auxiliary_modular_constructions':0,'materialized_auxiliary_only_zeros':0}
 # Main exponent congruence for the formerly excluded small indices.
 for q in (16,17,31,32,46,64):
  for w in (1,2):
   for s in(1,3):
    X=w*q**3;Y=s*q**3;a=Y*(X+1);A=a+2;H=4*a+3
    need(a>2**24 and X>=4096 and X<a,'uniform pretyping margins')
    for p in range(1,12):
     d,c=pell(A,p);need((d-a*c-pow(2,p,H))%H==0,'literal main exponent recurrence');need(pow(2,p)<a and pow(2,p)<X,'small index exclusion');counts['main_projection_prefixes']+=1
    need(pell(A,12)[1]>2*q**4*(X+q*q),'rank lower bound dominates raw signed packing range')
 # The actual shifted source, including negative representatives and odd q.
 for B in(16,32,64):
  for J in range(1,5):
   q=(B-1)*J+1
   for w in(1,2):
    X=w*q**3;Y=q**3;E=X*Y;A=Y*(X+1)+2
    for K in(1,B*B-1):
     for C in(3,q-2):
      for Z in(1,C-1):
       total=(K+X)*C
       for z in(1,(total-1)//(q-1)):
        F=total-z*(q-1);need(F>0 and F<total,'positive transport solution')
        MC=2;MF0=4;TC=MC*J+1;TF=MF0*J-1;Tp=TC+q*TF;Sp=Z+q*F-1
        R=(q*q-Z-q*F)*(q*q-1)+(MC+q*(MF0+B-1))*J
        need(R==(q*q-Sp)*(q*q-1)+Tp and 0<Tp<q*q-1 and R!=0,'actual packing and nonzero remainder')
        need(R<q**4 and abs(R)<q**4*(K+X)<(q+1)*E,'signed raw bound')
        need(2*abs(R)<pell(A,12)[1],'uniform c/2 margin at p12')
        if q%2:need(R%2==0,'odd-q literal packing parity');counts['odd_q_even_packing_cases']+=1
        counts['outer_bound_cases']+=1
 # Exact doubled-index identity used to establish n<p<2n.
 for A in range(3,12):
  for n in range(1,13):
   need(pell(A,2*n)[1]==2*A*pell(2*A*A-1,n)[1],'doubled psi identity');counts['double_index_identities']+=1
 # Exhaustive finite check of the integer representative implication only.
 for E in range(2,66):
  for p in range(3,100,2):
   for n in range((p+1)//2,p):
    total=2*n+p-1
    if total%E==0:
     v=total//E;need(2*p<=v*E<=3*p-3 and v*E<3*p,'negative-index window');counts['negative_representative_cases']+=1
 # Exact modular realizations of both p-mod4 branches; these are auxiliary only.
 construction=[]
 for A,p in((2,3),(2,5),(2,7),(3,3),(3,5)):
  _,c=pell(A,p);m=c*p*(1 if p%4==3 else 2);f,psi=pell(A,m);Delta=A*A-1;T=Delta*psi
  need(T%(c*c)==0 and T*T==Delta*(f*f-1),'ordinary strong construction')
  ell=p+2*m;h=(ell-1)//2;need(h%2==0 and m% c==0 and m%p==0,'mixed sign index')
  need(qpoly(T*T,h,c)==p%c and qpoly(T*T,h,f)==(-c)%f,'both original auxiliary congruences')
  construction.append(dict(A=A,p=p,c=c,m=m,ell=ell,coefficient_bits=T.bit_length(),f_bits=f.bit_length(),r=-p))
  counts['auxiliary_modular_constructions']+=1
 # A full finite negative-r solution of every ordinary strong/auxiliary row.
 A=3;p=3;_,c=pell(A,p);m=c*p;f,v=pell(A,m);T=(A*A-1)*v;ell=p+2*m;TU,y=pell(T,ell)
 need(TU%T==0,'odd normalized root divisibility');U=TU//T;i=T//(c*c);j=(U-p)//c;o=(U+c)//f;r=-p
 need((U-p)%c==0 and(U+c)%f==0 and min(i,j,o,y)>0,'positive mixed-sign witnesses')
 need(i*c*c==T and T*T==(A*A-1)*(f*f-1)and T*T*(U*U-y*y)==1-y*y and U==j*c-r==o*f-c,'entire auxiliary subsystem zero')
 counts['materialized_auxiliary_only_zeros']=1
 values={'A':A,'p':p,'c':c,'m':m,'ell':ell,'r':r,'f':f,'i':i,'j':j,'o':o,'y':y,'U':U}
 witness_digest=digest(stable({k:hex(v)for k,v in values.items()}).encode())
 fixture={k:values[k]for k in('A','p','c','m','ell','r')};fixture.update(U_bits=U.bit_length(),all_positive_supplied=True,full_auxiliary_zero=True,whole_child_zero_claim=False,witness_hex_sha256=witness_digest)
 return dict(status='PASS',source_sha256=digest(Path(__file__).read_bytes()),pins=PINS,counts=counts,source_interfaces=sources,auxiliary_constructions=construction,materialized_auxiliary_fixture=fixture,scope='New symbolic bootstrap is proved in companion note. These finite checks corroborate actual source premises and exact component identities. Full positive inverse and full negative child/compiler zeros remain unresolved; no universal bound changes.')
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=run(a.root)
 if a.expect:need(stable(r)==stable(json.loads(a.expect.read_text())),'exact saved receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps({'status':r['status'],'counts':r['counts'],'fixture':r['materialized_auxiliary_fixture']}))
if __name__=='__main__':main()
