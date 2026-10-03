#!/usr/bin/env python3
"""Source-aware mathematical audit of asymmetric X scaling in three actual74 forms.
No author or historical Python imports; not an API or new degree-census audit.
"""
import argparse,hashlib,json,random
from pathlib import Path
from fractions import Fraction
from collections import Counter
if not __debug__:raise RuntimeError('run without -O')
PINS={'complete74_factored_first_norm.py':'7c4b10fa78a3fa6517083c41fc6228dd403fec5ac87f2ca6b80b45dd60e8b908','complete74_factored_first_norm.json':'7ebfa54d3846d1c3a6ff7b8e5cd143f3ac80f8299b51698a9f45681d3524eb28','complete74_factored_first_norm.md':'119b51ca9a5d50e0eb998b334af87c1ea3eb0913f956b4f9d7a985f5d1159d9f','complete113_asymmetric_retained109.py':'5017530a67107651cbde1cbfd81e4a2cf0aad294bb81997789e8e749a1ea2368','complete113_asymmetric_retained109.json':'8a037d2830ef3cbbfe7f0b02b71b5337ffac8a3e34cf8391c09257d0babb9f24','complete113_asymmetric_retained109.md':'cee18b24b50fcea5f3cd6fa9fb20f8dbdd5ae9f5e99107e24ffff4e66b3305f0','review_asymmetric_retained109_math.md':'0f9ff2fc994d54af9221e604cd9ec32890539e53a5fae3d951ad064fd64c04c5','complete75_signed_projection_elimination101.py':'5a781fdacabab7feda2a8879c1cc207936045a1e4aa063c064a0bfffcdc9b4c8','complete75_signed_projection_elimination101.json':'00de69d028b79d3837bbd892a202d78d95092711d68ca6f40bf7d5e2ab20c3e3','complete75_signed_projection_elimination101.md':'55b701410d05b515b6cbc4619a3f39fc290f469d21d03dfee9e291aa674fa31d','complete75_positive_elimination.md':'59cc280280bb8ab74318f648da56aabf31317f42a8a08d01851c5f8db0232d6b','pell_kernel_half_binomial42.md':'0df596859d84aa1cf1d4636457937274e8fdac0c1f8da3196962d911be232992','../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md':'e381124c969087ffa867448177a9df693d81e7bd85dd3a8489d443220fba053d','../../1980/PELL_RELAXED_AUXILIARY_PROOF.md':'9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90','../../1980/HALF_PARAMETER_PELL_92_PROOF.md':'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b'}
def need(v,m):
 if not v:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def same(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(same(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(same(x,y)for x,y in zip(a,b))
 return a==b

def calc(rows,v):
 e=dict(v)
 for n,o,a,b in rows:
  a=e[a]if type(a)is str else a;b=e[b]if type(b)is str else b;e[n]=a*b if o=='*'else a+b if o=='+'else a-b
 return e

def add(a,b,sign=1):
 p=dict(a)
 for k,c in b.items():p[k]=p.get(k,0)+sign*c
 return {k:c for k,c in p.items()if c}
def mul(a,b):
 r={}
 for m,c in a.items():
  for n,d in b.items():
   k=tuple(x+y for x,y in zip(m,n));r[k]=r.get(k,0)+c*d
 return {k:c for k,c in r.items()if c}
def ring(n):return lambda c:{(0,)*n:c}if c else{},lambda i:{tuple(int(i==j)for j in range(n)):1}

def identities():
 C,V=ring(3);L,k,g=map(V,range(3));tau=add(L,g)
 first=add(add(mul(tau,tau),mul(L,add(L,k)),-1),C(1),-1)
 gap=add(add(mul(g,g),mul(L,add(mul(C(2),g),k,-1))),C(1),-1)
 need(first==gap,'exact ordinary root to positive gap identity')
 C,V=ring(2);q,w=map(V,range(2));q2=mul(q,q)
 need(mul(mul(q2,w),q)==mul(w,mul(q2,q)),'full-coordinate X identity')
 C,V=ring(7);q,Z,F,MC,MF,J,one=map(V,range(7));one=C(1)
 # Here MF means the unshifted mask and q=(B-1)J+1 has already been used.
 S=add(add(Z,mul(q,F)),one,-1);T=add(add(mul(MC,J),one),mul(q,add(mul(MF,J),one,-1)))
 raw=add(mul(add(add(mul(q,q),Z,-1),mul(q,F),-1),add(mul(q,q),one,-1)),add(mul(add(MC,mul(q,MF)),J),add(mul(q,q),q,-1)))
 shifted=add(mul(add(mul(q,q),S,-1),add(mul(q,q),one,-1)),T)
 need(raw==shifted,'actual shifted packing identity')
 return 3

def source_audit(packet,mode):
 rows=packet['source'];D={n:(o,a,b)for n,o,a,b in rows};comp=packet['comparisons'];raw=mode=='raw30';signed=mode=='signed20'
 k='k'if raw else'R10b';a='a'if raw else'R12';c='c'if raw else'R10a';d='d'if raw else'R14';ga='gamma_sum'if signed else'ga'
 needed={'Lbig':('*','q','q'),'n2':('*','Lbig','q'),'wn2':('*','w','n2'),'sn2':('*','s','n2'),'UM':('*','wn2','sn2'),
 'ksn2':('*',k,'sn2'),'first_root_base':('*','UM','ksn2'),'first_next':('+','first_root_base',k),'L9':('*','first_root_base','first_next'),
 'tau_square':('*','tau','tau'),'R9':('-','tau_square',1),'R10b':('+','eta','zeta'),'R10a':('+','ksn2','eta'),'R12':('+','UM','sn2'),
 'r1':('+','r',1),'hpm1':('*','h','UM'),'R11':('+','r1','hpm1'),
 'cam2':('*',c,a),'D1':('+','wn2','cam2'),'a4':('*',4,a),'a4m5':('+','a4',3),'gam':('*',ga,'a4m5'),'R14':('+','D1','gam'),
 'a_square':('*',a,a),'A':('+','a_square','a4m5'),'c2':('*',c,c),'Ac2':('*','A','c2'),'R15':('+','Ac2',1),'L15':('*',d,d),
 'ic2':('*','i','c2'),'ic22':('*','ic2','ic2'),'L16':('*','f','f'),'f_square_minus_one':('-','L16',1),'R16':('*','A','f_square_minus_one'),
 'jc':('*','j',c),'H17':('-','jc','r'),'of':('*','o','f'),'aux_u_rhs':('-','of',c),'H2':('*','H17','H17'),
 'aux_y2':('*','y_aux','y_aux'),'aux_square_gap':('-','H2','aux_y2'),'L17':('*','ic22','aux_square_gap'),'P17':('-',1,'aux_y2'),
 'qF':('*','q','F'),'packed':('+','Z','qF'),'gap':('-','Lbig','packed'),'Lm1':('-','Lbig',1),'rproduct':('*','gap','Lm1'),
 'qMF':('*','q','MF'),'mask_factor':('+','MC','qMF'),'mask':('*','mask_factor','Jrep'),'r_lhs':('+','rproduct','mask')}
 need(all(D.get(n)==row for n,row in needed.items()),'literal kernel source map '+mode)
 for pair in [['r','r_lhs'],['L9','R9'],[k,'R11'],['L15','R15'],['ic22','R16'],['L17','P17'],['H17','aux_u_rhs']]:need(pair in comp,'retained kernel equation '+str(pair))
 if raw:
  need(all(pair in comp for pair in [['repunit','qm1'],['k','R10b'],['a','R12'],['c','R10a'],['d','R14']]),'actual positive supplied definitions at raw zeros')
  need(D['repunit']==('*','Bm1','Jrep')and D['qm1']==('-','q',1),'raw repunit interface')
 else:need(D['repunit']==('*','Bm1','Jrep')and D['q']==('+','repunit',1),'computed repunit interface')
 if signed:
  need(D['gamma_sum']==('+','rho','sigma')and D['C_partial']==('-','q','alpha')and D['marked_rhs']==('-','C_partial','scaled_t')and D['W']==('-','marked_rhs','Z'),'actual signed definitions')
  need(D['kinner']==('+','Kconstant','wn2')and D['innerC']==('*','kinner','marked_rhs')and D['local_rhs_sum']==('+','F','local_rhs')and D['local_rhs']==('*','zquot','repunit')and ['innerC','local_rhs_sum']in comp,'positive transport numerator')
 need([n for n,o,a,b in rows if 'w'in(a,b)]==['wn2'],'only scale-coordinate consumer')
 need(all('w'not in pair for pair in comp),'no direct comparison consumer')
 need(packet['polynomial_source'][:len(rows)]==rows,'full paid SOS prefix')
 # q is either supplied independently of w or computed only from positive J.
 free=packet['witnesses']+packet['fixed_numerals']+['x'];known=set(free)
 for n,o,a,b in rows:need(all(type(v)is int or v in known for v in(a,b)),'actual acyclic closure');known.add(n)
 return dict(k=k,a=a,c=c,main_root=d,gamma=ga,first_root='tau',first_base='first_root_base',q='q',R='r',strong_is_ordinary=True,positive_coordinates=len(packet['witnesses']),comparisons=len(comp),checked_producer_rows=len(needed))

def verify(root):
 blobs={}
 for n,h in PINS.items():
  data=(Path(root)/n).read_bytes();need(sha(data)==h,'pinned '+n);blobs[n]=data
 forms=json.loads(blobs['complete74_factored_first_norm.json'])['forms'];need([f['mode']for f in forms]==['raw30','positive22','signed20'],'three actual current endpoints')
 counts=Counter(algebra_identities=identities());records=[];rng=random.Random(740113)
 for form in forms:
  mode=form['mode'];p=form['packet'];ports=source_audit(p,mode);rows=p['polynomial_source'];changed=[[n,o,a,'q']if n=='wn2'else[n,o,a,b]for n,o,a,b in rows]
  need(sum(a!=b for a,b in zip(rows,changed))==1,'one actual complete-source edit')
  # Local associative identity plus unchanged downstream instructions proves
  # every comparison and complete polynomial after w_new=q²*w_old.
  for j in range(12):
   v={n:rng.randrange(-3,5)for n in p['witnesses']+p['fixed_numerals']+['x']}
   if j>=8:v={n:Fraction(x,3)for n,x in v.items()};counts['rational_cases']+=1
   old=calc(rows,v);nv=dict(v);nv['w']*=old['q']**2;new=calc(changed,nv)
   need(all(old[n]==new[n]for n,o,a,b in rows),'full supplied-coordinate pullback fixture')
   need(old[p['output']]==new[p['output']],'full output pullback fixture');counts['full_graph_fixtures']+=1;counts['register_values']+=len(rows)
  records.append(dict(mode=mode,actual_ports=ports,source_rows=len(p['source']),full_rows=len(rows),inverse='w_old=w_new/q²; every other supplied coordinate fixed',changed_row=['wn2','*','w','q']))
 # Exact local Pell pairs establish only the positive tau-gap boundary, not
 # accepting complete compiler assignments.
 for q in (16,32,64):
  for w in (1,2):
   for s in (1,3):
    X=w*q;Y=s*q**3;V=X*Y*Y;P=2*V+1;T,k=1,0
    for n in range(1,5):
     T,k=P*T+2*V*(V+1)*k,2*T+P*k
     L=V*k;g=T-L
     need(T*T-V*(V+1)*k*k==1 and g>0 and g*g+L*(2*g-k)==1,'positive first-root gap at local Pell solutions');counts['local_positive_gap_cases']+=1
 # Shifted packing and optional signed input-root margins, before dyadic
 # typing. Noncompiler masks here test only the explicitly stated bounds.
 for B in (16,32,64):
  for J in range(1,5):
   q=(B-1)*J+1;MC=2;MF0=4;T=MC*J+1+q*(MF0*J-1)
   need(3*q+1<=T<q*q-1,'strict shifted-mask window')
   for F in (1,2,q//2,q,q+1):
    for Z in sorted({1,2,q-1,q,q*q-q+1,q*q}):
     S=Z+q*F-1;R=(q*q-S)*(q*q-1)+T
     if R<=0:continue
     need(q<=S<=q*q and 3*q+1<=R<q**4 and Z<q*q,'positive-index raw window')
     counts['packing_bound_cases']+=1;counts['exceptional_boundary_cases']+=int(S==q*q)
     u=2*(B.bit_length()-1)+1;C=q-u;W=C-Z;X=q;Y=q**3;a=Y*(X+1);H=4*a+3;Delta=a*a+H;kappa=u+Delta;mu=W+a*kappa+H
     need(0<C<q and -q*q<W<q and a>q**4>q*q and mu>0,'optional weak-scale signed input-root margin')
     counts['signed_root_margin_cases']+=1;counts['negative_W_margin_cases']+=int(W<0)
     need(0<R+1<=X*Y,'weak first-index representative interval')
 # The weak inequality intentionally retains R+1=E: a negative quotient v
 # is still impossible for positive2n, including that endpoint.
 for E in (16,256,65536):
  for R in (1,E-2,E-1):
   for v in (-3,-2,-1):need(R+1+v*E<=0,'no negative first-index quotient');counts['nonpositive_index_representatives']+=1
 for t in range(4,21):
  q=1<<t;need(3*q+1>3*t,'recovered exponent exceeds cube scale');counts['dyadic_cube_margin_cases']+=1
 return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),pins=PINS,records=records,counts=dict(counts),scope='Mathematical premise/source audit for three actual complete74 scale transfers. Full positive-zero bijection uses the extracted retained109 kernel argument before old compiler typing. No maintained successor API/cost/degree review, no historical execution, no complete accepting Pell tuple claimed.')

def main():
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);a=p.parse_args();r=verify(a.root)
 if a.expect:need(same(r,json.loads(a.expect.read_text())),'exact saved receipt')
 if a.output:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 print(json.dumps(dict(status=r['status'],counts=r['counts'])))
if __name__=='__main__':main()
