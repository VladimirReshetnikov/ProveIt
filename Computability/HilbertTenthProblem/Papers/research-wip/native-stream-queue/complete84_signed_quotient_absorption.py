#!/usr/bin/env python3
"""Signed-T proof component: predecessors are authenticated inert data only."""
import argparse
import hashlib
import json
from pathlib import Path

PINS={'complete84_scaled_strong_output.py': '8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737', 'complete84_scaled_strong_output.json': '8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf', 'complete84_scaled_strong_output.md': '01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade', 'complete84_exterior_auxiliary_absorption.py': '46e42d8947c1e5cbed62a4473fa83d96115a80b334656ea45ad1f31796bde0a9', 'complete84_exterior_auxiliary_absorption.json': 'ec0b2a298d4382867ca0d638e3b52b18be3ad38a64ea7c4efb96d1ad985d692b', 'complete84_exterior_auxiliary_absorption.md': '69f8e40bd44dca5bcb2f0f292a2ad842fff5a41b2014007f3f986176cd7bd8de', 'complete84_auxiliary_ordinate_absorption.py': '9d8ea463330b31dea1af8187784981b576c932a3799ca45a5dabfe2ea0bc2c94', 'complete84_auxiliary_ordinate_absorption.json': '8101345c3c6588539fe56f340322ba573e66ce66b978db7da8154781c23547f8', 'complete84_auxiliary_ordinate_absorption.md': '9cc0fc5f3d9f72dd3fc150c1253cb038fef1eb0666dc72b1096ed86c85481b53', 'complete85_auxiliary_bezout_projection.md': 'd8f91555bed114470ee5dfb742175079f2df25e9c04d75abbf16752e70a91a4b', 'review_complete85_auxiliary_bezout_math.md': '77a4071be471db23642cabddc5bd4880debfa53441bf3640c3c45523e9bdb36d', '../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md': '47a2c5b69f3c87b7a1ddc61ef84757023de291b63d1330e2c8dc9b40e811ab8b', 'complete75_half_binomial_compiler.md': '68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117', '../../1980/FIXED_RAW_UNIVERSAL_76_PROOF.md': '75a13b5fd0c44c3ec91366306fb5876a3ea2f867e464b84cebd46ca08d060f87', '../../1980/FIXED_RAW_UNIVERSAL_78_PROOF.md': 'b28ddb9aec5225cda7dabc85fb952daf49de4041cf35910f62dabf3893749d39'}
EXPECTED_FREE=['Jrep', 'F', 'alpha', 'transport_quotient', 'f', 'h', 'i', 'auxiliary_quotient', 's', 'w', 'tau_root', 'eta', 'zeta', 'y_aux', 'Z', 'delta', 'rho', 'sigma', 'x', 'Bm1', 'Kconstant', 'twice_cell_bits', 'inner_bits', 'MC', 'MF']
EXPECTED_SOURCE=[
 ['tau_square', '*', 'tau_root', 'tau_root'],
 ['repunit', '*', 'Bm1', 'Jrep'],
 ['q', '+', 'repunit', 1],
 ['Lbig', '*', 'q', 'q'],
 ['n2', '*', 'Lbig', 'q'],
 ['wn2', '*', 'w', 'q'],
 ['sn2', '*', 's', 'n2'],
 ['UM', '*', 'wn2', 'sn2'],
 ['R10b', '+', 'eta', 'zeta'],
 ['ksn2', '*', 'R10b', 'sn2'],
 ['first_root_base', '*', 'UM', 'ksn2'],
 ['first_next', '+', 'first_root_base', 'R10b'],
 ['first_product', '*', 'first_root_base', 'first_next'],
 ['norm_first', '-', 'tau_square', 'first_product'],
 ['R10a', '+', 'ksn2', 'eta'],
 ['R12', '+', 'UM', 'sn2'],
 ['cam2', '*', 'R10a', 'R12'],
 ['D1', '+', 'wn2', 'cam2'],
 ['gamma_sum', '+', 'rho', 'sigma'],
 ['a4', '*', 4, 'R12'],
 ['a4m5', '+', 'a4', 3],
 ['gam', '*', 'gamma_sum', 'a4m5'],
 ['R14', '+', 'D1', 'gam'],
 ['L15', '*', 'R14', 'R14'],
 ['a_square', '*', 'R12', 'R12'],
 ['A', '+', 'a_square', 'a4m5'],
 ['c2', '*', 'R10a', 'R10a'],
 ['Ac2', '*', 'A', 'c2'],
 ['norm_main', '-', 'L15', 'Ac2'],
 ['norm_pair', '*', 'norm_first', 'norm_main'],
 ['q_minus_F', '-', 'q', 'F'],
 ['q_minus_FZ', '-', 'q_minus_F', 'Z'],
 ['C_after_alpha', '-', 'q_minus_FZ', 'alpha'],
 ['scaled_t', '*', 'twice_cell_bits', 'x'],
 ['marked_rhs', '-', 'C_after_alpha', 'scaled_t'],
 ['W', '-', 'marked_rhs', 'Z'],
 ['odd_index', '+', 'scaled_t', 'inner_bits'],
 ['index_product', '*', 'delta', 'A'],
 ['index_rhs', '+', 'odd_index', 'index_product'],
 ['difference_multiple', '*', 'index_rhs', 'R12'],
 ['exponent_partial', '+', 'W', 'difference_multiple'],
 ['modulus_multiple', '*', 'rho', 'a4m5'],
 ['exponent_rhs', '+', 'exponent_partial', 'modulus_multiple'],
 ['mu2', '*', 'exponent_rhs', 'exponent_rhs'],
 ['kappa2', '*', 'index_rhs', 'index_rhs'],
 ['scaled_kappa2', '*', 'A', 'kappa2'],
 ['norm_input', '-', 'mu2', 'scaled_kappa2'],
 ['norm_triple', '*', 'norm_pair', 'norm_input'],
 ['aux_y2', '*', 'y_aux', 'y_aux'],
 ['hpm1', '*', 'h', 'UM'],
 ['index_difference', '-', 'R10b', 'hpm1'],
 ['gap_product', '*', 'repunit', 'q_minus_F'],
 ['gap', '+', 'gap_product', 'q_minus_FZ'],
 ['Lm1', '-', 'Lbig', 1],
 ['rproduct', '*', 'gap', 'Lm1'],
 ['qMF', '*', 'q', 'MF'],
 ['mask_factor', '+', 'MC', 'qMF'],
 ['mask', '*', 'mask_factor', 'Jrep'],
 ['r_lhs', '+', 'rproduct', 'mask'],
 ['norm_index', '-', 'index_difference', 'r_lhs'],
 ['kinner', '+', 'Kconstant', 'w'],
 ['innerC', '*', 'kinner', 'marked_rhs'],
 ['transport_partial', '+', 'innerC', 'q_minus_F'],
 ['local_rhs', '*', 'transport_quotient', 'repunit'],
 ['norm_transport', '-', 'transport_partial', 'local_rhs'],
 ['L16', '*', 'f', 'f'],
 ['auxiliary_Tf', '*', 'auxiliary_quotient', 'f'],
 ['auxiliary_Tf_minus_one', '-', 'auxiliary_Tf', 1],
 ['auxiliary_c_Tf', '*', 'R10a', 'auxiliary_Tf_minus_one'],
 ['auxiliary_R_f2', '*', 'r_lhs', 'L16'],
 ['aux_u_rhs', '-', 'auxiliary_c_Tf', 'auxiliary_R_f2'],
 ['H2', '*', 'aux_u_rhs', 'aux_u_rhs'],
 ['aux_square_gap', '-', 'H2', 'aux_y2'],
 ['aux_coefficient_root', '*', 'i', 'Ac2'],
 ['R16', '*', 'aux_coefficient_root', 'aux_coefficient_root'],
 ['scaled_f_square', '*', 'A', 'L16'],
 ['norm_strong', '-', 'scaled_f_square', 'R16'],
 ['L17', '*', 'R16', 'aux_square_gap'],
 ['norm_aux', '+', 'L17', 'aux_y2'],
 ['norm_four', '*', 'norm_triple', 'norm_aux'],
 ['norm_product', '*', 'norm_four', 'norm_index'],
 ['all_units', '*', 'norm_product', 'norm_transport'],
 ['seven_units', '*', 'all_units', 'norm_strong'],
 ['polynomial', '-', 'seven_units', 'A'],
]
OLD_OMIT=['i','f','auxiliary_quotient','y_aux']
OMIT=['auxiliary_quotient','y_aux']
FACTORS=['norm_first','norm_main','norm_input','norm_index','norm_transport']
# Every group is disjoint. Each row receives its exact literal producer below.
BOUND_GROUPS=[
 ('units','norm_first norm_main norm_pair norm_input norm_triple norm_index norm_transport','1','=1','unit and index-sign recovery'),
 ('first','tau_square','tau^2=k^2*U*(U+1)+1','<c^4','U=XY^2<a^2<c/4; k<c'),
 ('first','R10b ksn2 R10a hpm1','k; kY; c; k-R-1','<=c','ratio and index equation'),
 ('first','first_root_base','kU','<c^2/4','U<c/4,k<c'),
 ('first','first_next','k(U+1)','<c^2/2','c>4,U<c/4,k<c'),
 ('first','first_product','k^2*U*(U+1)','<c^4/8','product of preceding two bounds'),
 ('main','cam2 D1 gam R14','ac; X+ac; gamma*H; D','<=D<c^2','positive main summands, D<A0*c'),
 ('main','gamma_sum a4 a4m5','gamma; 4a; H','<c','gamma*H<2c; H<c'),
 ('main','L15','D^2','<c^4','D<c^2'),
 ('main','a_square','a^2','<c/4','c>=psi_3(A0)'),
 ('main','A','Delta','<c','c>=psi_3(A0)'),
 ('main','c2','c^2','<c^4','c>2'),
 ('main','Ac2','Delta*c^2','<c^3','Delta<c'),
 ('input','index_product index_rhs','kappa-u; kappa','<c','input index j<R'),
 ('input','difference_multiple exponent_partial modulus_multiple exponent_rhs','a*kappa; W+a*kappa; rho*H; mu','<=mu<D<c^2','W+a*kappa>0 and W+rho*H>0'),
 ('input','mu2','mu^2','<c^4','mu<D<c^2'),
 ('input','kappa2','kappa^2','<c^2','kappa<c'),
 ('input','scaled_kappa2','Delta*kappa^2=mu^2-1','<c^4','input norm +1'),
 ('outer','repunit q Lbig n2 wn2 sn2 UM R12','q-1; q; q^2; q^3; X; Y; XY; a','<=a<c','X>=q,Y>=q^3,a=Y(X+1)'),
 ('outer','q_minus_F q_minus_FZ C_after_alpha scaled_t marked_rhs','q-F; q-F-Z; C+2dx; 2dx; C','0<value<q','original positive slacks and Nt=1'),
 ('outer','W','C-Z','absolute value <q','0<C,Z<q; W need not be positive'),
 ('outer','odd_index','2dx+b','<2q<R','2dx<q,b<=d<B<=q'),
 ('outer','index_difference','k-hE0=R+1','<a','index=+1; R+2<E0<a'),
 ('outer','gap_product gap Lm1','(q-1)(q-F); q(q-F)-Z; q^2-1','0<value<q^2','F,Z>0,F+Z<q'),
 ('outer','rproduct','gap*(q^2-1)','<q^4<=E0<a','gap<q^2'),
 ('outer','qMF','q*MF_source','<2q^2','shifted MF_source<2(B-1)'),
 ('outer','mask_factor','MC+q*MF_source','<3q^2','MC<B-1<q'),
 ('outer','mask','mask_factor*Jrep','<3q^3<a','Jrep<q; X>=q,Y>=q^3,q>=16'),
 ('outer','r_lhs','R','<a','untyped packing margin'),
 ('outer','kinner','Kconstant+w','<q^2+X<a','DC,DR<B; w=X/q'),
 ('outer','innerC','(Kconstant+w)*C','<q^3+X<a','0<C<q; w=X/q'),
 ('outer','transport_partial','innerC+q-F','<q^3+X+q<a','X>=q>=16,Y>=q^3'),
 ('outer','local_rhs','transport_quotient*(q-1)=transport_partial-1','<a','Nt=+1'),
]
FREE_GROUPS=[
 ('Jrep F alpha Z','<q<c','positive slacks and q=(B-1)Jrep+1'),
 ('eta zeta h','<c','eta,zeta<k<c; hE0=k-R-1<c'),
 ('s w','<a<c','s<Y,w<X'),
 ('tau_root','<c^2','tau_root^2<c^4'),
 ('delta rho sigma','<c','direct main and input j<R bounds'),
 ('transport_quotient','<a<c','positive local_rhs=t(q-1)<a'),
 ('x','<q<c','2dx<q'),
 ('Bm1','<q<c','B-1<q'),
 ('Kconstant','<q^2<a<c','DC,DR<B after high-monomial correction'),
 ('twice_cell_bits inner_bits','<q<c','2d<B<=q, b<=d'),
 ('MC','<q<c','MC<B-1'),
 ('MF','<2q<c','shifted MF<2(B-1),c>2Y>=2q^3'),
]
ADDED_BOUNDS={
 'L16':('f^2','<f^3'), 'auxiliary_R_f2':('R*f^2','<f^3'),
 'aux_coefficient_root':('S=Delta*i*c^2','<f^2'), 'R16':('S^2=Delta*(f^2-1)','<f^3'),
 'scaled_f_square':('Delta*f^2','<f^3'), 'norm_strong':('Delta','<f'),
}
def ck(ok,msg):
 if not ok:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def encode(v):return json.dumps(v,sort_keys=True,separators=(',',':'),ensure_ascii=True).encode()
def read(p):
 def pairs(xs):
  d={}
  for k,v in xs:ck(k not in d,'duplicate JSON key');d[k]=v
  return d
 def bad(v):raise ValueError('noninteger JSON number: '+v)
 return json.loads(p.read_text(),object_pairs_hook=pairs,parse_float=bad,parse_constant=bad)
def census(p,omitted):
 taint=set(omitted);outside=[];known=set(p['free'])
 for n,o,a,b in p['source']:
  ck(type(n)is str and n not in known and o in ['+','-','*'],'SSA/op')
  ck(all(type(z)is int or type(z)is str and z in known for z in [a,b]),'topology')
  known.add(n)
  if a in taint or b in taint:taint.add(n)
  else:outside.append(n)
 return outside,[n for n in p['free'] if n not in omitted]
def num(v):return {():v} if v else {}
def var(n):return {(n,):1}
def add(a,b,s=1):
 out=dict(a)
 for m,c in b.items():out[m]=out.get(m,0)+s*c
 return {m:c for m,c in out.items() if c}
def mul(a,b):
 out={}
 for m,c in a.items():
  for n,d in b.items():
   k=tuple(sorted(m+n));out[k]=out.get(k,0)+c*d
 return {m:c for m,c in out.items() if c}
def pw(a,n):
 out=num(1)
 for _ in range(n):out=mul(out,a)
 return out
def records(a):return [[list(m),c] for m,c in sorted(a.items())]
def source_identity(p,old):
 expanded=['norm_pair','norm_triple','c2','Ac2'];cuts=set(old)-set(expanded)
 env={n:var('port:'+n) for n in p['free']}
 for n,o,a,b in p['source']:
  if n in cuts:env[n]=var('cut:'+n);continue
  a=env[a] if type(a)is str else num(a);b=env[b] if type(b)is str else num(b)
  env[n]=mul(a,b) if o=='*' else add(a,b,1 if o=='+' else -1)
 D,c,R=[var('cut:'+n) for n in ['A','R10a','r_lhs']]
 i,f,T,y=[var('port:'+n) for n in ['i','f','auxiliary_quotient','y_aux']]
 S=mul(mul(D,i),pw(c,2));V=add(mul(c,add(mul(T,f),num(1),-1)),mul(R,pw(f,2)),-1)
 Ns=add(pw(f,2),mul(mul(D,pw(i,2)),pw(c,4)),-1)
 Na=add(mul(pw(S,2),add(pw(V,2),pw(y,2),-1)),pw(y,2))
 P5=num(1)
 for n in FACTORS:P5=mul(P5,env[n])
 normalized=add(mul(mul(P5,Na),Ns),num(1),-1)
 ck(env['aux_u_rhs']==V and env['aux_coefficient_root']==S,'actual V,S binding')
 ck(env['norm_aux']==Na and env['norm_strong']==mul(D,Ns),'actual auxiliary/strong factors')
 ck(env[p['output']]==mul(D,normalized),'whole84 normalized product identity')
 o=add(mul(c,T),mul(R,f),-1)
 j=add(add(mul(T,f),mul(mul(mul(R,D),pw(i,2)),pw(c,3)),-1),num(1),-1)
 ck(add(V,c)==mul(f,o),'exact congruence V+c=f*(cT-Rf)')
 ck(add(add(V,R),mul(c,j),-1)==mul(R,add(num(1),Ns,-1)),'V+R congruence modulo c after Ns=1')
 ck(all(m.count('port:auxiliary_quotient')<=2 for m in env[p['output']]),'literal T degree')
 return dict(rows_visited=len(p['source']),valid_auxiliary_independent_cuts=sorted(cuts),expanded_dependent_products=expanded,
  all_auxiliary_rows_expanded=True,all_finalizer_rows_expanded=True,T_unrestricted_formal_indeterminate=True,
  whole_source_identity='F84=Delta*(P5*Na*(f^2-Delta*i^2*c^4)-1)',
  full_output_coefficients=records(env[p['output']]),normalized_product_coefficients=records(normalized),
  literal_V_coefficients=records(V),literal_S_coefficients=records(S),
  congruence_f_quotient=records(o),congruence_c_quotient=records(j),
  congruence_c_correction='V+R-c*j=R*(1-Ns_normalized)',positive_restoration_claim=False)
def bound_census(p,old,free,new,newfree):
 by={r[0]:r for r in p['source']};mapped={};groups={}
 for group,names,formula,bound,reason in BOUND_GROUPS:
  for n in names.split():
   ck(n not in mapped,'duplicate bound name')
   mapped[n]=dict(name=n,literal_producer=by[n],group=group,value_description=formula,bound=bound,reason=reason)
   groups[group]=groups.get(group,0)+1
 ck(set(mapped)==set(old),'all64 computed bounds exactly')
 ck(groups==dict(units=7,first=8,main=12,input=9,outer=28),'64 group sizes')
 fm={}
 for names,bound,reason in FREE_GROUPS:
  for n in names.split():
   ck(n not in fm,'duplicate supplied bound');fm[n]=dict(name=n,bound=bound,reason=reason)
 ck(set(fm)==set(free),'all21 supplied bounds exactly')
 ck(set(new)-set(old)==set(ADDED_BOUNDS),'exact six new computed bounds')
 ck(set(newfree)-set(free)=={'i','f'},'exact new supplied bounds')
 extra=[dict(name=n,literal_producer=by[n],value=ADDED_BOUNDS[n][0],bound=ADDED_BOUNDS[n][1]) for n in new if n not in old]
 return dict(old_computed=[mapped[n] for n in old],old_supplied=[fm[n] for n in free],group_counts=groups,
  added_computed=extra,added_supplied=[dict(name='i',bound='i<f<f^3'),dict(name='f',bound='f<f^3')],
  old_bound='absolute value <c^4',new_bound='absolute value <=f^3',
  direct_input_premises=['mu>a-q>0','E_input=W+rhoH<X+gammaH=E_R','input_index<R',
   'W+a*kappa>a-q>0','W+rhoH>H-q>0'],
  uses_positive_T_parent_theorem=False,uses_R_three_mod_four=False,uses_X_equals_two_to_R=False,
  uses_canonical_input_index=False,all_bounds_are_quantified_proof_not_sampling=True)
def pell(A,n,mod=None):
 # Binary powering of the quadratic unit, fresh independent arithmetic.
 D=A*A-1;r=(1,0);b=(A,1)
 def mm(u,v):
  x=u[0]*v[0]+D*u[1]*v[1];y=u[0]*v[1]+u[1]*v[0]
  return (x%mod,y%mod) if mod else (x,y)
 while n:
  if n&1:r=mm(r,b)
  b=mm(b,b);n//=2
 return r
def C_coefficients(n):
 cs=[[1],[-3,4]]
 while len(cs)<n:
  a,b=cs[-1],cs[-2];out=[0]*(len(a)+1)
  for j,v in enumerate(a):out[j]-=2*v;out[j+1]+=4*v
  for j,v in enumerate(b):out[j]-=v
  cs.append(out)
 return cs[:n]
def value(cs,z):
 out=0
 for c in reversed(cs):out=out*z+c
 return out
def finite_evidence():
 cs=C_coefficients(14);identities=[];rank=[];step=[];signed=[];growth=[];inputmonotone=[]
 for A in range(2,9):
  for v,C in enumerate(cs):
   ell=2*v+1;x,y=pell(A,ell)
   ck(value(C,-(A*A-1))==(-1)**v*y,'odd-index reduction')
   ck(value(C,A*A)*A==x and value(C,0)==(-1)**v*ell,'odd quotient/zero identity')
   identities.append([A,v])
  for p in range(2,7):
   D,c=pell(A,p)
   for j in [1,2,c,c+1,2*c]:
    rem=pell(A,p*j,c*c)[1]
    ck(rem%c==0,'p divides m rank congruence setup')
    lhs=rem//c;rhs=j*pow(D,j-1,c)%c
    ck(lhs==rhs and ((lhs==0)==(j%c==0)),'normalized c-square divisibility equivalence')
    rank.append([A,p,j,c,lhs])
  for m in range(3,18):
   f=pell(A,m)[0]
   for p in range(1,(m+1)//2):
    if 2*p>=m:continue
    target=pell(A,2*p,f)[0]
    for ell in range(4*m):
     if pell(A,2*ell,f)[0]==target:
      ck(ell%m in [p%m,(-p)%m],'signed step-down')
      step.append([A,m,p,ell])
  E=[pell(A,j)[0]-(A-2)*pell(A,j)[1] for j in range(22)]
  ck(all(a<b for a,b in zip(E,E[1:])),'projected root strict increase')
  for j in range(1,21):
   ps=pell(A,j)[1];prev=pell(A,j-1)[1]
   ck(E[j+1]-E[j]==(4*A-3)*ps-prev>0,'projected recurrence difference')
  inputmonotone.append([A,E])
 # Small main/strong/auxiliary components: both V signs, never compiler histories.
 for A in range(2,5):
  for R in [3,5]:
   D,c=pell(A,R);m=R*c;f,ps=pell(A,m);ck(ps%(c*c)==0,'normalized strong component')
   i=ps//(c*c);Delta=A*A-1;S=Delta*i*c*c
   ell=R;e=-(-1)**((R-1)//2);chi,y=pell(S,ell);ck(chi%S==0,'aux root quotient')
   V=e*(chi//S);numT=V+c+R*f*f;denT=c*f
   ck(numT%denT==0,'signed T component integrality');T=numT//denT
   ck(f*f-Delta*i*i*c**4==1 and S*S*V*V-(S*S-1)*y*y==1,'component norms')
   ck(V==c*(T*f-1)-R*f*f and (T>0)==(e>0),'signed affine component')
   ck(c>2*R and f>2*c and (V+c)%f==0 and (V+R)%c==0,'component congruences')
   signed.append(dict(A0=A,R=R,strong_index=m,sign_V=e,sign_T=1 if T>0 else -1,
    c=c,f_bits=f.bit_length(),T_bits=abs(T).bit_length(),
    auxiliary_index=ell,compiler_history=False,complete_source_zero=False))
 for S in range(2,17):
  for ell in range(2,22):
   chi=pell(S,ell)[0];ck(chi>S**ell,'chi strict power growth')
   growth.append([S,ell])
 separation=[]
 for A in range(2,9):
  for R in [3,5,7,9]:
   c=pell(A,R)[1];f=2*c+1
   for ell in range(1,R,2):
    z=pell(A,ell)[1];ck(0<c-z<c+z<2*c<f,'both smaller-index signs excluded')
    separation.append([A,R,ell])
 integer_bounds=[]
 for f in range(2,40):
  ck((f-1)+(f-1)*f*f<f**3,'strict constant term including T zero')
  for R in range(5,15):
   ck(f**(R-2)+f**3<=2*f**(R-2)<=f**(R-1),'quotient growth contradiction')
  integer_bounds.append(f)
 cutoffs=[]
 for t in range(13):
  for L in [1,2,3,4,5,7,8,9,15,16,17,31,32,33,255,256,257,1024]:
   bound=3*t+(L-1).bit_length()+3;R=bound+1
   for f in [2,3,5,11]:ck(f**(R-4)>=L*f**(3*t),'cutoff contradiction')
   cutoffs.append([t,L,bound])
 return dict(C_coefficients=cs,odd_polynomial_checks=identities,normalized_rank_checks=rank,
  signed_step_down_checks=step,signed_auxiliary_components=signed,projected_input_monotonicity=inputmonotone,
  chi_growth_checks=growth,small_index_separation=separation,integer_constant_term_checks=integer_bounds,
  cutoff_checks=cutoffs,scope='Standalone arithmetic components only; no compiled histories or full source zeros')
def build(root):
 for n,h in PINS.items():ck(sha((root/n).read_bytes())==h,'pin '+n)
 ext=read(root/'complete84_exterior_auxiliary_absorption.json')
 ordn=read(root/'complete84_auxiliary_ordinate_absorption.json')
 allpins=dict(PINS)
 for prior,stem in [(ext,'complete84_exterior_auxiliary_absorption'),(ordn,'complete84_auxiliary_ordinate_absorption')]:
  ck(prior['source_sha256']==PINS[stem+'.py'],'predecessor self binding')
  for n,h in prior['pins'].items():
   ck(n not in allpins or allpins[n]==h,'conflicting pin');allpins[n]=h
   ck(sha((root/n).read_bytes())==h,'transitive pin '+n)
 p=read(root/'complete84_scaled_strong_output.json')['packet']
 ck(p['free']==EXPECTED_FREE and p['source']==EXPECTED_SOURCE and p['output']=='polynomial','full literal84 contract')
 ck(p['source']==ext['authenticated_parent_source']==ordn['authenticated_parent_source'],'three source copies')
 old,oldfree=census(p,OLD_OMIT);new,newfree=census(p,OMIT)
 ck(len(old)==64 and len(oldfree)==21 and len(new)==70 and len(newfree)==23,'full censuses')
 ck(old==ext['source_census']['computed_exterior_in_source_order'],'old literal census')
 ck(new==ordn['census']['computed_in_source_order'] and newfree==ordn['census']['free_values'],'ordinate interface equality')
 ck([r for r in p['source'] if 'auxiliary_quotient' in r[2:]]==[['auxiliary_Tf','*','auxiliary_quotient','f']],'sole literal T consumer')
 by={r[0]:r for r in p['source']};live=set();todo=[p['output']]
 while todo:
  n=todo.pop()
  if type(n)is int or n in live:continue
  live.add(n)
  if n in by:todo+=by[n][2:]
 ck(live==set(p['free'])|set(by),'all84 rows and25 free ports live')
 count={o:sum(r[1]==o for r in p['source']) for o in ['*','+','-']}
 ck(count['*']==47 and count['+']+count['-']==37,'actual84 ledger')
 return dict(status='PASS_SIGNED_AUXILIARY_QUOTIENT_ABSORPTION',source_sha256=sha(Path(__file__).read_bytes()),
  pins=allpins,parent_packet_sha256=sha(encode(p)),authenticated_parent_source=p['source'],
  authenticated_free_ports=p['free'],source_counts=dict(total=84,multiplications=47,additions_subtractions=37),
  census=dict(old_computed=old,old_free=oldfree,new_computed=new,new_free=newfree,total93=93),
  source_identities=source_identity(p,old),bound_audit=bound_census(p,old,oldfree,new,newfree),
  finite_evidence=finite_evidence(),
  theorem=dict(domain='valid fixed compiler; only T is signed; all other supplied witnesses and input positive',
   normalized_rank='c=psi_p(A0), f=chi_m(A0), psi_m(A0)=i*c^2, p*c divides m, p=R',
   input_bound='2d*x+b<R',old85_bound='absolute values <c^4',all93_bound='absolute values <=f^3',
   auxiliary_growth='ell>=R; abs(V)>f^(R-1); abs(T)>f^(R-4)',
   polynomial_cutoff='R<=3*degree(G)+ceil(log2(max(1,l1(G))))+3',zero_G_sector='empty',
   fixed_G_coefficients=True,R_three_mod_four_assumed=False,full_signed_compiler_transfer=False,
   positive_T_parent_restoration_used=False),
  scope=dict(predecessor_execution=False,generic_G_compiler=False,new_circuit=False,new_operation_bound=False,
   sampled_full_zeros=False,finite_components_prove_quantified_theorem=False))
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',required=True,type=Path)
 g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path)
 args=ap.parse_args();result=build(args.root)
 if args.output:
  with args.output.open('x') as f:f.write(json.dumps(result,sort_keys=True,indent=2)+'\n')
 else:ck(encode(result)==encode(read(args.expect)),'exact type-sensitive receipt')
 print(result['status'],'84 literal rows; 64+21 and70+23 bounds; signed-T cutoff')
if __name__=='__main__':main()
