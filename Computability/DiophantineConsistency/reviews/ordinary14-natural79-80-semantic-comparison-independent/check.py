#!/usr/bin/env python3
"""Exact source/graph and algebra cuts only: not a Lean or iPRA proof."""
from pathlib import Path
from functools import lru_cache
import hashlib, json, sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
pins={
'research/ordinary14-natural-forced-w79/candidate.json':'0d047283e1aed25040871e7d0b797ac168e5f80c596d4551fec916d48fe84cb5',
'research/ordinary14-natural-forced-gamma80/candidate.json':'136560324b95b3fda68d10ebe49bdba0a02e950e0bf6b7f1b1588baea4805bf5',
'research/ordinary14-natural79-wshift-model-draft/Natural79WShift.lean':'7635b50c819f665a6d9410758b3db01c70d3b42c1fff2aee6f3733263f76d7a1',
'research/ordinary14-natural79-zero-w-divisibility-client-draft/Natural79ZeroWDivisibility.lean':'5166f77208e4af6ed8214663aa3b07550f86796f7183c46e0f1039b0d87c4293',
'research/ordinary14-natural80-gamma-client-draft/Natural80GammaClient.lean':'7fca431907062c8578970ae7840f37d3710f09f49c0e1e4a784ba7a94cb8288b',
'research/ordinary14-natural80-partial74-bridge-draft/Natural80Partial74.lean':'942674c7951850ae30d457410cfc7a0359fc255831c31a87fc914a5ef3035c16',
'research/ordinary14-natural79-zero-w-root-cut-draft/Natural79ZeroWRootCut.lean':'c3fd2660899139ddd335214893e5698a4124399432604111a6aa1942bc8009ec',
'research/ordinary14-natural79-zero-w-main-norm-draft/Natural79ZeroWMainNorm.lean':'afacf4636f4b66e2bff939300347ba5568b72d477a3028ec0a424aba42ce8009',
'research/ordinary14-natural80-gamma-premises-draft/GammaPremises.lean':'cfdbb97e748edbef9a8bf121cc3e44ac09bc91dc1e60e362b32d675df7ad7192'}
s={}
for p,h in pins.items():
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;s[p]=b.decode()
def src(name):return next(v for k,v in s.items() if k.endswith('/'+name))
a=json.loads(src('candidate.json')) # dictionary insertion order: 79 first
b=json.loads(s['research/ordinary14-natural-forced-gamma80/candidate.json'])
assert len(a['source'])==79 and len(b['source'])==80
assert a['witnesses']==b['witnesses'] and a['fixed_numerals']==b['fixed_numerals']
assert a['witnesses'][6]=='n_w' and a['witnesses'][12]=='n_gamma'
assert ['w','+','n_w',1] in b['source']
assert a['source']==[[n,op,'n_w' if x=='w' else x,'n_w' if y=='w' else y] for n,op,x,y in b['source'] if n!='w']
shift=src('Natural79WShift.lean')
for x in ('if j = 6 then v j - 1 else v j','v79 6 = v80 6 + 1',
          'if j = 6 then v j + 1 else v j','positive_w : ∀ v',
          'simpa [w, add_comm] using hz'):
 assert x in shift,x
partial=src('Natural80Partial74.lean')
assert 'j = 0 ∨ j = 3 ∨ j = 8 ∨ j = 11 ∨ j = 12' in partial
# Exact sparse integer polynomials. A variable name denotes a formal generator.
def K(i):return {():i} if i else {}
def V(name):return {(name,):1}
def add(a,b):
 z=dict(a)
 for m,c in b.items():z[m]=z.get(m,0)+c
 return {m:c for m,c in z.items() if c}
def neg(a):return {m:-c for m,c in a.items()}
def sub(a,b):return add(a,neg(b))
def mul(a,b):
 z={}
 for m,c in a.items():
  for n,d in b.items():
   key=tuple(sorted(m+n));z[key]=z.get(key,0)+c*d
 return {m:c for m,c in z.items() if c}
def sq(a):return mul(a,a)
rows={n:(op,x,y) for n,op,x,y in a['source']}
# Make Y,U,R algebraic cuts, so results assert identities for any values of
# these shared nodes, not merely numerical samples.
@lru_cache(None)
def ev(t):
 if type(t)==int:return K(t)
 if t=='n_w':return K(0)
 if t in ('Y','U','R'):return V(t)
 if t not in rows:return V(t)
 op,x,y=rows[t];x,y=ev(x),ev(y)
 return add(x,y) if op=='+' else sub(x,y) if op=='-' else mul(x,y)
Y,U,R,eta,zeta,gamma,r=map(V,['Y','U','R','n_eta','n_zeta','n_gamma','n_r'])
one=K(1); E=add(eta,one);k=add(add(E,zeta),one);c=add(E,mul(Y,k));H=add(mul(K(4),Y),K(3))
cut=sub(mul(U,gamma),sub(add(E,zeta),R))
assert ev('X')=={} and ev('ell')=={} and ev('F0')==sq(r)
assert ev('a')==Y and ev('c')==c and ev('H')==H
assert ev('Delta')==add(sq(Y),H) and ev('shift')==cut
assert ev('Dstar')==add(mul(U,mul(Y,c)),mul(H,cut))
# The guard at J=0,w=0 is -((n_F+n_alpha+1)K0+n_F).
@lru_cache(None)
def evguard(t):
 if type(t)==int:return K(t)
 if t in ('n_w','n_J'):return {}
 if t not in rows:return V(t)
 op,x,y=rows[t];x,y=evguard(x),evguard(y)
 return add(x,y) if op=='+' else sub(x,y) if op=='-' else mul(x,y)
f,alpha,K0=map(V,['n_F','n_alpha','K0'])
assert evguard('guard')==neg(add(mul(add(add(f,alpha),one),K0),f))
# Ring certificate: from D=Ud and D=U*a*c+H*shift, write U(d-ac)=Hz;
# d²=1+(H+a²)c² then forces H|U. No cancellation or sign case used.
d,a0,c0,h,u,z,q=map(V,['d','a','c','H','U','z','q'])
norm=sub(sq(d),add(one,mul(add(h,sq(a0)),sq(c0))))
root=sub(mul(u,sub(d,mul(a0,c0))),mul(h,z))
witness=sub(mul(z,add(d,mul(a0,c0))),mul(u,sq(c0)))
assert sub(u,mul(h,witness))==sub(mul(root,add(d,mul(a0,c0))),mul(u,norm))
# For H=4Y+3 and U=Yq², if U=Hz then H|(3q²).
y=V('y');hq=add(mul(K(4),y),K(3));uu=mul(y,sq(q));second=sub(uu,mul(hq,z))
assert sub(mul(hq,sub(sq(q),mul(K(4),z))),mul(K(3),sq(q)))==mul(K(4),second)
client79=src('Natural79ZeroWDivisibility.lean')
for x in ('(hbeta : (p 0 : DiffRing V)=ι beta)','(hK : (p 1 : DiffRing V)=ι K)',
          '(hb : 0<beta)','J_pos_of_zero_w_zero p K v hK hz hw',
          'signed_dvd_three_square_of_zero_w_zero p beta v hbeta hb hJ hz hw',
          'natural_dvd_three_square (q beta v) (y beta v) hsigned',
          'no_divisor_in_window (q beta v) (y beta v) hq hY hnatural'):
 assert x in client79,x
client80=src('Natural80GammaClient.lean')
for x in ('(hKpos : 0<K) (hMCbound : MC<beta) (hMFbound : MF<2*beta)',
          'let u := partial74 v','have hw : 0<u 6', 'have hs : 0<u 7',
          'have hgammaU : u 12=0', 'have hfirst : u 8*u 8=1+m beta u*(m beta u+1)*k u*k u',
          'large_ordinate_of_two_norms','gamma_zero_impossible'):
 assert x in client80,x
premises=src('GammaPremises.lean')
assert '(hm : 0<m)' in premises and '(hfirst : tau*tau=1+m*(m+1)*k*k)' in premises
# Small explicit boundary example: at K0=F=J=w=0, guard equals 0, not a
# strictly negative value; unlike the gamma route K0>0 is not needed here.
assert -(0+0+1)*0-0==0
print(json.dumps({'scope':'pinned source interfaces, exact graph edit and sparse-polynomial cuts; no Lean/model theorem',
 'pinned_files':len(pins),'graph_rows':[79,80], 'partial74_unshifted_slots':[0,3,8,11,12],
 'w_zero_exact_cuts':['X','ell','F0','a','c','H','Delta','shift','Dstar','guard_at_J_zero'],
 'exact_divisibility_certificates':2,'boundary_K0_F_zero_checked':True,
 'lean_elaboration_or_ipra_proof':False},indent=2,sort_keys=True))
