#!/usr/bin/env python3
"""Independent source, exact norm extraction and compact-client audit."""
from pathlib import Path
import collections,hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
b='research/ordinary13-residue90-norm-model-draft/'
l=pin(b+'Residue90Literal.lean.src','00ec512e2f9069bafd06edb3cf1cb86a7bd3ca2656b6d67a840981294d1b69af')
r=pin(b+'Residue90Residuals.lean.src','efc4bac39b680966c387f03d5a1f2df65899ee5b470adf0d9fbb769bd1069925')
n=pin(b+'Residue90GraphNorms.lean.src','422b2bf043181eacdaf047204eeed952ce36383afe84ee614999da4912ad6805')
s=pin(b+'Residue90SignedNorms.lean.src','f0f7b2af039ed45c19cb45170d8f6bed601451f794d871b7b21c818fd1cac70a')
pb=pin(b+'Residue90CompactPortBounds.lean.src','11ba8e4e01d29b956926a26b04815d5a660b79caabfce7b8cc1ce6d5c85d615a')
gg=pin(b+'Residue90GraphGamma.lean.src','1260994075d32f7ba5f927c1444ee8ad9c954134ec0f563185c3e2b846a52d5b')
cg=pin(b+'Residue90CompactGraphGamma.lean.src','02c81eb303910d459890f3a001b8bdd65dccbe5f52e9bc05a24a6ddac383604b')
pin(b+'receipt.json','df70467acf2a7671cd1059407d0da5e084ac7203860774053efbeb4545b015dd')
pin('reviews/ordinary13-residue90-gamma-model-independent/result.json','04efe5f176e670197db8e1808430d05c8921abe9166fcf7366dba02edbc6d59e')
g=json.loads(pin('research/ordinary13-natural-residue-forced90-degree56/candidate.json','e65b2aa417a94320aafc0f93b2ae5d30ec69ca1d401762668f0f13d1d431f946'))
for source in (l,r):
 for i,name in enumerate(g['witnesses']):assert f'let {name} : Expr (Fin 13) := .var {i}' in source
 for i,name in enumerate(g['fixed_numerals']):assert f'let {name} : Expr (Fin 13) := .constant (p {i})' in source
 for name,op,x,y in g['source']:assert f'  let {name} := {x} {op} {y}\n' in source
assert 'def residuals (p : Fin 4 → ℤ) : Fin 4 → Expr (Fin 13)' in r
vec=re.findall(r'^  !\[([^\n]+)\]$',r,re.M);assert len(vec)==1 and len(vec[0].split(','))==4
for x in ['(hFq : v 1+1≤q p v)','P72Root.ι_tsub hq1','P72Root.ι_tsub hFq','P72Root.ι_tsub hq2','(hg : v 12=0)','rank p v+v 6*Y p v*q p v+1','all_residuals_zero _ v hz 0','all_residuals_zero _ v hz 1']:assert x in n,x
for x in ['ReducedNormSigned.natural_magnitude_square z','ArithmeticAdaptiveQuotients2011.scaled_quotient','P72Root.ι_magnitude_sq','∃ tau : V','∃ d : V']:assert x in s,x
for x in ['CompactFixedBeta.bounds (V:=V) J hJ','ArithmeticAdaptiveRankWindow2011.scalar_rank_window','(hgap : F+alpha<q)','CompactSymbolicPorts.ports CompactFixedBeta.betaNat K','CompactSymbolicPorts.lowNat CompactSymbolicPorts.highNat']:assert x in pb,x
for x in ['(hb : 0<v 0*(p 0:V))','(hU : 0<U p v)','(hq : 2≤q p v)','(hX : 1≤v 6)','(hY : (q p v)^3≤Y p v)','(hFq : v 1+1≤q p v)','(hR : rank p v+', 'Residue90GammaModelDraft.gamma_pos_of_fact_cut']:assert x in gg,x
for x in ['theorem gamma_positive (K : ℕ)','(hJ : 0<v 0) (hX : 1≤v 6)','(hgap : (v 1+1)+(v 2+1)<q (ports K) v)','have hp0','have hp2','have hp3','CompactFixedBeta.bounds','compact_rank_window','gamma_positive_of_graph_facts']:assert x in cg,x
# Independently expand the two signed norms and rank over a free ring.
def atom(x):return {(x,):1}
def add(a,b,k=1):
 d=dict(a)
 for m,v in b.items():d[m]=d.get(m,0)+k*v
 return {m:v for m,v in d.items() if v}
def mul(a,b):
 d=collections.defaultdict(int)
 for ma,ca in a.items():
  for mb,cb in b.items():d[tuple(sorted(ma+mb))]+=ca*cb
 return {m:v for m,v in d.items() if v}
targets={'A0','A1','Z','R','Dstar'};rows={x[0]:x for x in g['source']};need=set(targets);todo=list(targets)
while todo:
 for x in rows.get(todo.pop(),[None,None,None,None])[2:]:
  if isinstance(x,str) and x not in need:need.add(x);todo.append(x)
env={x:atom(x) for x in g['witnesses']+g['fixed_numerals']};env['n_gamma']={}
for name,op,x,y in g['source']:
 if name not in need:continue
 x=env[x] if isinstance(x,str) else ({():x} if x else {});y=env[y] if isinstance(y,str) else ({():y} if y else {})
 env[name]=mul(x,y) if op=='*' else add(x,y,-1 if op=='-' else 1)
one={():1};v=lambda x:atom('n_'+x);shift=lambda x:add(v(x),one)
J,X=v('J'),v('X');F,alpha=shift('F'),shift('alpha');beta,K0,MC,MF=map(atom,['beta','K0','MC','MF'])
bm=mul(J,beta);q=add(one,bm);q2=mul(q,q);Y=mul(mul(q,q2),shift('s'));k=add(shift('eta'),shift('zeta'));c=add(shift('eta'),mul(Y,k));A=add(mul(X,Y),Y);H=add({():3},mul({():4},A));delta=add(H,mul(A,A));U=mul(Y,q2);m=mul(mul(X,Y),Y)
Bt=add(mul(add(add(q,F,-1),alpha,-1),add(X,K0)),F,-1)
Z=add(mul(bm,add(add(add(mul(m,k),k),shift('r')),mul(k,Bt),-1)),Bt,-1)
R=add(mul(add(mul(add(q,one,-1),add(q,F,-1)),alpha),add(q2,one,-1)),mul(add(MC,mul(q,MF)),J))
P=add(mul(U,add(X,mul(A,c))),mul(H,add(add(R,mul(mul(X,Y),q)),one)));N=mul(H,k)
assert env['Z']==Z and env['R']==R and env['Dstar']==add(P,N,-1)
assert env['A0']==add(mul(Z,Z),mul(mul(bm,bm),add(one,mul(mul(m,add(m,one)),mul(k,k)))),-1)
assert env['A1']==add(mul(add(P,N,-1),add(P,N,-1)),mul(mul(U,U),add(one,mul(delta,mul(c,c)))),-1)
assert not re.search(r'(?m)^\s*(?:sorry|axiom)\b',l+r+n+s+pb+gg+cg)
print(json.dumps({'scope':'static source and exact free-ring graph norm audit; no Lean','literal_and_residual_rows':90,'residual_arity':4,'first_norm_rank_and_gamma_zero_main_norm_exact':True,'truncated_rank_requires_F_le_q':True,'compact_symbolic_K_arbitrary':True,'compact_client_explicit_J_X_and_positive_C_premises':True,'selected_bytes_provider_and_endpoint_open':True},sort_keys=True,indent=2))
