#!/usr/bin/env python3
"""Independent graph, symbolic-square and degree-ray audit; no Lean."""
from pathlib import Path
import hashlib,itertools,json,math,zlib
D=Path(__file__).resolve().parents[2]
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(path,digest):
 b=(D/path).read_bytes();assert sha(b)==digest,path;return b
p=json.loads(pin('research/ordinary13-natural-unit-product88/candidate.json','95fdd3495b777a0bdf64c95f6dd24cda660dee42f0508c76fdb081da21f42a5a'))
c=json.loads(pin('research/ordinary13-natural-forced-gamma87/candidate.json','e753c7c5f8110b9f15e84c9f0da88847a54486f442b60b11812ca3688ca55e21'))
rank=pin('Lean/DiophantineConsistency/ArithmeticAdaptiveRankWindow2011.lean','0895f6e74b29c2cc2e4542d739b238352778750da62766819caeb105995fb794').decode()
assert '(hbeta : 0<beta) (hJ : 0<J) (hF : 0<F) (halpha : 0<alpha)' in rank
assert '(hMC : MC<beta) (hMF : MF<2*beta) (hq : q=beta*J+1)' in rank
assert '(hgap : F+alpha<q)' in rank and ')+q^3+q+1≤q^4' in rank
assert p['domain']==c['domain']=='nonnegative integers' and p['witnesses']==c['witnesses'] and len(c['witnesses'])==13
assert p['fixed_numerals']==c['fixed_numerals']==['beta','K0','MC','MF']
a={r[0]:r[1:] for r in p['source']};b={r[0]:r[1:] for r in c['source']}
assert len(a)==88 and len(b)==87 and set(a)-set(b)=={'gamma'} and set(b)<=set(a)
assert a['gamma']==['+','n_gamma',1]
for n,row in b.items():
 op,x,y=a[n];assert row==[op,'n_gamma' if x=='gamma' else x,'n_gamma' if y=='gamma' else y]
seen=set(c['witnesses']+c['fixed_numerals']); assert len(seen)==17
for n,op,x,y in c['source']:
 assert n not in seen and op in ('+','-','*') and all(type(v) is int or v in seen for v in (x,y));seen.add(n)
live={'out'}
for n,op,x,y in reversed(c['source']):
 if n in live:live.update(v for v in (x,y) if isinstance(v,str))
assert set(b)|set(c['witnesses'])|set(c['fixed_numerals'])<=live
shape={'F':['+','n_F',1],'alpha':['+','n_alpha',1],'w':['+','n_w',1],'s':['+','n_s',1],
 'eta':['+','n_eta',1],'qm':['*','n_J','beta'],'q':['+',1,'qm'],'X':['*','q','w'],
 'q2':['*','q','q'],'q3':['*','q','q2'],'Y':['*','q3','s'],'U':['*','Y','q2'],
 'qF':['-','q','F'],'C':['-','qF','alpha'],'g26':['+','X','K0'],'g27':['*','C','g26'],
 'Bt':['-','g27','F'],'E':['*','X','Y'],'kbase':['+','eta','n_zeta'],'k':['+','kbase',1],
 'kY':['*','Y','k'],'c':['+','eta','kY'],'a':['+','E','Y'],'g15':['*',4,'a'],
 'H':['+',3,'g15'],'g17':['*','a','a'],'Delta':['+','H','g17'],'g19':['*','a','c'],
 'b0':['+','X','g19'],'ell':['*','E','kY'],'g30':['+','ell','k'],
 'g31':['+','g30','n_r'],'folded_kBt':['*','k','Bt'],'folded_g31':['-','g31','folded_kBt'],
 'g32':['*','qm','folded_g31'],'Z':['-','g32','Bt'],'g38':['*','Z','Z'],
 'g39':['*','qm','qm'],'g40':['*','ell','g30'],'g41':['+',1,'g40'],
 'g42':['*','g39','g41'],'A0':['-','g38','g42'],'g44':['*','qF','qm'],
 'G':['+','alpha','g44'],'g46':['-','q2',1],'g47':['*','G','g46'],
 'g48':['*','MF','q'],'g49':['+','MC','g48'],'g50':['*','n_J','g49'],
 'R':['+','g47','g50'],'r0':['-','kbase','R'],'g54':['*','U','n_gamma'],
 'shift':['-','g54','r0'],'g58':['*','U','b0'],'g59':['*','H','shift'],
 'Dstar':['+','g58','g59'],'g61':['*','Dstar','Dstar'],'g62':['*','U','U'],
 'c2':['*','c','c'],'g63':['*','Delta','c2'],'g64':['+',1,'g63'],
 'g65':['*','g62','g64'],'A1':['-','g61','g65'],'F0':['+',1,'A0'],
 'F1':['+',1,'A1'],'Fs':['+',1,'g72'],'P01':['*','F0','F1'],
 'P012':['*','P01','Fa'],'P0123':['*','P012','Fs'],'out':['-','P0123',1]}
for n,row in shape.items():assert b[n]==row,n
# Exact multivariate polynomial identities underpinning the square gaps and
# Pell transformation. Signs/inequalities are justified in the review prose.
def cn(n):return {():n} if n else {}
def v(n):return {(n,):1}
def add(a,b):
 z=dict(a)
 for m,w in b.items():z[m]=z.get(m,0)+w
 return {m:w for m,w in z.items() if w}
def neg(a):return {m:-w for m,w in a.items()}
def sub(a,b):return add(a,neg(b))
def mul(a,b):
 z={}
 for i,x in a.items():
  for j,y in b.items():
   m=tuple(sorted(i+j));z[m]=z.get(m,0)+x*y
 return {m:w for m,w in z.items() if w}
def sq(a):return mul(a,a)
a,c0,m,k,t=map(v,('a','c','m','k','t')); ap2=add(a,cn(2));delta=sub(sq(ap2),cn(1))
N=add(cn(1),mul(delta,sq(c0)));ac=mul(ap2,c0)
assert sub(sq(ac),N)==sub(sq(c0),cn(1))
assert sub(N,sq(sub(ac,cn(1))))==mul(c0,sub(mul(cn(2),ap2),c0))
assert sub(N,sq(mul(add(a,cn(1)),c0)))==add(mul(add(mul(cn(2),a),cn(2)),sq(c0)),cn(1))
DD=mul(m,add(m,cn(1)));hh=add(mul(cn(2),m),cn(1))
t1=sub(mul(hh,t),mul(mul(cn(2),DD),k));k1=sub(mul(hh,k),mul(cn(2),t))
assert sub(sq(hh),mul(cn(4),DD))==cn(1)
assert sub(sq(t1),mul(DD,sq(k1)))==sub(sq(t),mul(DD,sq(k)))
# Finite modular sanity for the four old unit exclusions; the general proof is
# inherited from the reviewed all-integer parent and is not inferred from samples.
for q0 in range(2,8):
 for w in range(1,4):
  for ss in range(1,4):
   X=q0*w;Y=q0**3*ss;mm=X*Y*Y;kk=8*mm+4;RR=q0**4-q0**3-q0-1
   aa=X*Y+Y;cc=1+Y*kk;H=3+4*aa;U=Y*q0*q0
   assert mm>=q0**7 and kk>q0**4>RR+1 and cc>X
   assert Y*Y*q0*q0*aa>H and U*(X+aa*cc)+H*(RR+1-kk)>0
# Authenticated ports and an independent 99th finite difference for degree.
root='con-zfc-diophantine-forms/72-congruence-sextic/positive13/'
x=json.loads(pin(root+'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'))
y=json.loads(pin('con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'))
ports={}
for n,meta in x['ports'].items():
 assert all(meta[z]==y['ports'][n][z] for z in ('sha256_gzip','sha256_raw','raw_bytes','bits'))
 packed=(D/root/meta['path']).read_bytes();raw=zlib.decompress(packed,31)
 assert sha(packed)==meta['sha256_gzip'] and sha(raw)==meta['sha256_raw'] and len(raw)==meta['raw_bytes']
 ports[n]=int.from_bytes(raw,'little');assert ports[n].bit_length()==meta['bits']
assert ports['beta']>=46 and ports['K0']>=0 and 0<ports['MC']<ports['beta'] and 0<ports['MF']<2*ports['beta']
prime=1000000007
def ev(t):
 e={n:t for n in c['witnesses']};e.update({n:v%prime for n,v in ports.items()})
 def val(x):return x if type(x) is int else e[x]
 for n,op,x,y in c['source']:
  x,y=val(x),val(y);e[n]=(x+y if op=='+' else x-y if op=='-' else x*y)%prime
 return e['out']
row=[ev(i) for i in range(100)]
for _ in range(99):row=[(b-a)%prime for a,b in zip(row,row[1:])]
lead=row[0]*pow(math.factorial(99),-1,prime)%prime
assert lead==663418019
print(json.dumps({'scope':'source rank assumptions, graph, algebraic identities and degree; unbounded descent/rank theorem inherited, no Lean',
 'inputs':13,'parent_gates':88,'candidate_gates':87,'all_gates_inputs_ports_live':True,
 'pell_transform_and_main_square_gaps_checked':True,'rank_source_hypotheses_checked':True,
 'port_bounds_checked':True,'degree_upper_inherited':99,'ray_method':'99th finite difference',
 'ray_prime':prime,'ray_leader':lead},sort_keys=True,indent=2))
