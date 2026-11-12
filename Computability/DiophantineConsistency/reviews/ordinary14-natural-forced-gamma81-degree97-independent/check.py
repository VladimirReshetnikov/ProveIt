#!/usr/bin/env python3
"""Independent gamma edit, factor shapes and degree ray; no Lean."""
from pathlib import Path
import hashlib,itertools,json,math,zlib
D=Path(__file__).resolve().parents[2]
CANDIDATE='ordinary14-natural-forced-gamma81-degree97';PARENT='ordinary14-natural-forcedj82-degree97';CANDIDATE_SHA='cc67ddaf73f571a51ae9132c5584d48b353fb9b90a64b5ff0599459bf84ef94c';PARENT_SHA='7d4ba963bda9c7acd7eb80fd96cd289809960e6c9de6e919f461ebd14ecea76f'
GATES=81;DEGREE=97;LEADER=979034495;RAY_COORD='n_t'
def sha(x):return hashlib.sha256(x).hexdigest()
def load(path,digest):
 data=(D/path).read_bytes();assert sha(data)==digest,path;return json.loads(data)
p=load('research/'+PARENT+'/candidate.json',PARENT_SHA);c=load('research/'+CANDIDATE+'/candidate.json',CANDIDATE_SHA)
assert p['domain']==c['domain']=='nonnegative integers' and p['witnesses']==c['witnesses'] and len(c['witnesses'])==14
assert p['fixed_numerals']==c['fixed_numerals']==['beta','K0','MC','MF']
a={r[0]:r[1:] for r in p['source']};b={r[0]:r[1:] for r in c['source']}
assert len(a)==GATES+1 and len(b)==GATES and set(a)-set(b)=={'gamma'} and set(b)<=set(a)
assert a['gamma']==['+','n_gamma',1]
for n,row in b.items():
 op,x,y=a[n];assert row==[op,'n_gamma' if x=='gamma' else x,'n_gamma' if y=='gamma' else y]
seen=set(c['witnesses']+c['fixed_numerals']);assert len(seen)==18
for n,op,x,y in c['source']:
 assert n not in seen and op in ('+','-','*') and all(type(v) is int or v in seen for v in (x,y));seen.add(n)
live={'out'}
for n,op,x,y in reversed(c['source']):
 if n in live:live.update(v for v in (x,y) if isinstance(v,str))
assert set(b)|set(c['witnesses'])|set(c['fixed_numerals'])<=live
shape={'alpha':['+','n_alpha',1],'w':['+','n_w',1],'s':['+','n_s',1],
 'eta':['+','n_eta',1],'qm':['*','n_J','beta'],'q':['+',1,'qm'],'X':['*','q','w'],
 'q2':['*','q','q'],'q3':['*','q','q2'],'Y':['*','q3','s'],'U':['*','Y','q2'],
 'qF':['-','qm','n_F'],'C':['-','qF','alpha'],'g26':['+','X','K0'],'g27':['*','C','g26'],
 'guard_base':['-','g27','n_F'],'bt_quotient':['*','qm','n_h'],'guard':['-','guard_base','bt_quotient'],
 'E':['*','X','Y'],'kbase':['+','eta','n_zeta'],'k':['+','kbase',1],
 'kY':['*','Y','k'],'c':['+','eta','kY'],'c2':['*','c','c'],'a':['+','E','Y'],
 'g15':['*',4,'a'],'H':['+',3,'g15'],'g17':['*','a','a'],'Delta':['+','H','g17'],
 'g19':['*','a','c'],'b0':['+','X','g19'],'ell':['*','E','kY'],
 'g44':['*','qF','qm'],'G':['+','alpha','g44'],'g46':['-','q2',1],
 'g47':['*','G','g46'],'g48':['*','MF','q'],'g49':['+','MC','g48'],
 'g50':['*','n_J','g49'],'R':['+','g47','g50'],'r0':['-','kbase','R'],
 'g54':['*','U','n_gamma'],'shift':['-','g54','r0'],'g58':['*','U','b0'],
 'g59':['*','H','shift'],'Dstar':['+','g58','g59'],'g61':['*','Dstar','Dstar'],
 'g62':['*','U','U'],'g63':['*','Delta','c2'],'g64':['+',1,'g63'],
 'g65':['*','g62','g64'],'A1':['-','g61','g65'],'F1':['+',1,'A1'],
 'f2':['*','n_f','n_f'],'rho':['-','f2',1],'Q':['*','Delta','rho'],
 'I':['*','c2','i'],'g71':['*','I','I'],'g72':['-','g71','Q'],'Fs':['+',1,'g72'],
 'y2':['*','n_y','n_y'],'V2':['*','V','V'],'g81':['-','y2','V2'],
 'g82':['*','Q','g81'],'Fa':['-','y2','g82'],
 'P01':['*','F0','F1'],'P012':['*','P01','Fa'],'P0123':['*','P012','Fs'],
 'P01234':['*','P0123','guard'],'out':['-','P01234',1]}
if RAY_COORD is None:
 shape.update({'g30':['+','ell','k'],'g38':['*','n_r','n_r'],'g40':['*','ell','g30'],'F0':['-','g38','g40']})
else:
 shape.update({'t2':['*','n_t','n_t'],'twot':['*',2,'n_t'],'twot_minus_k':['-','twot','k'],
 'ell_times':['*','ell','twot_minus_k'],'F0':['+','t2','ell_times']})
for n,row in shape.items():assert b[n]==row,n
rankpath='Lean/DiophantineConsistency/ArithmeticAdaptiveRankWindow2011.lean'
raw=(D/rankpath).read_bytes();assert sha(raw)=='0895f6e74b29c2cc2e4542d739b238352778750da62766819caeb105995fb794'
rank=raw.decode()
for fragment in ('(hbeta : 0<beta) (hJ : 0<J) (hF : 0<F) (halpha : 0<alpha)',
 '(hMC : MC<beta) (hMF : MF<2*beta) (hq : q=beta*J+1)', '(hgap : F+alpha<q)', ')+q^3+q+1≤q^4'):
 assert fragment in rank
# Algebraic identities over an abstract commutative ring, checked exactly as
# sparse polynomials. This includes shifted-root equivalence and descent.
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
a,c0,m,k,t,ell=map(v,('a','c','m','k','t','ell'));ap2=add(a,cn(2));delta=sub(sq(ap2),cn(1));N=add(cn(1),mul(delta,sq(c0)));ac=mul(ap2,c0)
assert sub(sq(ac),N)==sub(sq(c0),cn(1))
assert sub(N,sq(sub(ac,cn(1))))==mul(c0,sub(mul(cn(2),ap2),c0))
assert sub(N,sq(mul(add(a,cn(1)),c0)))==add(mul(add(mul(cn(2),a),cn(2)),sq(c0)),cn(1))
assert add(sq(t),mul(ell,sub(mul(cn(2),t),k)))==sub(sq(add(ell,t)),mul(ell,add(ell,k)))
DD=mul(m,add(m,cn(1)));hh=add(mul(cn(2),m),cn(1));t1=sub(mul(hh,t),mul(mul(cn(2),DD),k));k1=sub(mul(hh,k),mul(cn(2),t))
assert sub(sq(hh),mul(cn(4),DD))==cn(1)
assert sub(sq(t1),mul(DD,sq(k1)))==sub(sq(t),mul(DD,sq(k)))
# Factor residue controls remain finite; the unbounded negative-Pell exclusion
# and sign argument are inherited from separately reviewed mathematics.
for aa,cc,U,d in itertools.product(range(4),repeat=4):
 delta=(aa*aa+4*aa+3)%4
 assert (1+d*d-U*U*(1+delta*cc*cc))%4 in (0,1,2)
for aa,f,y,V,I in itertools.product(range(4),repeat=5):
 Q=((aa*aa+4*aa+3)*(f*f-1))%4
 assert Q in (0,1) and (y*y-Q*(y*y-V*V))%4 in (0,1) and (1+I*I-Q)%4 in (0,1,2)
root='con-zfc-diophantine-forms/72-congruence-sextic/positive13/'
x=load(root+'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf')
y=load('con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01')
ports={}
for n,meta in x['ports'].items():
 assert all(meta[z]==y['ports'][n][z] for z in ('sha256_gzip','sha256_raw','raw_bytes','bits'))
 packed=(D/root/meta['path']).read_bytes();raw=zlib.decompress(packed,31)
 assert sha(packed)==meta['sha256_gzip'] and sha(raw)==meta['sha256_raw'] and len(raw)==meta['raw_bytes']
 ports[n]=int.from_bytes(raw,'little');assert ports[n].bit_length()==meta['bits']
assert ports['beta']>=46 and ports['K0']>0 and 0<ports['MC']<ports['beta'] and 0<ports['MF']<2*ports['beta']
prime=1000000007
def ev(t):
 e={n:t for n in c['witnesses']};e.update({n:v%prime for n,v in ports.items()})
 if RAY_COORD:e[RAY_COORD]=2*t
 def val(x):return x if type(x) is int else e[x]
 for n,op,x,y in c['source']:
  x,y=val(x),val(y);e[n]=(x+y if op=='+' else x-y if op=='-' else x*y)%prime
 return e['out']
row=[ev(i) for i in range(DEGREE+1)]
for _ in range(DEGREE):row=[(b-a)%prime for a,b in zip(row,row[1:])]
lead=row[0]*pow(math.factorial(DEGREE),-1,prime)%prime
assert lead==LEADER
print(json.dumps({'scope':'external gamma graph and arithmetic identities; rank and unbounded Pell exclusions inherited, no Lean',
 'inputs':14,'parent_gates':GATES+1,'candidate_gates':GATES,'degree_upper_inherited':DEGREE,
 'rank_source_hypotheses_checked':True,'pell_and_square_identities_checked':True,
 'first_factor_shift_checked':RAY_COORD is not None,'actual_port_bounds_checked':True,
 'ray_method':str(DEGREE)+'th finite difference','ray_prime':prime,'ray_leader':lead},sort_keys=True,indent=2))
