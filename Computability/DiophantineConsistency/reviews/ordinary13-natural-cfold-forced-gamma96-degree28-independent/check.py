#!/usr/bin/env python3
"""Independent C-fold gamma graph and degree checks; no Lean."""
from pathlib import Path
import hashlib,itertools,json,math,zlib
D=Path(__file__).resolve().parents[2]
CANDIDATE='ordinary13-natural-cfold-forced-gamma96-degree28';PARENT='ordinary13-natural-cfold97-degree28';CANDIDATE_SHA='f23a4f8b5b7761cd2226f71235f34dfa9cf362f5567b10589a1859106a00be81';PARENT_SHA='8c56deec58c4fbe29ab024fc5a61628ec0d677858c9bc6eb066b4f81244ee2e6'
GATES=96;DEGREE=28;LEADER=59132194;PRODUCT=False
def sha(x):return hashlib.sha256(x).hexdigest()
def load(path,digest):
 data=(D/path).read_bytes();assert sha(data)==digest,path;return json.loads(data)
p=load('research/'+PARENT+'/candidate.json',PARENT_SHA);c=load('research/'+CANDIDATE+'/candidate.json',CANDIDATE_SHA)
assert p['domain']==c['domain']=='nonnegative integers' and p['witnesses']==c['witnesses'] and len(c['witnesses'])==13
assert p['fixed_numerals']==c['fixed_numerals']==['beta','K0','MC','MF']
a={r[0]:r[1:] for r in p['source']};b={r[0]:r[1:] for r in c['source']}
assert len(a)==GATES+1 and len(b)==GATES and set(a)-set(b)=={'gamma'} and set(b)<=set(a)
assert a['gamma']==['+','n_gamma',1]
for n,row in b.items():
 op,x,y=a[n];assert row==[op,'n_gamma' if x=='gamma' else x,'n_gamma' if y=='gamma' else y]
seen=set(c['witnesses']+c['fixed_numerals']);assert len(seen)==17
for n,op,x,y in c['source']:
 assert n not in seen and op in ('+','-','*') and all(type(v) is int or v in seen for v in (x,y));seen.add(n)
live={'out'}
for n,op,x,y in reversed(c['source']):
 if n in live:live.update(v for v in (x,y) if isinstance(v,str))
assert set(b)|set(c['witnesses'])|set(c['fixed_numerals'])<=live
shape={'F':['+','n_F',1],'alpha':['+','n_alpha',1],'X':['+','n_X',1],'Y':['+','n_Y',1],
 'eta':['+','n_eta',1],'qm':['*','n_J','beta'],'q':['+',1,'qm'],
 'q2':['*','q','q'],'q3':['*','q','q2'],'M':['*','q3','qm'],'U':['*','Y','q2'],
 'qF':['-','q','F'],'C':['-','qF','alpha'],'E':['*','X','Y'],
 'kbase':['+','eta','n_zeta'],'k':['+','kbase',1],'kY':['*','Y','k'],
 'c':['+','eta','kY'],'c2':['*','c','c'],'a':['+','E','Y'],'g15':['*',4,'a'],
 'H':['+',3,'g15'],'g17':['*','a','a'],'Delta':['+','H','g17'],'g19':['*','a','c'],
 'b0':['+','X','g19'],'ell':['*','E','kY'],'g25':['*','K0','q'],
 'g26':['+','X','g25'],'g27':['*','C','g26'],'g28':['*','F','q'],'Bt':['-','g27','g28'],
 'g30':['+','ell','k'],'g31':['+','g30','n_r'],'folded_kBt':['*','k','C'],
 'folded_g31':['-','g31','folded_kBt'],'g32':['*','M','folded_g31'],'g33':['*','Y','qm'],
 'g34':['+','g32','g33'],'folded_q3Bt':['*','q3','Bt'],'Z':['-','g34','folded_q3Bt'],
 'g38':['*','Z','Z'],'g39':['*','M','M'],'g40':['*','ell','g30'],'g41':['+',1,'g40'],
 'g42':['*','g39','g41'],'A0':['-','g38','g42'],'g44':['*','qF','qm'],
 'G':['+','alpha','g44'],'g46':['-','q2',1],'g47':['*','G','g46'],
 'g48':['*','MF','q'],'g49':['+','MC','g48'],'g50':['*','n_J','g49'],
 'R':['+','g47','g50'],'r0':['-','kbase','R'],'g54':['*','U','n_gamma'],
 'g55':['*','E','q'],'g56':['+','g54','g55'],'shift':['-','g56','r0'],
 'g58':['*','U','b0'],'g59':['*','H','shift'],'Dstar':['+','g58','g59'],
 'g61':['*','Dstar','Dstar'],'g62':['*','U','U'],'g63':['*','Delta','c2'],
 'g64':['+',1,'g63'],'g65':['*','g62','g64'],'A1':['-','g61','g65'],
 'i':['+','n_i',1],'f2':['*','n_f','n_f'],'rho':['-','f2',1],
 'Q':['*','Delta','rho'],'I':['*','c2','i'],'g71':['*','I','I'],'g72':['-','g71','Q'],
 'g78':['+','V','u'],'y2':['*','g78','g78'],'g80':['+','g78','V'],
 'g81':['*','u','g80'],'g82':['*','Q','g81'],'Fa':['-','y2','g82']}
if PRODUCT:
 shape.update({'F0':['+',1,'A0'],'F1':['+',1,'A1'],'Fs':['+',1,'g72'],
 'P01':['*','F0','F1'],'P012':['*','P01','Fa'],'P0123':['*','P012','Fs'],'out':['-','P0123',1]})
 # Verify the product candidate's entire shared graph against the independently
 # reviewed gamma-zero sum-of-squares candidate, not just named residuals.
 sq=load('research/ordinary13-natural-cfold-forced-gamma96-degree28/candidate.json','f23a4f8b5b7761cd2226f71235f34dfa9cf362f5567b10589a1859106a00be81')
 old={r[0]:r[1:] for r in sq['source']}
 removed={'A0sq','A1sq','Fam','Fam2','Fsm2','sum01','sum23','out'}
 added={'F0','F1','Fs','P01','P012','P0123','out'}
 assert set(old)-removed==set(b)-added and all(old[n]==b[n] for n in set(old)-removed)
 for bb,z,h in itertools.product(range(4),repeat=3):
  M=((bb+1)**3*bb)%4;assert M%2==0 and (1+z*z-M*M*(1+h))%4 in (0,1,2)
 for aa,cc,U,d in itertools.product(range(4),repeat=4):
  delta=(aa*aa+4*aa+3)%4;assert (1+d*d-U*U*(1+delta*cc*cc))%4 in (0,1,2)
 for aa,f,V,u,I in itertools.product(range(4),repeat=5):
  Q=((aa*aa+4*aa+3)*(f*f-1))%4;y0=V+u
  assert Q in (0,1) and (y0*y0-Q*u*(u+2*V))%4 in (0,1) and (1+I*I-Q)%4 in (0,1,2)
else:
 shape.update({'A0sq':['*','A0','A0'],'A1sq':['*','A1','A1'],'Fam':['-','Fa',1],
 'Fam2':['*','Fam','Fam'],'Fsm2':['*','g72','g72'],'sum01':['+','A0sq','A1sq'],
 'sum23':['+','Fam2','Fsm2'],'out':['+','sum01','sum23']})
for n,row in shape.items():assert b[n]==row,n
rankpath='Lean/DiophantineConsistency/ArithmeticAdaptiveRankWindow2011.lean';raw=(D/rankpath).read_bytes();assert sha(raw)=='0895f6e74b29c2cc2e4542d739b238352778750da62766819caeb105995fb794'
rank=raw.decode()
for fragment in ('(hbeta : 0<beta) (hJ : 0<J) (hF : 0<F) (halpha : 0<alpha)',
 '(hMC : MC<beta) (hMF : MF<2*beta) (hq : q=beta*J+1)', '(hgap : F+alpha<q)', ')+q^3+q+1≤q^4'):
 assert fragment in rank
# Sparse-polynomial square-gap and Pell-transform identities.
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
a,c0,m,k,t=map(v,('a','c','m','k','t'));ap2=add(a,cn(2));delta=sub(sq(ap2),cn(1));N=add(cn(1),mul(delta,sq(c0)));ac=mul(ap2,c0)
assert sub(sq(ac),N)==sub(sq(c0),cn(1))
assert sub(N,sq(sub(ac,cn(1))))==mul(c0,sub(mul(cn(2),ap2),c0))
assert sub(N,sq(mul(add(a,cn(1)),c0)))==add(mul(add(mul(cn(2),a),cn(2)),sq(c0)),cn(1))
DD=mul(m,add(m,cn(1)));hh=add(mul(cn(2),m),cn(1));t1=sub(mul(hh,t),mul(mul(cn(2),DD),k));k1=sub(mul(hh,k),mul(cn(2),t))
assert sub(sq(hh),mul(cn(4),DD))==cn(1) and sub(sq(t1),mul(DD,sq(k1)))==sub(sq(t),mul(DD,sq(k)))
# Y divisibility and orientation inequalities remain unbounded arguments;
# these small controls are supplementary checks only.
for q in range(2,8):
 for X in range(1,4):
  for ss in range(1,4):
   Y=q**3*ss;mm=X*Y*Y;kk=8*mm+4;R=q**4-q**3-q-1;E=X*Y
   aa=X*Y+Y;cc=1+Y*kk;H=3+4*aa;U=Y*q*q
   assert kk-E*q>=X*Y*(8*Y-q)+4>q**4>R+1 and cc>X
   assert Y*Y*q*q*aa>H and U*(X+aa*cc)+H*(E*q+R+1-kk)>0
root='con-zfc-diophantine-forms/72-congruence-sextic/positive13/'
x=load(root+'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf')
y=load('con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01')
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
row=[ev(i) for i in range(DEGREE+1)]
for _ in range(DEGREE):row=[(b-a)%prime for a,b in zip(row,row[1:])]
lead=row[0]*pow(math.factorial(DEGREE),-1,prime)%prime
assert lead==LEADER
print(json.dumps({'scope':'external C-fold gamma graph and algebra; rank and unbounded descent inherited, no Lean',
 'inputs':13,'parent_gates':GATES+1,'candidate_gates':GATES,'degree_upper_inherited':DEGREE,
 'E_q_main_term_checked':True,'rank_source_hypotheses_checked':True,'pell_and_square_identities_checked':True,
 'unit_finalizer_controls':PRODUCT,'actual_port_bounds_checked':True,
 'ray_method':str(DEGREE)+'th finite difference','ray_prime':prime,'ray_leader':lead},sort_keys=True,indent=2))
