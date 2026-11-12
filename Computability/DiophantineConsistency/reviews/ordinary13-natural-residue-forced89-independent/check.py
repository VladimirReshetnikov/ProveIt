#!/usr/bin/env python3
"""Independent mixed-shift, forcing algebra and compact degree review."""
from pathlib import Path
import collections,gzip,hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b
p=json.loads(pin('research/ordinary13-residue-first82/candidate.json','bb90faa3815c5ff46f5fdbf41c2d001790d565baa17d97c79514c33fa928f1d2'))
c=json.loads(pin('research/ordinary13-natural-residue-forced89-degree56/candidate.json','c18892fc5e50e091411cf24511481995ad2fdbab20e55068787722feca41a22a'))
pin('research/ordinary13-natural-residue-forced89-degree56/receipt.json','beb633428beee90b6049162d9e77ae063755dcdf2c63a07283a97a2bcb12e123')
pin('reviews/ordinary13-residue-first82-independent/result.json','75224f3e6b7811271bfa0cf343862ed09b80a9634e155521808de856a10c1a40')
sq=pin('Lean/DiophantineConsistency/ArithmeticSquareDivisibility.lean','f775c2050a794b1ea026cdec0950e42528260fa1d75a03f1ef625f258670e660').decode()
dr=pin('Lean/DiophantineConsistency/ModelDifferenceRing.lean','5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998').decode()
ref=pin('Lean/DiophantineConsistency/BFS943/Trace75IntegralTransport.lean','4d764b377ae95cc13b4548ab63266cb97084a061c8c14dd9d8922ac88cbc6885').decode()
assert 'theorem dvd_of_square_dvd (m z : V) (hm : 0<m) (h : m*m ∣ z*z) : m∣z' in sq
assert 'theorem nonneg_iff {x : DiffRing V} : 0 ≤ x ↔ ∃ a, x = ι a' in dr
assert 'theorem natural_dvd_of_signed (a b : V) (hd : (ι a : DiffRing V)∣ι b) : a∣b' in ref
forced={'J','X','f','y','gamma','r'};ren={x:'n_'+x for x in p['witnesses']};rep=lambda x:('shift_'+x if x in ren and x not in forced else ren.get(x,x)) if isinstance(x,str) else x
assert len(p['source'])==82 and len(c['source'])==89 and len(c['witnesses'])==13 and c['domain']=='nonnegative integers'
assert c['forced_unshifted']==sorted(forced) and c['witnesses']==list(ren.values())
assert c['source']==[['shift_'+x,'+',ren[x],1] for x in p['witnesses'] if x not in forced]+[[n,op,rep(x),rep(y)] for n,op,x,y in p['source']]
assert c['fixed_numerals']==p['fixed_numerals'] and c['output']==p['output']
rows={x[0]:x for x in p['source']}; known=set(c['witnesses']+c['fixed_numerals']);children={}
for name,op,x,y in c['source']:
 assert name not in known and op in '+-*' and all(type(a) is int or a in known for a in (x,y));children[name]=(x,y);known.add(name)
live={c['output']};todo=[c['output']]
while todo:
 for x in children.get(todo.pop(),()):
  if isinstance(x,str) and x not in live:live.add(x);todo.append(x)
assert set(children)|set(c['witnesses'])|set(c['fixed_numerals'])<=live
# Independent direct graph wiring for all four zero-forcing branches.
for row in [['qm','*','J','beta'],['q','+',1,'qm'],['q3','*','q','q2'],['Y','*','q3','s'],['qF','-','q','F'],['C','-','qF','alpha'],['g26','+','X','K0'],['g27','*','C','g26'],['Bt','-','g27','F'],['g32','*','qm','folded_g31'],['Z','-','g32','Bt'],['g38','*','Z','Z'],['g39','*','qm','qm'],['A0','-','g38','g42'],['U','*','Y','q2'],['H','+',3,'g15'],['a','+','E','Y'],['Delta','+','H','g17'],['g58','*','U','b0'],['g59','*','H','shift'],['Dstar','+','g58','g59'],['g61','*','Dstar','Dstar'],['g62','*','U','U'],['g63','*','Delta','c2'],['g64','+',1,'g63'],['g65','*','g62','g64'],['A1','-','g61','g65'],['g19','*','a','c'],['b0','+','X','g19'],['g17','*','a','a'],['f2','*','f','f'],['rho','-','f2',1],['Q','*','Delta','rho'],['I','*','c2','i'],['g71','*','I','I'],['g72','-','g71','Q'],['y2','*','y','y'],['V2','*','V','V'],['g81','-','y2','V2'],['g82','*','Q','g81'],['Fa','-','y2','g82'],['Fam','-','Fa',1],['A0sq','*','A0','A0'],['A1sq','*','A1','A1'],['Fam2','*','Fam','Fam'],['Fsm2','*','g72','g72'],['sum01','+','A0sq','A1sq'],['sum23','+','Fam2','Fsm2'],['out','+','sum01','sum23']]:assert rows[row[0]]==row,row
# Exact residue-adjusted carrier, rank expression and gamma branch wiring.
for row in [['g30','+','ell','k'],['g31','+','g30','r'],['folded_kBt','*','k','Bt'],['folded_g31','-','g31','folded_kBt'],['g44','*','qF','qm'],['G','+','alpha','g44'],['g46','-','q2',1],['g47','*','G','g46'],['g48','*','MF','q'],['g49','+','MC','g48'],['g50','*','J','g49'],['R','+','g47','g50'],['g52','-','k','R'],['r0','-','g52',1],['g54','*','U','gamma'],['g55','*','E','q'],['g56','+','g54','g55'],['shift','-','g56','r0']]:assert rows[row[0]]==row,row
rank=pin('Lean/DiophantineConsistency/ArithmeticAdaptiveRankWindow2011.lean','0895f6e74b29c2cc2e4542d739b238352778750da62766819caeb105995fb794').decode()
assert 'theorem scalar_rank_window (q beta MC MF J F alpha : V)' in rank and '(hgap : F+alpha<q)' in rank and 'hMC : MC<beta' in rank and 'hMF : MF<2*beta' in rank
pin('reviews/ordinary13-natural-residue-forced90-independent/result.json','d4cfc1fa4f40cbd6e308814640151b2c954d99487889fe2c91733bd05b8bf97c')
pin('reviews/ordinary13-natural-residue-forced91-independent/result.json','d874913d91544bbaa6a6259601005388dc1c9a5c438767f7d475c18e46cb0fcb')
pin('reviews/ordinary13-folded-root86-negated-positive-bt-independent/README.md','8f324ee252dd58745df93200d0e6ff0733d7eb625dbadaf24a45dd6525d0e0d4')
# Check H-divisibility cancellation with arbitrary signed quotient d.
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
U,A,C,X,H,S,dd=map(atom,['U','a','c','X','H','S','d']);one={():1};ac=mul(A,C);z=add(dd,ac,-1)
norm=add(add(mul(dd,dd),one,-1),mul(add(mul(A,A),H),mul(C,C)),-1)
prod=add(mul(U,z),mul(H,S),-1)
identity=add(add(mul(H,add(mul(S,add(dd,ac)),mul(U,mul(C,C)),-1)),mul(U,norm),-1),mul(prod,add(dd,ac)))
assert identity==U
# Inverse Pell descent preserves norm exactly for symbolic m,k,tau.
m,k,tau=map(atom,['m','k','tau']);dP=mul(m,add(m,one));pellA=add(mul({():2},m),one)
taup=add(mul(pellA,tau),mul({():2},mul(dP,k)),-1)
kp=add(mul(pellA,k),mul({():2},tau),-1)
assert add(mul(taup,taup),mul(dP,mul(kp,kp)),-1)==add(mul(tau,tau),mul(dP,mul(k,k)),-1)
# The k=2 consecutive-square gap and main norm comparison are exact.
a2=add(A,{():2});cm=add(mul(a2,C),one,-1)
mid=add(one,mul(add(mul(a2,a2),one,-1),mul(C,C)))
assert add(mid,mul(cm,cm),-1)==mul(C,add(mul({():2},a2),C,-1))
assert add(mid,mul(add(mul(a2,C),{}),add(mul(a2,C),{})),-1)==add(one,mul(C,C),-1)
# A1 cancellation supplies the degree upper bound.
b0=add(X,ac);dst=add(mul(U,b0),mul(H,S));delta=add(mul(A,A),H)
lhs=add(mul(dst,dst),mul(mul(U,U),add(one,mul(delta,mul(C,C)))),-1)
inner=add(add(add(mul({():2},mul(X,ac)),mul(X,X)),one,-1),mul(H,mul(C,C)),-1)
rhs=add(add(mul(mul(U,U),inner),mul({():2},mul(mul(mul(U,b0),H),S))),mul(mul(H,H),mul(S,S)))
assert lhs==rhs
d={x:1 for x in c['witnesses']};d.update({x:0 for x in c['fixed_numerals']})
for n,op,x,y in c['source']:
 dx=0 if type(x) is int else d[x];dy=0 if type(y) is int else d[y];d[n]=dx+dy if op=='*' else max(dx,dy)
bound=max(2*d['U']+d['n_X']+d['a']+d['c'],2*d['U']+2*d['n_X'],2*d['U'],2*d['U']+d['H']+2*d['c'],d['U']+d['b0']+d['H']+d['shift'],2*d['H']+2*d['shift'])
assert bound==28 and max(d['A0'],d['Fam'],d['g72'],bound)==28
root=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
binding=json.loads(pin('con-zfc-diophantine-forms/72-congruence-sextic/positive13/ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'))
b115=json.loads(pin('con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'))
fixed={}
for n,item in binding['ports'].items():
 assert b115['ports'][n]['sha256_raw']==item['sha256_raw'] and b115['ports'][n]['sha256_gzip']==item['sha256_gzip']
 raw=gzip.decompress(pin(str(root.relative_to(D)/item['path']),item['sha256_gzip']));assert len(raw)==item['raw_bytes'] and hashlib.sha256(raw).hexdigest()==item['sha256_raw']
 fixed[n]=int.from_bytes(raw,'little')
assert set(fixed)==set(c['fixed_numerals']) and fixed['beta']>=46 and fixed['K0']>=0
assert fixed['K0']+1 <= (fixed['beta']+1)**2
# Independently exercise the corrected order argument; this finite check is not its proof.
for m0 in range(2,31):
 for p0 in range(1,m0):
  for t0 in range(1,p0+1):
   for k0 in range(2,11):
    ell0=m0*k0
    assert k0*(p0-1)<ell0 and t0<m0<=ell0
    assert k0*(p0-1)+t0<2*ell0
assert 2*(99-1)+99 > 2*99  # the earlier stronger inequality is false
prime=1000000009
def trim(x):
 while len(x)>1 and not x[-1]:x.pop()
 return x
def ap(x,y,k=1):return trim([((x[i] if i<len(x) else 0)+k*(y[i] if i<len(y) else 0))%prime for i in range(max(len(x),len(y)))])
def mp(x,y):
 d=[0]*(len(x)+len(y)-1)
 for i,a in enumerate(x):
  for j,b in enumerate(y):d[i+j]=(d[i+j]+a*b)%prime
 return trim(d)
e={x:[0,1] for x in c['witnesses']};e.update({x:[v%prime] for x,v in fixed.items()})
for name,op,x,y in c['source']:
 x=e[x] if type(x) is str else [x%prime];y=e[y] if type(y) is str else [y%prime]
 e[name]=mp(x,y) if op=='*' else ap(x,y,-1 if op=='-' else 1)
assert len(e[c['output']])-1==56 and e[c['output']][-1]!=0
print(json.dumps({'scope':'exact mixed-shift, signed divisibility algebra and fixed-compact-port degree; no Lean','variables':13,'natural_operations':89,'forced_unshifted':sorted(forced),'degree_for_authenticated_compact_ports':56,'different_ray_prime':prime,'ray_leading_coefficient':e[c['output']][-1],'beta_and_K0_representation_required':True,'signed_magnitude_and_divisibility_sources_pinned':True,'parent_arbitrary_model_calibration_not_established':True,'gamma_forcing_standard_integer_only':True,'compact_K_plus_one_at_most_q_squared':True,'corrected_r_bound_finite_controls':True,'rank_window_and_pell_descent_sources_pinned':True},sort_keys=True,indent=2))
