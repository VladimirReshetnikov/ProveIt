#!/usr/bin/env python3
"""Pin the exact quotient graph, generic norm identities and compact-port degree."""
from pathlib import Path
from collections import Counter
import gzip,hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
def digest(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert digest(b)==h,(p,digest(b));return b
pr=pin(D/'research/ordinary13-residue-first81/candidate.json','067d3cf0e92961d272e9018dde38bbe8b00ad55ec8e9145fbdd34c0f13e18352');p=json.loads(pr)
c=json.loads(pin(P/'candidate.json','cb488cb849c08c11d159f8805fdd7664c6472cbd41cefadc530e21060a5a1dd2'))
forced={'J','f','y','w','gamma','r'};ren={x:'n_'+x for x in p['witnesses']};shift={x:'shift_'+x for x in p['witnesses'] if x not in forced};rep=lambda x:shift.get(x,ren.get(x,x)) if isinstance(x,str) else x
assert c['positive_parent_sha256']==digest(pr) and c['domain']=='nonnegative integers' and c['forced_unshifted']==sorted(forced)
assert c['witnesses']==list(ren.values()) and c['fixed_numerals']==p['fixed_numerals'] and c['output']==p['output']
expect=[['shift_'+x,'+',ren[x],1] for x in p['witnesses'] if x not in forced]+[[n,o,rep(a),rep(b)] for n,o,a,b in p['source']]
assert c['source']==expect and c['operations']==len(expect)==88
def live(g):
 known=set(g['witnesses']+g['fixed_numerals']);nodes={}
 for n,o,a,b in g['source']:
  assert n not in known and o in ('+','-','*') and all(type(x) is int or x in known for x in (a,b)),(n,o,a,b)
  known.add(n);nodes[n]=(a,b)
 seen={g['output']};todo=[g['output']]
 while todo:
  for x in nodes.get(todo.pop(),()):
   if isinstance(x,str) and x not in seen:seen.add(x);todo.append(x)
 assert set(nodes)|set(g['witnesses'])|set(g['fixed_numerals'])<=seen
 return dict(sorted(Counter(x[1] for x in g['source']).items()))
counts=live(c);live(p)
sq=pin(D/'Lean/DiophantineConsistency/ArithmeticSquareDivisibility.lean','f775c2050a794b1ea026cdec0950e42528260fa1d75a03f1ef625f258670e660').decode()
assert 'theorem dvd_of_square_dvd (m z : V) (hm : 0<m) (h : m*m ∣ z*z) : m∣z' in sq
rp={r[0]:r for r in p['source']}
for row in [['qm','*','J','beta'],['q','+',1,'qm'],['q3','*','q','q2'],['X','*','q','w'],['Y','*','q3','s'],['qF','-','q','F'],['C','-','qF','alpha'],['g26','+','X','K0'],['g27','*','C','g26'],['Bt','-','g27','F'],['g30','+','ell','k'],['g31','+','g30','r'],['folded_kBt','*','k','Bt'],['folded_g31','-','g31','folded_kBt'],['g32','*','qm','folded_g31'],['Z','-','g32','Bt'],['g38','*','Z','Z'],['g39','*','qm','qm'],['A0','-','g38','g42'],['U','*','Y','q2'],['H','+',3,'g15'],['a','+','E','Y'],['Delta','+','H','g17'],['g52','-','k','R'],['r0','-','g52',1],['g54','*','U','gamma'],['shift','-','g54','r0'],['g58','*','U','b0'],['g59','*','H','shift'],['Dstar','+','g58','g59'],['g61','*','Dstar','Dstar'],['g62','*','U','U'],['g63','*','Delta','c2'],['g64','+',1,'g63'],['g65','*','g62','g64'],['A1','-','g61','g65'],['g19','*','a','c'],['b0','+','X','g19'],['g17','*','a','a'],['f2','*','f','f'],['rho','-','f2',1],['Q','*','Delta','rho'],['I','*','c2','i'],['g71','*','I','I'],['g72','-','g71','Q'],['y2','*','y','y'],['V2','*','V','V'],['g81','-','y2','V2'],['g82','*','Q','g81'],['Fa','-','y2','g82'],['A0sq','*','A0','A0'],['A1sq','*','A1','A1'],['Fam','-','Fa',1],['Fam2','*','Fam','Fam'],['Fsm2','*','g72','g72'],['sum01','+','A0sq','A1sq'],['sum23','+','Fam2','Fsm2'],['out','+','sum01','sum23']]:assert rp[row[0]]==row
# Free-ring identities used by cancellation and the A1 degree bound.
def con(n):return {():n} if n else {}
def var(n):return {(n,):1}
def add(a,b,s=1):
 z=dict(a)
 for k,v in b.items():z[k]=z.get(k,0)+s*v
 return {k:v for k,v in z.items() if v}
def mul(a,b):
 z={}
 for x,u in a.items():
  for y,v in b.items():
   k=tuple(sorted(x+y));z[k]=z.get(k,0)+u*v
 return {k:v for k,v in z.items() if v}
U,a,c0,X,H,S=map(var,['U','a','c','X','H','S']);ac=mul(a,c0);b0=add(X,ac);dst=add(mul(U,b0),mul(H,S));delta=add(mul(a,a),H)
lhs=add(mul(dst,dst),mul(mul(U,U),add(con(1),mul(delta,mul(c0,c0)))),-1)
inner=add(add(add(mul(con(2),mul(X,ac)),mul(X,X)),con(1),-1),mul(H,mul(c0,c0)),-1)
rhs=add(add(mul(mul(U,U),inner),mul(con(2),mul(mul(mul(U,b0),H),S))),mul(mul(H,H),mul(S,S)))
assert lhs==rhs
# Finite controls for the two strict estimates in the r=0 minus branch.
# These controls supplement, and do not replace, the general order argument.
checks=0
for km in range(2,17):
 for mm in range(2,41):
  for pp in range(1,mm):
   for tt in range(1,pp+1):
    assert km*(pp-1)<km*mm and tt<mm<=km*mm
    assert km*(pp-1)+tt<2*km*mm
    checks+=1
# t<=P does not imply the formerly proposed t<=k bound.
assert 2*(99-1)+99>2*99
# Syntactic witness-degree upper bound, with the checked A1 identity substituted.
d={x:1 for x in c['witnesses']};d.update({x:0 for x in c['fixed_numerals']})
for n,o,a0,b0_ in expect:
 da=0 if type(a0) is int else d[a0];db=0 if type(b0_) is int else d[b0_]
 d[n]=da+db if o=='*' else max(da,db)
bound=max(2*d['U']+d['X']+d['a']+d['c'],2*d['U']+2*d['X'],2*d['U'],2*d['U']+d['H']+2*d['c'],d['U']+d['b0']+d['H']+d['shift'],2*d['H']+2*d['shift'])
assert bound==30 and max(d['A0'],d['Fam'],d['g72'],bound)==30
# Authenticate compact P72/P115 bytes, then evaluate complete ray modulo a prime.
root=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
binding=json.loads(pin(root/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'))
b115=json.loads(pin(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'))
fixed={}
for n,item in binding['ports'].items():
 assert b115['ports'][n]['sha256_raw']==item['sha256_raw'] and b115['ports'][n]['sha256_gzip']==item['sha256_gzip']
 raw=gzip.decompress(pin(root/item['path'],item['sha256_gzip']));assert len(raw)==item['raw_bytes'] and digest(raw)==item['sha256_raw']
 fixed[n]=int.from_bytes(raw,'little')
assert set(fixed)==set(c['fixed_numerals']) and fixed['beta']>=46 and fixed['K0']>=0 and 0<fixed['MC']<fixed['beta'] and 0<fixed['MF']<2*fixed['beta']
assert fixed['K0']+1 <= (fixed['beta']+1)**2
prime=1000000007
def trim(x):
 while len(x)>1 and x[-1]==0:x.pop()
 return x
def ap(x,y,s):return trim([((x[i] if i<len(x) else 0)+s*(y[i] if i<len(y) else 0))%prime for i in range(max(len(x),len(y)))])
def mp(x,y):
 out=[0]*(len(x)+len(y)-1)
 for i,u in enumerate(x):
  for j,v in enumerate(y):out[i+j]=(out[i+j]+u*v)%prime
 return trim(out)
env={n:[0,1] for n in c['witnesses']};env.update({n:[v%prime] for n,v in fixed.items()})
for n,o,x,y in expect:
 x=[x%prime] if type(x) is int else env[x];y=[y%prime] if type(y) is int else env[y]
 env[n]=mp(x,y) if o=='*' else ap(x,y,1 if o=='+' else -1)
assert len(env['out'])-1==60 and env['out'][-1]!=0
print(json.dumps({'scope':'exact mixed-shift source and A1 identity; zero maps require documented force arguments; no Lean','variables':13,'operations':88,'degree':60,'counts':counts,'mixed_shift_rows_exact':True,'forced_unshifted':sorted(forced),'A1_cancellation_identity':True,'bounded_root_inequality_controls':checks,'invalid_stronger_inequality_counterexample_checked':True,'residual_degree_upper_bounds':{'A0':d['A0'],'A1':bound,'Fam':d['Fam'],'g72':d['g72']},'compact_port_bounds_checked':True,'compact_K_plus_one_le_beta_plus_one_squared':True,'ray_prime':prime,'ray_leading_coefficient':env['out'][-1],'lean_elaboration':False},sort_keys=True,indent=2))
