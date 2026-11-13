#!/usr/bin/env python3
"""Exact graph cuts, four unit-sign residue controls and actual-port degree rays."""
import gzip,hashlib,itertools,json
from collections import Counter
from pathlib import Path
H=Path(__file__).resolve().parent;ROOT=H.parents[1];p72=ROOT/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';p115=ROOT/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement'
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,p
 return b
old87=json.loads(pin(p115/'circuits/positive13_87_degree51.json','24b9120cc07693ba3fab0bff254c071fae800d14415850c3411651c026e28f0c'))
b115=json.loads(pin(p115/'coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'))
b72=json.loads(pin(p72/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'))
old90=json.loads(pin(ROOT/'research/ordinary-unit-products/p13_ordinary_degree51.json','c9f5f495249ed13d30393fec5838a85408889d214d2253615f4ba6f60414cf71'))
sphere54=json.loads(pin(ROOT/'research/ordinary13-p73-conditional-pair90-54/polynomial.json','3946b8c328d692e829d1f556ffcf78cc559e885f3715ee3509f241f4e75c47c0'))
review=json.loads(pin(ROOT/'reviews/ordinary13-p73-conditional-pair90-54-independent/result.json','4c8ab83c8ff728766d954fc6b1a11e2d86a8a5e45dcb05d9e668da092ffd2b9e'))
assert review['status']=='PASS_SCOPED_INDEPENDENT_REVIEW';pin(ROOT/'reviews/ordinary13-p73-conditional-pair90-54-independent/check.py','f73239adb431450a7618f42dd2f61eb80a0a116847e2d75806c901da58d097a9')
g88=json.loads(pin(H/'freej88.json','fc4627a15edc10f4cfcd3e6acf7df0896bb552a5f00cf238af6f1b5a349975bb'))
g90=json.loads(pin(H/'p73_90.json','7e230b399dc47497fa18c245bd043fb77adbe37cf0808ec4fb18fe75eaf17f48'))
assert {x[0]:x for x in old87['source']}['g80']==['g80','*','V','V']
assert {x[0]:x for x in old87['source']}['g81']==['g81','-','y2','g80']
assert old87['source'][-6:]==[['F0','+',1,'A0'],['F1','+',1,'A1'],['g86','*','F0','F1'],['g87','*','Fa','g86'],['g88','*','Fs','g87'],['P13','-','g88',1]]
r=[]
for row in old87['source'][:-6]:
 n=row[0]
 r.append(['g80','+','g78','V'] if n=='g80' else ['g81','*','u','g80'] if n=='g81' else row)
r.extend([['A0sq','*','A0','A0'],['A1sq','*','A1','A1'],['pair','*','Fa','Fs'],['pairm','-','pair',1],['pair2','*','pairm','pairm'],['sum01','+','A0sq','A1sq'],['out','+','sum01','pair2']])
assert g88['source']==r and g88['witnesses']==old87['witnesses'] and g88['fixed_numerals']==old87['fixed_numerals']
assert g90['source']==[['g72','-','g71','Kaux'] if r[0]=='g72' else ['Fs','+',1,'g72'] if r[0]=='Fs' else r for r in sphere54['source']]
assert g90['witnesses']==sphere54['witnesses'] and g90['fixed_numerals']==sphere54['fixed_numerals']
# Ring polynomials over explicit cuts; also compare P73 values against its
# established 90/51 ordinary-unit graph without identifying free-J coordinates.
def var(x):return {(x,):1}
def add(a,b):
 z=dict(a)
 for m,c in b.items():z[m]=z.get(m,0)+c
 return {m:c for m,c in z.items() if c}
def neg(a):return {m:-c for m,c in a.items()}
def sub(a,b):return add(a,neg(b))
def mul(a,b):
 z={}
 for m,x in a.items():
  for n,y in b.items():
   t=tuple(sorted(m+n));z[t]=z.get(t,0)+x*y
 return {m:c for m,c in z.items() if c}
one={():1};u,V=var('u'),var('V');y=add(V,u)
assert sub(mul(y,y),mul(V,V))==mul(u,add(y,V))
def eval_cut(g,cuts,target):
 vals={k:var(v) for k,v in cuts.items()}
 for n,op,a,b in g['source']:
  if n in vals:continue
  if (isinstance(a,str) and a not in vals) or (isinstance(b,str) and b not in vals):continue
  x=({():a} if isinstance(a,int) else vals[a]);y0=({():b} if isinstance(b,int) else vals[b])
  vals[n]=mul(x,y0) if op=='*' else (add(x,y0) if op=='+' else sub(x,y0))
 assert target in vals,target
 return vals[target]
for cuts,oldname,newname in [
 ({x:x for x in ['J','beta']},'qm','qm'),
 ({x:x for x in ['q']},'q2','q2'),
 ({x:x for x in ['q','q2']},'q3','q3'),
 ({x:x for x in ['q','F','alpha','X','K0']},'Bt','Bt'),
 ({x:x for x in ['X','Y']},'E','E'),
 ({x:x for x in ['Y','eta','zeta']},'c','c'),
 ({x:x for x in ['E','Y']},'a','a'),
 ({x:x for x in ['a']},'Delta','Delta'),
 ({x:x for x in ['a','c','X']},'b0','b0'),
 ({x:x for x in ['E','Y','eta','zeta']},'ell','ell'),
 ({x:x for x in ['q','q2','qm','J','F','alpha','MC','MF']},'R','R'),
 ({x:x for x in ['U','b0','H','E','q','k','R','gamma']},'Dstar','Dstar'),
 ({x:x for x in ['f','T','c','R']},'V','V'),
 ({x:x for x in ['c','i']},'I','I'),
 ({x:x for x in ['Delta','f']},'Q','Kaux'),
 ({x:x for x in ['ell','k','r','Y','qm','Bt','q3']},'A0','A0'),
 ({x:x for x in ['Dstar','U','Delta','c2']},'A1','A1'),
 ({'V':'V','u':'u','Q':'Q','Kaux':'Q'},'Fa','g83'),
 ({'I':'I','Q':'Q','Kaux':'Q'},'Fs','Fs')]:
 assert eval_cut(old90,cuts,oldname)==eval_cut(g90,cuts,newname),(oldname,newname)
# Source structures required by the four global negative-unit exclusions.
source={x[0]:x for x in old87['source']}
for row in [['q','+',1,'qm'],['q2','*','q','q'],['q3','*','q','q2'],['M','*','q3','qm'],['g15','*',4,'a'],['H','+',3,'g15'],['g17','*','a','a'],['Delta','+','H','g17'],['g38','*','Z','Z'],['g39','*','M','M'],['g40','*','ell','g30'],['g41','+',1,'g40'],['g42','*','g39','g41'],['A0','-','g38','g42'],['g61','*','Dstar','Dstar'],['g62','*','U','U'],['g63','*','Delta','c2'],['g64','+',1,'g63'],['g65','*','g62','g64'],['A1','-','g61','g65'],['f2','*','f','f'],['rho','-','f2',1],['Q','*','Delta','rho'],['I','*','c2','i'],['g71','*','I','I'],['g72','-','g71','Q'],['Fs','+',1,'g72'],['g78','+','V','u'],['y2','*','g78','g78'],['g80','*','V','V'],['g81','-','y2','g80'],['g82','*','Q','g81'],['Fa','-','y2','g82']]:assert source[row[0]]==row
# Finite controls for the unbounded mod-4 proof in README.
for a,f,I,V0,y0 in itertools.product(range(4),repeat=5):
 delta=(a*a+4*a+3)%4;Q=delta*(f*f-1)%4
 Fa=(y0*y0-Q*(y0*y0-V0*V0))%4;Fs=(1+I*I-Q)%4
 assert Q in (0,1) and Fa in (0,1) and Fs in (0,1,2)
for z in range(4):
 for m in range(0,8,2):assert (1+z*z-m*m)%4!=3
for ds,U,c,a in itertools.product(range(4),repeat=4):
 delta=(a*a+4*a+3)%4; F1=(1+ds*ds-U*U*(1+delta*c*c))%4
 assert F1!=3
prime=1000000007;fixed={}
assert set(b72['ports'])==set(b115['ports'])=={'beta','K0','MC','MF'}
for n,m in b72['ports'].items():
 assert b115['ports'][n]['sha256_raw']==m['sha256_raw'] and b115['ports'][n]['sha256_gzip']==m['sha256_gzip']
 raw=gzip.decompress(pin(p72/m['path'],m['sha256_gzip']));assert len(raw)==m['raw_bytes'] and hashlib.sha256(raw).hexdigest()==m['sha256_raw']
 x=int.from_bytes(raw,'little');assert x>0 and x.bit_length()==m['bits']
 if n=='beta':assert x==(1<<590069)-1
 fixed[n]=x%prime
def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
def sadd(a,b,s):return trim([((a[i] if i<len(a) else 0)+s*(b[i] if i<len(b) else 0))%prime for i in range(max(len(a),len(b)))])
def smul(a,b):
 z=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y0 in enumerate(b):z[i+j]=(z[i+j]+x*y0)%prime
 return trim(z)
def inspect(g,expected_count,leader,faname):
 rows=g['source'];assert len(rows)==g['operations']==expected_count and len(g['witnesses'])==13
 ready=set(g['witnesses']+g['fixed_numerals']);deg={x:1 for x in g['witnesses']};deg.update({x:0 for x in g['fixed_numerals']})
 for n,op,a,b in rows:
  assert n not in ready and op in ('+','-','*') and all(isinstance(x,int) or x in ready for x in (a,b))
  def dv(x):return 0 if isinstance(x,int) else deg[x]
  deg[n]=dv(a)+dv(b) if op=='*' else max(dv(a),dv(b));ready.add(n)
 needed={g['output']}
 for n,op,a,b in reversed(rows):
  if n in needed:needed.update((a,b))
 assert all(n in needed for n,_,_,_ in rows) and all(x in needed for x in g['witnesses']+g['fixed_numerals'])
 assert deg[faname]==13 and deg['Fs']==10 and deg[g['output']]==46
 vals={x:[0,1] for x in g['witnesses']};vals.update({n:[x] for n,x in fixed.items()})
 def value(x):return [x%prime] if isinstance(x,int) else vals[x]
 for n,op,a,b in rows:vals[n]=smul(value(a),value(b)) if op=='*' else sadd(value(a),value(b),1 if op=='+' else -1)
 assert len(vals[g['output']])-1==46 and vals[g['output']][-1]==leader
 return {'operations':len(rows),'counts':dict(sorted(Counter(x[1] for x in rows).items())),'all_gates_live':True,'syntactic_degree_upper':46,'ray_degree':len(vals[g['output']])-1,'ray_leader':leader}
results={'freej88':inspect(g88,88,528057335,'Fa'),'p73_90':inspect(g90,90,832098066,'g83')}
print(json.dumps({'status':'PASS','graphs':results,'prime':prime,'port_binding':'P72 raw and compressed bytes match P115 binding','ordinary_comparison':'P73 A0, A1, Fa, Fs exact symbolic cut equalities verified','scope':'external ring/graph checks, degree and mathematical integer-unit argument; no Lean or internal file binding'},indent=2,sort_keys=True))
