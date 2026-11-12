#!/usr/bin/env python3
"""direct Pell root with explicit quotient guards and authenticated compact44 degree; no Lean."""
import gzip,hashlib,json,random
from pathlib import Path
D=Path(__file__).resolve().parents[2];H=Path(__file__).resolve().parent
def load(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h;return json.loads(b)
c=load(H/'candidate.json','a4304844c9860ac1468d9cdbb4b75dd8d18c177ab5db267a24658cbdbce0fb43')
p=load(D/'research/ordinary13-aux-root87-36/candidate.json','abdd93cebd85dc2194478a76297d16ea04ca06855265420abf0b6c1b7e70db51')
assert c['witnesses']==p['witnesses']+['s_guard','t_guard'] and c['fixed_numerals']==p['fixed_numerals']
expect=[]
for row in p['source']:
 if row[0] in ('M','g31','folded_kBt','folded_g31','g32','g33','g34','folded_q3Bt','Z','g39','g42'):continue
 if row[0]=='g38':expect.append(['g38','*','r','r'])
 elif row[0]=='A0':expect.append(['A0','-','g38','g41'])
 else:expect.append(row)
expect += [['Y_expected','*','q3','s_guard'],['guard_y','-','Y','Y_expected'],['guard_y2','*','guard_y','guard_y'],['partial_out','+','out','guard_y2'],['Bt_expected','*','qm','t_guard'],['guard_bt','-','Bt','Bt_expected'],['guard_bt2','*','guard_bt','guard_bt'],['guarded_out','+','partial_out','guard_bt2']]
assert c['source']==expect and len(c['source'])==84
assert len({r[0] for r in c['source']})==84 and not ({r[0] for r in c['source']} & set(c['witnesses']+c['fixed_numerals']))
needed={'guarded_out'}
for n,op,x,y in reversed(c['source']):
 if n in needed:needed.update((x,y))
assert all(r[0] in needed for r in c['source']) and all(x in needed for x in c['witnesses']+c['fixed_numerals'])
def calc(graph,vs):
 d=vs.copy()
 def val(x):return x if isinstance(x,int) else d[x]
 for n,op,x,y in graph['source']:
  a,b=val(x),val(y);d[n]=a*b if op=='*' else a+b if op=='+' else a-b
 return d
rng=random.Random(8436)
for _ in range(100):
 v={x:rng.randrange(-4,5) for x in c['witnesses']+c['fixed_numerals']};new=calc(c,v)
 oldv={x:v[x] for x in p['witnesses']+p['fixed_numerals']}
 oldv['r']=new['k']*new['Bt']-new['ell']-new['k']-v['s_guard']+v['t_guard']+v['r']
 old=calc(p,oldv);M=new['q3']*new['qm']
 assert old['Z']==M*v['r']+new['qm']*new['guard_y']-new['q3']*new['guard_bt']
 assert all(old[n]==new[n] for n in ('A1','Fa','g72'))
p72=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';binding=load(p72/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf');b115=load(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01');fixed={}
for n,m in binding['ports'].items():
 assert b115['ports'][n]['sha256_raw']==m['sha256_raw'] and b115['ports'][n]['sha256_gzip']==m['sha256_gzip'];z=(p72/m['path']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['sha256_gzip'];x=gzip.decompress(z);assert len(x)==m['raw_bytes'] and hashlib.sha256(x).hexdigest()==m['sha256_raw'];fixed[n]=int.from_bytes(x,'little')
assert fixed['beta']>=46 and 0<=fixed['K0'] and 0<fixed['MC']<fixed['beta'] and 0<fixed['MF']<2*fixed['beta']
prime=1000000007;v={x:[0,1] for x in c['witnesses']};v.update({n:[x%prime] for n,x in fixed.items()})
def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
def add(a,b,s):return trim([((a[i] if i<len(a) else 0)+s*(b[i] if i<len(b) else 0))%prime for i in range(max(len(a),len(b)))])
def mul(a,b):
 z=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):z[i+j]=(z[i+j]+x*y)%prime
 return trim(z)
def val(x):return [x%prime] if isinstance(x,int) else v[x]
for n,op,x,y in c['source']:v[n]=mul(val(x),val(y)) if op=='*' else add(val(x),val(y),1 if op=='+' else -1)
assert len(v['guarded_out'])-1==36 and v['guarded_out'][-1]!=0
print(json.dumps({'operations':84,'variables':15,'all_gates_inputs_ports_live':True,'all_integer_substitution_controls':100,'port_bounds_checked':True,'prime':prime,'ray_degree':36,'ray_leader':v['guarded_out'][-1],'scope':'external two-quotient-guard source/substitution and degree controls; positive-zero equivalence submitted for review; no Lean/PDF binding'},sort_keys=True,indent=2))
