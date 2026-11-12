#!/usr/bin/env python3
"""Graph delta, signed controls and actual-port degree ray; no Lean."""
import gzip, hashlib, json, random, subprocess, sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
D=Path(__file__).resolve().parents[2]; P=Path(__file__).resolve().parent
def pin(p,h):
 x=p.read_bytes(); assert hashlib.sha256(x).hexdigest()==h,p; return x
old=json.loads(pin(D/'research/ordinary14-direct-pell79/candidate.json','5c5e2c089d0f10450374219e9d74883235fd0ef3b10d31d6df09a7dc498e2507'))
new=json.loads(pin(P/'candidate.json','d579ba32a40eed91a336b0015086104e1d1a7c6569092f757328769a3128ab43'))
assert new['witnesses']==[('y' if n=='u' else n) for n in old['witnesses']]
assert new['fixed_numerals']==old['fixed_numerals'] and new['output']==old['output']
expect=[]
for row in old['source']:
 n,op,a,b=row
 if n in ('g78','g80','g81'):continue
 if n=='y2':row=['y2','*','y','y']
 if n=='g82':expect.extend([['V2','*','V','V'],['g81','-','y2','V2']])
 expect.append(row)
assert expect==new['source'] and len(expect)==78
known=set(new['witnesses']+new['fixed_numerals']); needed={new['output']}
for n,op,a,b in expect:
 assert n not in known and op in '+-*' and all(isinstance(x,int) or x in known for x in (a,b));known.add(n)
for n,op,a,b in reversed(expect):
 if n in needed:needed.update(x for x in (a,b) if isinstance(x,str))
assert all(row[0] in needed for row in expect) and set(new['witnesses']+new['fixed_numerals'])<=needed
def calc(g,v):
 v=v.copy()
 for n,op,a,b in g['source']:
  a=a if isinstance(a,int) else v[a];b=b if isinstance(b,int) else v[b]
  v[n]=a+b if op=='+' else a-b if op=='-' else a*b
 return v
rng=random.Random(7860)
for _ in range(160):
 v={n:rng.randrange(-4,5) for n in old['witnesses']+old['fixed_numerals']}
 x=calc(old,v); w={n:v[n] for n in new['witnesses'] if n!='y'};w.update({n:v[n] for n in new['fixed_numerals']});w['y']=x['V']+v['u'];z=calc(new,w)
 assert all(x[n]==z[n] for n in ('A0','A1','Fa','g72','guard','guarded_out'))
for directory,checksha,resultsha in [
 ('ordinary14-direct-pell79-math-independent','1ebee8cc29957fb9f044510bbc80efc80951ec2e9430ef294fafac78b293d1fe','056877679b6a9d7fcc2cc04747d80344fcb14956914a3affb0caa824fde42555'),
 ('ordinary13-folded-root86-negated-positive-bt-independent','676c47df37d52784e45dc39b1a29af36f9cb7caaaaa9beb896fbc96f68f867c8','6067f43c969e733ca45841f4cb52b9337ef42a35f865b781cac6875abd8bb09a')]:
 q=D/'reviews'/directory;pin(q/'check.py',checksha);pin(q/'result.json',resultsha)
 r=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=180)
 assert not r.stderr and r.stdout==(q/'result.json').read_bytes()
root=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
binding=json.loads(pin(root/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'))
b115=json.loads(pin(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'))
ports={}
for n,m in binding['ports'].items():
 assert all(b115['ports'][n][x]==m[x] for x in ('sha256_raw','sha256_gzip'))
 raw=gzip.decompress(pin(root/m['path'],m['sha256_gzip']));assert len(raw)==m['raw_bytes'] and hashlib.sha256(raw).hexdigest()==m['sha256_raw'];ports[n]=int.from_bytes(raw,'little')
assert ports['beta']==(1<<590069)-1
prime=1000000007;v={n:[0,1] for n in new['witnesses']};v.update({n:[x%prime] for n,x in ports.items()})
def trim(a):
 while len(a)>1 and not a[-1]:a.pop()
 return a
def pol(op,x,y):
 if op!='*':return trim([((x[i] if i<len(x) else 0)+(1 if op=='+' else -1)*(y[i] if i<len(y) else 0))%prime for i in range(max(len(x),len(y)))])
 z=[0]*(len(x)+len(y)-1)
 for i,a in enumerate(x):
  for j,b in enumerate(y):z[i+j]=(z[i+j]+a*b)%prime
 return trim(z)
for n,op,a,b in expect:v[n]=pol(op,[a%prime] if isinstance(a,int) else v[a],[b%prime] if isinstance(b,int) else v[b])
assert len(v['guarded_out'])==61 and v['guarded_out'][-1]
print(json.dumps({'operations':78,'operation_breakdown':{op:sum(row[1]==op for row in expect) for op in '+-*'},'all_gates_inputs_ports_live':True,'signed_graph_substitution_controls':160,'reviewed_parent_and_Pell_descent_replayed':True,'prime':prime,'ray_degree':len(v['guarded_out'])-1,'ray_leader':v['guarded_out'][-1],'scope':'external positive-zero existence map for beta>0; compact44 degree only; no Lean or PDF binding'},sort_keys=True,indent=2))
