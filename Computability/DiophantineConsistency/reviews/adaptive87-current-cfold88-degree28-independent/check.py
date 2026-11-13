#!/usr/bin/env python3
"""Independent bounded checks of current-port C-fold; no Lean."""
import gzip,hashlib,json,math,random,subprocess,sys
from collections import Counter
from pathlib import Path
R=Path(__file__).resolve().parents[2];D=Path(__file__).resolve().parent
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
for f,h in json.loads((D/'pins.json').read_text()).items():assert hashlib.sha256((R/f).read_bytes()).hexdigest()==h,f
c=json.loads((R/'research/adaptive87-current-cfold88-degree28/graph.json').read_bytes())
p=json.loads((R/'research/adaptive87-four-square-current88-30/graph.json').read_bytes())
assert c['witnesses']==p['witnesses'] and c['fixed_numerals']==p['fixed_numerals'] and c['output']==p['output']
assert len(c['witnesses'])==13 and len(c['fixed_numerals'])==4 and len(c['source'])==len(p['source'])==88
changes=[(i,a,b) for i,(a,b) in enumerate(zip(p['source'],c['source'])) if a!=b]
assert changes==[(28,['root_skew','*','k','Bt'],['root_skew','*','k','C'])]
assert [(i,r) for i,r in enumerate(c['source']) if 'r' in r[2:]]==[(27,['g31','+','g30','r'])]
# Independently derive topology and liveness by backtracking from the output.
env=set(c['witnesses']+c['fixed_numerals']);rows={}
for n,op,a,b in c['source']:
 assert n not in env and op in '+-*' and all(not isinstance(x,str) or x in env for x in (a,b))
 rows[n]=(op,a,b);env.add(n)
live=set();stack=[c['output']]
while stack:
 n=stack.pop()
 if n in live:continue
 live.add(n)
 if n in rows:stack.extend(a for a in rows[n][1:] if isinstance(a,str))
assert set(rows).issubset(live) and set(c['witnesses']+c['fixed_numerals']).issubset(live)
meta_path=R/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json'
meta=json.loads(meta_path.read_bytes())['coefficient_binding']['ports'];ports={}
for n,d in meta.items():
 raw=gzip.decompress((meta_path.parent/'coefficients'/d['file']).read_bytes())
 assert hashlib.sha256(raw).hexdigest()==d['raw_sha256'] and len(raw)==d['raw_bytes']; ports[n]=int.from_bytes(raw,'big')
assert ports['beta']==2**(47*2011)-1
assert ports['beta']>=46 and ports['K0']>=0 and 0<ports['MC']<ports['beta'] and 0<ports['MF']<2*ports['beta']
P=1000000007
def evaluate(g,values,mod=None):
 v=values.copy()
 for n,op,a,b in g['source']:
  x=v[a] if isinstance(a,str) else a;y=v[b] if isinstance(b,str) else b
  z=x+y if op=='+' else x-y if op=='-' else x*y
  v[n]=z if mod is None else z%mod
 return v
# Different degree-witness method: the 28th forward difference of the whole
# output at 0,...,28 is 28! times its leading coefficient given degree <=28.
f=[]
for t in range(29):
 val={**{n:v%P for n,v in ports.items()},**{n:t for n in c['witnesses']}}
 f.append(evaluate(c,val,P)[c['output']])
for j in range(28):f=[(f[i+1]-f[i])%P for i in range(len(f)-1)]
leading=f[0]*pow(math.factorial(28),-1,P)%P
assert leading==437565601 and leading!=0
# Check the coordinate map at generic signed ports, including negative r,
# without using the author's checker; this is a wiring control, not the proof.
rng=random.Random(99813)
for _ in range(100):
 v={name:rng.randrange(-7,8) for name in c['witnesses']+c['fixed_numerals']};x=evaluate(c,v)
 v['r']+=x['k']*(x['Bt']-x['C']);y=evaluate(p,v)
 assert all(x[n]==y[n] for n in ['Z','A0','A1','Fa','g72','output'])
original=subprocess.check_output([sys.executable,'-I','-S','-B',str(R/'research/adaptive87-current-cfold88-degree28/check.py')],cwd=R)
assert original==(R/'research/adaptive87-current-cfold88-degree28/result.json').read_bytes()
print(json.dumps({'changed_row':changes,'live_rows':len(rows),'op_counts':dict(Counter(r[1] for r in c['source'])),'beta_exponent':47*2011,'fixed_port_inequalities':True,'finite_difference_order':28,'leading_coefficient_mod_1000000007':leading,'signed_wiring_controls':100,'author_receipt_reproduced':True,'limits':'port-payload, finite and source checks only; Cal remains an explicit premise; no Lean'},sort_keys=True,indent=2))
