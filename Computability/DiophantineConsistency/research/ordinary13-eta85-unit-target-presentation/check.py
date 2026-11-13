from pathlib import Path
from hashlib import sha256
import json,random,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-eta85-unit-target-presentation')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
a=json.loads(Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_text());b=json.loads((D/'presentation.json').read_text())
assert len(a['source'])==85 and len(b['source'])==84
assert a['source'][:-1]==b['source'] and a['source'][-1]==['out','-','P0123',1]
assert a['output']=='out' and b['output']=='P0123' and b['target']==1
assert a['witnesses']==b['witnesses'] and a['fixed_numerals']==b['fixed_numerals'] and a['domain']==b['domain']
def ev(g,w,p):
 d=dict(zip(g['witnesses'],w));d.update(zip(g['fixed_numerals'],p))
 for n,op,x,y in g['source']:
  x=d[x] if isinstance(x,str) else x;y=d[y] if isinstance(y,str) else y
  d[n]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 return d[g['output']]
rng=random.Random(85111)
for _ in range(200):
 w=[rng.randrange(5) for _ in range(13)];p=[rng.randrange(-3,5) for _ in range(4)]
 old=ev(a,w,p);new=ev(b,w,p)
 assert old==new-1 and (old==0)==(new==1)
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'parent_rows':85,'left_side_rows':84,'target':1,'exact_last_gate_identity':True,
 'integer_evaluation_controls':200,'normalized_zero_polynomial_operations':85,
 'scope':'Presentation saving only; no normalized-circuit, Lean or proof-theory reduction.',
 'lean_executed':False},sort_keys=True,indent=2))
