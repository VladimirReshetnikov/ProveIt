#!/usr/bin/env python3
import hashlib,json,sys,subprocess,collections
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-operation-count';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'check.py')=='16f048ec08f71f5f9b1639175095a7dc7aad53d64d888aa07031ec24756a85b7' and sha(p/'result.json')=='6b7ab2acb34af528dc245ce7e299efdcd773c880479424dff3cf44863248e83b'
seed=root/'research/nine-sharing-sign14-tau-candidate/seed.json';assert sha(seed)=='7048a10d409ab5ff8031a444cd32117ba772b3834425c17a066188338e189ea9';d=json.loads(seed.read_text());assert d['witness_count']==14 and len(d['residuals'])==5
variables=set();ports=set()
def convert(e):
 assert isinstance(e,list)
 op=e[0]
 if op in ('add','sub','mul'):
  assert len(e)==3;return (op,convert(e[1]),convert(e[2]))
 assert len(e)==2 and op in ('var','port','num')
 if op=='var':assert type(e[1])==int and 1<=e[1]<=14;variables.add(e[1])
 if op=='port':assert e[1] in ('beta','K0','MC','MF');ports.add(e[1])
 if op=='num':assert type(e[1])==int
 return tuple(e)
roots=[convert(x['expr']) for x in d['residuals']];assert len(set(roots))==5 and variables==set(range(1,15)) and ports=={'beta','K0','MC','MF'}
def gather(node,acc):
 if node[0] in ('add','sub','mul'):
  acc.add(node);gather(node[1],acc);gather(node[2],acc)
base=set()
for e in roots:gather(e,base)
assert len(base)==89
squares=[('mul',x,x) for x in roots];output=squares[0]
for x in squares[1:]:output=('add',output,x)
live=set();gather(output,live);counts=dict(sorted(collections.Counter(x[0] for x in live).items()));assert len(live)==98 and counts=={'add':41,'sub':15,'mul':42} and len(live-base)==9
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,text=True,check=True,timeout=120);assert not x.stderr and json.loads(x.stdout)==json.loads((p/'result.json').read_text())
print(json.dumps({'status':'PASS_EXTERNAL_AUDIT','residual_gates':len(base),'live_gates':len(live),'counts':counts,'scope':'one exact ordered-subtree hash-consed circuit, square multiply and free leaves; upper bound, not minimum or Lean/JSON/PDF binding'},indent=2))
