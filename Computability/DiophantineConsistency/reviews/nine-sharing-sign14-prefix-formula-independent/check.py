#!/usr/bin/env python3
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-prefix-formula';seed=root/'research/nine-sharing-sign14-tau-candidate/seed.json';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(seed)=='7048a10d409ab5ff8031a444cd32117ba772b3834425c17a066188338e189ea9' and sha(p/'manifest.json')=='e693db97abb83295b47f720cf23133493a8d9c81956ae400f4692d182e5391a3'
d=json.loads(seed.read_text());m=json.loads((p/'manifest.json').read_text());assert m['ports']==['beta','K0','MC','MF'] and len(m['rows'])==len(d['residuals'])==5
op={'+' : 'add','-':'sub','*':'mul'};ports={'B':'beta','K':'K0','C':'MC','F':'MF'}
def decode(raw):
 stack=[]
 for c in reversed(raw.decode('ascii')):
  if c in op:
   assert len(stack)>=2;stack.append([op[c],stack.pop(),stack.pop()])
  elif c in ports:stack.append(['port',ports[c]])
  elif c in '1234':stack.append(['num',int(c)])
  else:assert 'a'<=c<='o';stack.append(['var',ord(c)-ord('a')])
 assert len(stack)==1;return stack[0]
for i,(row,res) in enumerate(zip(m['rows'],d['residuals'])):
 assert row['file']==f'row{i:02}.prefix' and row['gate']==res['gate'];q=p/row['file'];raw=q.read_bytes();assert len(raw)==row['length'] and sha(q)==row['sha256'] and decode(raw)==res['expr']
 assert all(b<128 for b in raw)
 try:decode(raw+b'+')
 except (AssertionError,IndexError):pass
 else:raise AssertionError('trailing operator accepted')
print(json.dumps({'status':'PASS_EXTERNAL_AST_RECONSTRUCTION','rows':5,'lengths':[x['length'] for x in m['rows']],'scope':'external prefix↔pinned seed AST; no Lean parser or PDF binding'},indent=2))
