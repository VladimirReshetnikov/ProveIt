#!/usr/bin/env python3
"""Independent bounded source-header and patch-delta review; no Lean."""
from pathlib import Path
from collections import deque
import hashlib,json,re,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1];A=D/'research/ordinary14-root74-tactic-import-audit';O=D/'research/ordinary14-root74-slim-overlay'
def H(b):return hashlib.sha256(b).hexdigest()
pins={A/'README.md':'3ff7b6eb564205a8f141d2784dccc1151395111abc3f5a6cdd17d0a3b4528054',A/'check_source.py':'bbb6a19d240f01047d566083d1f86af35284a6bf5609811b8eed2af2769b4ec0',A/'observation.json':'c32c11e4d041c2c8ced1d711438bf062d287213477c41f578106d8d50d76f598',O/'inventory.json':'b3317a1aa674fd67708aef94685af953126fcd1f30ead3bd43a9afb95467583e'}
tail=b"\nIndependent source review: [root74 tactic import audit](../../reviews/ordinary14-root74-tactic-import-audit-independent/README.md).\n"
for p,h in pins.items():
 if p==A/'README.md':
  data=p.read_bytes();assert H(data)=='43b178a2a413626f6fd7555639a15ae2a5329f919169c2730543c4b50f6f5c98'
  assert data.endswith(tail) and H(data[:-len(tail)])==h
 else:assert H(p.read_bytes())==h,(str(p),H(p.read_bytes()),h)
j=json.loads((O/'inventory.json').read_bytes()); receipt=json.loads((A/'observation.json').read_bytes());
# Independent nested-comment stripping and initial-header parser. No external
# package/Foundation source is followed beyond the recorded project graph.
def header(b):
 text=b.decode();z=[];depth=0;pos=0
 while pos<len(text):
  if depth and text.startswith('-/',pos):depth-=1;pos+=2;continue
  if text.startswith('/-',pos):depth+=1;pos+=2;continue
  if not depth and text.startswith('--',pos):
   pos=text.find('\n',pos)
   if pos<0:break
  if text[pos]=='\n':z.append('\n')
  elif not depth:z.append(text[pos])
  pos+=1
 assert depth==0
 out=[]
 for line in ''.join(z).splitlines():
  line=line.strip()
  if not line or line in ('prelude','module'):continue
  m=re.fullmatch(r'(?:(?:public|meta)\s+)*import\s+(?:all\s+)?([A-Za-z0-9_.]+(?:\s+[A-Za-z0-9_.]+)*)',line)
  if not m:break
  out.extend(m.group(1).split())
 return out
rows={r['module']:r for r in j['drafts_topological']};assert len(rows)==159
edges={};users={}
for n,r in rows.items():
 b=(O/r['path']).read_bytes();assert H(b)==r['overlay_sha256'];imports=header(b)
 assert [x for x in imports if '.' not in x]==r['bare_imports']
 assert [x for x in imports if '.' in x]==r['qualified_imports']
 edges[n]=imports
 hit=[i for i,line in enumerate(b.decode().splitlines(),1) if re.search(r'\blinear_combination\b',line)]
 if hit:users[n]=hit
for n,r in j['project_sources'].items():
 b=(D/r['path']).read_bytes();assert H(b)==r['sha256'];assert header(b)==r['imports'],n;assert n not in edges;edges[n]=header(b)
assert set(users)==set(receipt['tactic_users']) and len(users)==8 and sum(map(len,users.values()))==14
T='Mathlib.Tactic.LinearCombination'
def explore(start):
 q=deque([(start,)]);seen={start};leaves=set();shortest=None
 while q:
  path=q.popleft();n=path[-1]
  if n==T and shortest is None:shortest=path
  if n not in edges:leaves.add(n);continue
  for x in edges[n]:
   if x not in seen:seen.add(x);q.append(path+(x,))
 return shortest,sorted(leaves)
for n,lines in users.items():
 expected=receipt['tactic_users'][n];shortest,leaves=explore(n)
 assert expected['lines']==lines and expected['unexpanded_leaves']==leaves and expected['unexpanded_leaf_count']==len(leaves)
 path=expected['shortest_observed_path'];assert (path is None)==(shortest is None)
 if path:
  assert path[0]==n and path[-1]==T and len(path)==len(shortest)
  assert all(b in edges[a] for a,b in zip(path,path[1:]))
assert sorted(n for n in users if explore(n)[0] is None)==['OwnZeroGuardStrict74','PairEvalRingBridge']
patches={'OwnZeroGuardStrict74':D/'research/ordinary14-74-guard-linear-combination-patch/OwnZeroGuardStrict74.lean.src','PairEvalRingBridge':D/'research/ordinary14-pair-eval-linear-combination-patch/PairEvalRingBridge.lean.src'}
for n,p in patches.items():
 old=(O/rows[n]['path']).read_bytes();new=p.read_bytes()
 assert new==b'import Mathlib.Tactic.LinearCombination\n'+old
 assert header(new)==[T]+header(old)
 assert receipt['preventive_patch_controls'][n]['patch_sha256']==H(new)
 assert receipt['preventive_patch_controls'][n]['in_memory_path']==[n,T]
r=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not r.stderr and r.stdout==(A/'observation.json').read_bytes()
print(json.dumps({'scope':'independent source-header graph and patch controls; unexpanded leaves are not absence, no Lean/provider proof','pins':{str(p.relative_to(D)):h for p,h in pins.items()},'draft_modules':len(rows),'project_headers':len(j['project_sources']),'lexical_users':len(users),'token_lines':sum(map(len,users.values())),'recorded_paths':sum(explore(n)[0] is not None for n in users),'no_recorded_path':sorted(n for n in users if explore(n)[0] is None),'patch_controls':sorted(patches),'author_receipt_replayed':True},sort_keys=True,indent=2))
