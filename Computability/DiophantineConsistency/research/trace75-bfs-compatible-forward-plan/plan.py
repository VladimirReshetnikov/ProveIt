#!/usr/bin/env python3
"""Read-only direct-import plan; does not run Lean or prove transitive ancestry."""
from hashlib import sha256
from pathlib import Path
import json,os,re,sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;D=H.parents[1];PARENT=D/'research/trace75-bfs-compatible-provider-rebuild/observations/attempt01/result.json';OUTER=D/'research/trace75-bfs-compatible-provider-rebuild/observations/outer-attempt01/terminal.json';AUDIT=D/'reviews/trace75-bfs-compatible-provider-result-independent/README.md';HIST=D/'research/trace75-bfs-model-halt-prototype/observations/attempt01/result.json';BFSOUT=D/'research/direct-bfs-80-coherent-rebuild/observations/attempt01/outside-baseline.json'
BASE=Path('/tmp/trace75-fresh-rebuild-i9ozk1vd/lib');PACK=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');CORE=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean');PINS={PARENT:'04cd437011c9a8b753a310da6c7691f229f9758b9050fdba9b61b812697fbc3c',OUTER:'8714c2ca237d88faa4bc373ed827ede93ee9cb2b4af9d77f0217d5363e3bd964',AUDIT:'e5721fba63d3cb6db75f389919f4f22a4177e0398cb07dfa671322e0a0d63f8a',HIST:'f07f6309693b7259e15bd149a14c2da5e96e50c62b5fc82c43ca60d4fa416a4a',BFSOUT:'5ed42b353836c0cae01a838b701347c7a2c9cc84318e893fbe5c4ae0c7c0b777'}
SUFFIXES=('.olean','.olean.private','.olean.server','.ilean','.ir','.olean.hash','.olean.private.hash','.olean.server.hash','.ilean.hash','.ir.hash')
sha=lambda p:sha256(Path(p).read_bytes()).hexdigest()
for p,h in PINS.items():assert sha(p)==h,(str(p),'pin')
parent=json.loads(PARENT.read_text());outer=json.loads(OUTER.read_text());hist=json.loads(HIST.read_text());outside=json.loads(BFSOUT.read_text());assert parent['status']=='PASS' and outer['exit']==0 and outer['child_status']=='PASS' and outer['child_result_sha256']==PINS[PARENT]
assert Path(parent['output_root'])/'lib'==BASE and len(parent['stages'])==31
oldroots=list(reversed(hist['env']['LEAN_PATH'].split(':')[:-2]));assert len(oldroots)==21
objs=[]
for d in oldroots:
 root=Path(d);items=list(root.glob('*.olean'));assert len(items)==1;obj=items[0];objs.append((obj.stem,obj,sha(obj)))
names=[n for n,_,_ in objs];assert len(set(names))==21 and names[-1]=='Trace75BFSModelHalt'
receipts=[]
for p,h in hist['inputs'].items():
 if not p.endswith('/result.json'):continue
 q=Path(p)
 try:r=json.loads(q.read_text())
 except (ValueError,OSError):continue
 if r.get('status')=='PASS':assert sha(q)==h;receipts.append((q,r))
receipts.append((HIST,hist))
def sel(n,roots):
 rel=n.replace('.','/')+'.olean'
 for root in roots:
  q=Path(root)/rel
  if os.path.lexists(q):assert q.is_file(),('shadow',str(q));return q
 raise RuntimeError('unresolved '+n)
def bundle(obj):
 stem=str(obj)[:-6];out={}
 for ext in SUFFIXES:
  q=Path(stem+ext)
  if not os.path.lexists(q):out[ext]=None;continue
  assert q.is_file();out[ext]={'path':str(q),'resolved':str(q.resolve(strict=True)),'sha256':sha(q),'link':os.readlink(q) if q.is_symlink() else None}
 return out
rows=[];done=set();direct={};changes=[]
for n,obj,digest in objs:
 hits=[(p,r) for p,r in receipts if r.get('object_sha256')==digest];assert len(hits)==1,(n,len(hits));receipt,rr=hits[0];assert rr['status']=='PASS' and rr['stage']['exit']==0 and rr['stage']['reason'] is None
 source=receipt.parents[2]/(n+'.lean');snapshot=receipt.parent/'source.txt';stdout=receipt.parent/'stdout';stderr=receipt.parent/'stderr';assert sha(source)==sha(snapshot)==rr['inputs'][str(source)] and sha(stdout)==rr['stage']['stdout_sha256'] and sha(stderr)==rr['stage']['stderr_sha256'] and not stderr.read_text()
 imports=re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',source.read_text(),re.M);assert [x for x in rr['header_imports'] if x!='Init']==imports
 refs={}
 for dep in imports:
  if dep in names:assert dep in done,('not topological',n,dep);refs[dep]={'kind':'stage'};continue
  now=sel(dep,[BASE,PACK,CORE]);old=sel(dep,rr['env']['LEAN_PATH'].split(':'));kind='project' if now.is_relative_to(BASE) else 'outside'
  rec={'kind':kind,'bundle':bundle(now),'old_selected':str(old),'old_sha256':sha(old)};refs[dep]=rec
  if dep in direct:assert direct[dep]['bundle']==rec['bundle']
  direct[dep]=rec
  if rec['bundle']['.olean']['sha256']!=rec['old_sha256']:changes.append({'stage':n,'module':dep,'old_sha256':rec['old_sha256'],'new_sha256':rec['bundle']['.olean']['sha256']})
 done.add(n);rows.append({'module':n,'source':str(source),'source_sha256':sha(source),'snapshot':str(snapshot),'snapshot_sha256':sha(snapshot),'receipt':str(receipt),'receipt_sha256':sha(receipt),'stdout':str(stdout),'stdout_sha256':sha(stdout),'stderr':str(stderr),'stderr_sha256':sha(stderr),'old_object':str(obj),'old_object_sha256':digest,'imports':imports,'prior_serialized_headers':rr['header_imports'],'direct':refs})
extras=sorted(n for n,r in direct.items() if r['kind']=='outside' and n not in outside)
for p,h in PINS.items():assert sha(p)==h
result={'status':'PASS','scope':'source/receipt and current first direct import plan only; no Lean replay or complete selected transitive closure/source ancestry','parent_result_sha256':sha(PARENT),'parent_outer_sha256':sha(OUTER),'parent_audit_sha256':sha(AUDIT),'prior_client_result_sha256':sha(HIST),'planner_sha256':sha(__file__),'stages':rows,'direct':direct,'direct_hash_changes':changes,'direct_outside_absent_from_bfs_capture':extras}
o=H/'observations/plan-attempt01';o.mkdir(parents=True,exist_ok=False);(o/'result.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps({'status':'PASS','stages':len(rows),'direct_names':len(direct),'changed_direct':changes,'additional_outside':extras,'sha256':sha(o/'result.json')}))
