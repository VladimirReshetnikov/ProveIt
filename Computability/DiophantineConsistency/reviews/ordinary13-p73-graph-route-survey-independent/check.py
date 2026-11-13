#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys
from collections import defaultdict
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
base=Path(__file__).resolve().parents[2];repo=base.parents[1];p=base/'research/ordinary13-p73-graph-route-survey'
cache={}
def sha(q):
 q=Path(q)
 if q not in cache:
  with q.open('rb') as f:cache[q]=hashlib.file_digest(f,'sha256').hexdigest()
 return cache[q]
for n,h in {'README.md':'0ca2046cfdb75848bfd0bf86b2d07fcec05b1e958299ac7dc4d877ea0ab0fa58','inspect.py':'072edc61b17b6cd9344963db101004e2b2922bfbe34c13011d364c5b6b4983e2','observation.json':'5e3efc56c0659a60ba1c3a935c69050f1bb57fe02ad1a083fb92da2a54d3d333'}.items():assert sha(p/n)==h
frozen=json.loads((p/'observation.json').read_text());r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'inspect.py')],cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=180);assert not r.stderr;fresh=json.loads(r.stdout)
volatile={'tmp_free_bytes','head','head_changed_during_prior_survey'}
assert {k:v for k,v in fresh.items() if k not in volatile}=={k:v for k,v in frozen.items() if k not in volatile}
assert fresh['status']=='READ_ONLY_OBSERVATION_NOT_BUILD_READINESS' and not fresh['route_issues'] and not fresh['different_hash_candidates'] and not fresh['excluded_target_artifacts'] and not fresh['provider_snapshot_target_sources']
assert fresh['inspector_sha256']==sha(p/'inspect.py')
p72=Path('/tmp/p72-current-base-extension-attempt02-20261105');b=Path('/tmp/current14-standard-fresh-build-20261104');pkg=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');tool=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean'); roots=[p72/'lib',pkg,tool]
order=json.loads((base/'research/p72-current-base-source-survey/result.json').read_text())['extension_order'];ix={n:i for i,n in enumerate(order)};bs=json.loads((b/'state.json').read_text());br={r['module']:r for r in bs['records']}
pref='DiophantineConsistency.Compact44.';front={pref+'FreeJSumSquares',pref+'FreeJSignedTransport'}
seenp=set();seenb=set();pq=list(front);bq=[];edge=0;guards=0
# Recompute the 30 producer ancestry from recorded rows; independently hash
# each recorded direct object and each of the specifically scoped slots.
def guard(g):
 global guards
 for raw,x in g.items():
  guards+=1;q=Path(raw)
  if x is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==x['realpath'] and sha(q)==x['sha256']
while pq:
 n=pq.pop()
 if n in seenp:continue
 seenp.add(n);row=json.loads((p72/'rows'/f'{ix[n]:04d}.json').read_text());assert row['module']==n and row['status']=='PASS'
 obj=p72/'lib'/Path(n.replace('.','/')+'.olean');assert sha(obj)==row['object_sha256'];guard(row['direct_guard'])
 for d,x in row['dependencies'].items():
  q=Path(x['path']);assert q.is_file() and str(q.resolve())==x['realpath'] and sha(q)==x['sha256'];edge+=1
  if d in ix:pq.append(d)
  elif d in br:bq.append(d)
while bq:
 n=bq.pop()
 if n in seenb:continue
 seenb.add(n);row=br[n];obj=b/'lib'/Path(n.replace('.','/')+'.olean');assert sha(obj)==row['object_sha256'];guard(bs['outputs'][n])
 for d,x in row['direct_inputs'].items():
  q=Path(x['path']);assert q.is_file() and sha(q)==x['sha256'];edge+=1
  if x['kind']=='project':assert d in br;bq.append(d)
assert (len(seenp),len(seenb),edge,guards)==(13,17,86,1220)
assert sorted(seenp)==fresh['p72_project_producers'] and sorted(seenb)==fresh['base_project_producers']
assert len(fresh['captured_edges'])==119 and sum(e['owner'] not in ('P72 producer','base producer','declared graph source') for e in fresh['captured_edges'])==86
# Independently compare the exact declared source and client import lines.
for n,row in fresh['declared_project_sources'].items():
 q=repo/row['source'];assert sha(q)==row['source_sha256'];imports=[]
 for line in q.read_text().splitlines():
  m=re.match(r'^\s*(?:public\s+)?import\s+([^\n-]+)',line)
  if m:imports.extend(m[1].split())
 assert imports==row['imports']
client=(base/'research/ordinary13-p73-share91-lean-draft/P73Shared91.lean').read_text();assert [s for s in client.splitlines() if s.startswith('import ')]==['import DiophantineConsistency.Compact44.P73Graph']
# Check every actual inventory candidate against all three existing roots and
# 13 suffixes, with the first candidate compared to its historical route.
suffix=['.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash','.so','.dll','.dylib'];inv=fresh['module_inventory'];assert len(inv)==54
for n,item in inv.items():
 stem=n.replace('.','/')
 for s in suffix:
  actual=[]
  for root in roots:
   q=root/(stem+s)
   if os.path.lexists(q):assert q.is_file();actual.append((str(q),str(q.resolve()),sha(q)))
  recorded=[(x['path'],x['realpath'],x['sha256']) for x in item['observed'].get(s,[])]
  assert actual==recorded and len({x[2] for x in actual})<=1
  if s=='.olean' and item['historical_routes']:
   assert len(item['historical_routes'])==1 and actual and actual[0][1:]==(item['historical_routes'][0]['realpath'],item['historical_routes'][0]['sha256'])
init=inv['Init']['observed']['.olean'];assert len(init)==2 and init[0]['realpath']==init[1]['realpath'] and init[0]['sha256']==init[1]['sha256']
# Independent traversal of all retained P72 olean names and cross-root suffix
# collisions. os.walk does not follow symlink directories, as qualified.
names=set()
for parent,dirs,files in os.walk(p72/'lib',followlinks=False):
 assert not any((Path(parent)/d).is_symlink() for d in dirs)
 for f in files:
  if f.endswith('.olean'):
   q=Path(parent)/f;assert q.is_file();names.add(str(q.relative_to(p72/'lib'))[:-6].replace('/','.'))
assert len(names)==1681 and names==set(ix)|set(br)
for n in names:
 stem=n.replace('.','/')
 for s in suffix:
  if os.path.lexists(roots[0]/(stem+s)):
   assert not any(os.path.lexists(root/(stem+s)) for root in roots[1:])
assert fresh['overlay_inventory']=={'observed_olean_names':1681,'expected_names':1681,'inventory_issues':[],'cross_root_companion_intersections':[]}
for n in fresh['future_output_modules']:
 stem=n.replace('.','/')
 assert not os.path.lexists(p72/'src'/(stem+'.lean'))
 for s in suffix:
  for root in roots+[b/'lib',repo/'.lake/build/lib/lean']:assert not os.path.lexists(root/(stem+s))
print(json.dumps({'status':'PASS_READ_ONLY_INDEPENDENT_REVIEW','recorded_producers':[13,17],'recorded_direct_edges':86,'guard_slots':1220,'inventory_names':54,'suffixes':len(suffix),'overlay_olean_names':len(names),'frozen_tmp_free_bytes':frozen['tmp_free_bytes'],'fresh_tmp_free_bytes':fresh['tmp_free_bytes'],'scope':'Existing-root and historical-route observation only; no Lean path resolution, future-root verification, package/dynamic closure, or build readiness.'},indent=2))
