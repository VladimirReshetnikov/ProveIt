#!/usr/bin/env python3
"""Source-declared P13/P14 closure versus frozen current14 base; no Lean."""
import contextlib,hashlib,io,json,runpy,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];root=next(p for p in D.parents if (p/'lakefile.toml').is_file());scan=D/'research/nine-variable-ipra/bounded-build-preflight/scan.py';manifest=D/'research/current14-standard-fresh-rebuild-preflight/snapshot-manifest.json'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
need(sha(scan)=='d72f3242ff991ad537217b8b25c3cde4ab091a06ce45f61d4f92f70886848816' and sha(manifest)=='1e8b03cac1b2db995091dff13c749faf955fc524bf2da42a637743e9d7a53749' and sha(root/'lakefile.toml')=='a378413000dd01d021315457d6c569202cca123f99dd224774e951fef3ec9b4f','input pins')
with contextlib.redirect_stdout(io.StringIO()):x=runpy.run_path(str(scan))
base=json.loads(manifest.read_bytes());targets=['DiophantineConsistency.Compact44.IPRAOrdinary72','DiophantineConsistency.Compact44.IPRAOrdinary72P14'];records={};external=set();missing={}
for target in targets:
 a,b,c=x['graph'](target);external|=c;missing.update(b)
 for n,r in a.items():need(n not in records or records[n]==r,'conflicting source '+n);records[n]=r
need(not missing,'missing sources '+repr(missing));shared=set(records)&set(base['sources']);extra=set(records)-shared
for n in shared:need(records[n]['source_sha256']==base['sources'][n]['sha256'] and records[n]['imports']==base['sources'][n]['imports'],'shared drift '+n)
active=set();done=set();order=[]
def visit(n):
 if n in done:return
 need(n not in active,'import cycle '+n);active.add(n)
 for dep in records[n]['imports']:
  if dep in records:visit(dep)
 active.remove(n);done.add(n)
 if n in extra:order.append(n)
for t in targets:visit(t)
need(set(order)==extra and len(order)==len(extra),'topological order')
for n,r in records.items():need(sha(root/r['source'])==r['source_sha256'],'post-scan source drift '+n)
need(sha(scan)=='d72f3242ff991ad537217b8b25c3cde4ab091a06ce45f61d4f92f70886848816' and sha(manifest)=='1e8b03cac1b2db995091dff13c749faf955fc524bf2da42a637743e9d7a53749','post-scan input drift')
print(json.dumps({'status':'PASS_SOURCE_SURVEY_ONLY','targets':targets,'project_count':len(records),'base_shared':len(shared),'extension_count':len(extra),'shared_source_drift':0,'new_declared_externals':sorted(external-set(base['external_modules'])),'all_declared_externals':sorted(external),'extension_order':order,'project_sources':dict(sorted(records.items())),'scope':'Source-declared closure and same-source comparison only; no fresh build, object authentication, package transitive closure, or dynamic ancestry.'},indent=2,sort_keys=True))
