#!/usr/bin/env python3
"""Derive a fixed source/route plan from the independently audited observation; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;ROOT=P.parents[3];D=ROOT/'Computability/DiophantineConsistency';R=D/'research'
OBS=R/'current14-coherent-extension-preflight/observation.json';AUDIT=D/'reviews/current14-coherent-extension-preflight-independent/check.py';RESULT=AUDIT.parent/'result.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(q,msg):
 if not q:raise RuntimeError(msg)
need(sha(OBS)=='f06cd481f1fbeb537cc2b7ce60e406e8e92f514cc5fbf678a805b82478fc4db3','observation pin')
need(sha(AUDIT)=='a59fe861b7dff4ff9d644901de1de58d89e151a74b58bed388c50c8a99126ae6','auditor pin')
need(sha(RESULT)=='255a244abfa1606b2f08a87b638e864b4898416402412490a5a74550a4c82eb4','audit result pin')
x=json.loads(OBS.read_text());audit=json.loads(RESULT.read_text());need(audit['status']=='PASS_INDEPENDENT_OBSERVATION_AUDIT','independent audit status');need(x['status']=='OBSERVATION_NOT_BUILD_READINESS','observation status')
fresh_manifest=R/'current14-standard-fresh-rebuild-preflight/snapshot-manifest.json';f=json.loads(fresh_manifest.read_text());base=set(f['order']);order=x['union']['observed_union_topological_order'];need(len(order)==490 and len(set(order))==490 and not (set(order)&base),'union inventory')
tracked=set(subprocess.check_output(['git','ls-files','-z'],cwd=ROOT,timeout=30).decode().split('\0'));head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True,timeout=30).strip();dirty=set(subprocess.check_output(['git','diff','--name-only',head,'--'],cwd=ROOT,text=True,timeout=30).splitlines());q=x['quoted']['traced'];host=x['host']['sources'];entries=[]
for n in order:
 a=host.get(n);z=q.get(n)
 if a:
  path=a['path'];h=a['sha256'];imports=a['imports'];kind='host' if not z else 'host-and-quote'
  if z:need(h==z['source_sha256'],'intersection source drift '+n)
 else:
  need(z is not None,'missing source record '+n);h=z['source_sha256'];imports=[v for v in z['dependencies'] if v!='Init'];kind='quote'
  choices=[p for p in z['workspace_source_copies'] if p in tracked and p not in dirty and (ROOT/p).is_file() and sha(ROOT/p)==h];need(choices,'no clean tracked copy '+n);path=min(choices,key=lambda p:(len(p),p))
 need(path in tracked and path not in dirty and (ROOT/path).is_file() and sha(ROOT/path)==h,'current source drift '+n)
 need(len(imports)==len(set(imports)),'duplicate declared import '+n)
 entries.append({'module':n,'source':path,'source_sha256':h,'imports':imports,'origin':kind,'old_parent_status':z['parent_status'] if z else None})
seen=set()
for r in entries:
 for dep in r['imports']:
  if dep in order:need(dep in seen,'non-topological '+r['module']+' '+dep)
 seen.add(r['module'])
# Existing external point pins are for direct imports only; not package closure.
ext={}
def add(n,path,h):
 if n in ext:need(ext[n]['realpath']==path and ext[n]['sha256']==h,'external route conflict '+n)
 else:ext[n]={'realpath':path,'sha256':h}
for n,v in x['host']['external_observed'].items():add(n,v['realpath'],v['sha256'])
for r in q.values():
 for n,v in r['dependencies'].items():
  if n not in seen and n not in base:add(n,v['path'],v['sha256'])
need(len(ext)==99,'external inventory')
need(sum(r['old_parent_status']=='FAILED' for r in entries)==7,'partial-parent inventory')
print(json.dumps({'schema':'current14-coherent-extension-plan-v1','observation_sha256':sha(OBS),'review_sha256':sha(AUDIT),'review_result_sha256':sha(RESULT),'fresh_manifest_sha256':sha(fresh_manifest),'source_selection_head':head,'entries':entries,'external_direct':ext,'scope':'490 source-pinned project stages; direct external pins only; no Lean, package-transitive or dynamic-load guarantee.'},sort_keys=True,indent=2))
