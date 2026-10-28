"""Read-only accepted EnumSoundness/Runtime union: metadata only, no overlay or Lean."""
from pathlib import Path
import copy,hashlib,json,re,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency';REV=D/'reviews';HERE=Path(__file__).resolve().parent
pins={};observations=0
def rec(p):
 p=Path(p);p=p if p.is_absolute()else R/p;b=p.read_bytes()
 return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def check(x):
 global observations
 a=rec(x['path']);assert a['sha256']==x['sha256'],(x,a)
 if 'bytes'in x:assert a['bytes']==x['bytes'],x
 pins[a['path']]=a;observations+=1;return a
def load(p,sha):
 a=check(dict(path=str(p),sha256=sha));return json.loads(Path(a['path']).read_text())
def manifest(p,sha,relative=False):
 d=load(p,sha);rows=d['files']if isinstance(d,dict)else d
 for x in rows:check(dict(x,path=str(Path(p).parent/x['path']))if relative else x)
 return rec(p)
def imports(p):
 s=Path(p).read_text();out=[];i=depth=0
 while i<len(s):
  pair=s[i:i+2]
  if depth:
   if pair=='/-':depth+=1;i+=2
   elif pair=='-/':depth-=1;i+=2
   else:out.append('\n'if s[i]=='\n'else' ');i+=1
  elif pair=='/-':depth=1;i+=2
  elif pair=='--':
   while i<len(s)and s[i]!='\n':i+=1
  else:out.append(s[i]);i+=1
 assert depth==0,p
 return list(dict.fromkeys(['Init']+[n for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',''.join(out),re.M)for n in line.split()]))
assert shutil.disk_usage('/tmp').free>=512*1024**2
assert not (HERE/'cache-plan.json').exists()
basep=D/'research/c222-runtime215-composition-plan-20261027/cache-plan.json'
base=load(basep,'4a93686eebfefcd2b325e88a9644e9a7aad5f8a45e4744bafb287959377ebb34')
basemf=manifest(basep.parent/'FILES.json','6419d84589931c450ac7ea94915c50285bf0457ed14111bcd2356b55179ad4b6')
for x in base['authenticated_pins']:check(x)
mods={m['module']:copy.deepcopy(m)for m in base['modules']};bound={m['module']:copy.deepcopy(m)for m in base['external']}
rp=REV/'arithmetic-runtime215-root-replay.json'
runtime=load(rp,'a88c9098980cc33de0d57bf2485fd2c7b944327fbaa59c6d2308102361315ccb')
rmf=manifest(REV/'arithmetic-runtime215-root-replay/FILES.json','60931483af9d656b0f44c71f71c423350de2e4587b817106adb2fd6b4ca6912a')
assert runtime['status']=='PASS'and runtime['provider']=='/tmp/runtime215-root-_hxbq4kn/lib'
rs=load(runtime['state']['path'],runtime['state']['sha256']);ri=load(runtime['inputs']['path'],runtime['inputs']['sha256'])
for x in ri['pins']:check(x)
for x in ri['actual_providers']:check(x['expected']);check(x['actual'])
check(runtime['driver']);check(rec(REV/'arithmetic-runtime215-root.md'))
ep=REV/'arithmetic-enum-soundnessperm222-root-replay/ROOT.json'
enum=load(ep,'a0d9458b24b527c9ceb271b52abc82f4b0763a7e141567c0478c58bb7665f78a')
emf=manifest(ep.parent/'FILES.json','3408cd04c8060b95c2d734ae58b0084e8732d999146c99850e932baaf5c5d0a2',True)
assert enum['status']=='PASS'and enum['private']=='/tmp/enum-soundnessperm222-root-peer-wmzrngb7'
ei=load(enum['inputs']['path'],enum['inputs']['sha256'])
for x in ei['pins']:check(x)
check(enum['driver']);check(rec(REV/'arithmetic-enum-soundnessperm222-root.md'))
assert ei['counts']==dict(custom=145,Foundation=95,artifacts=430,external=38)
assert ei['compiler']['sha256']==base['compiler']['sha256']==ri['compiler']['sha256']
for p in [runtime,enum]:
 for row in p['records']:
  assert row['exit_code']==0
  for key in ['source','snapshot','object','log','timing']:check(row[key])
overlap=[];added=[]
def arts(m):return {''.join(Path(x['path']).suffixes):x['sha256']for x in m['objects']}
for raw in ei['modules']:
 m=copy.deepcopy(raw);n=m['module']
 assert isinstance(m['source'],str)
 oldsource=dict(path=m['source'],sha256=m['source_sha256']);m['source']=check(oldsource)
 m['legacy_source_record']=oldsource;m['actual_imports']=m['imports'];m['parent_inventory']=enum['inputs']
 assert imports(m['source']['path'])==m['actual_imports'],n
 for x in m['objects']:check(x)
 if n in mods:
  current=mods[n];assert current['source']['sha256']==m['source']['sha256']and arts(current)==arts(m),n
  overlap.append(dict(module=n,selected_source=current['source'],selected_objects=current['objects'],alternate_legacy_record=raw,all_artifacts_equal=True))
 else:mods[n]=m;added.append(n)
assert len(overlap)==122 and len(added)==23
for packet,name,provider in [(runtime,'DiophantineConsistency.ArithmeticRuntime215',runtime['provider']),
 (enum,'DiophantineConsistency.ArithmeticEnumSoundnessPerm222',enum['private']+'/lib')]:
 row=next(x for x in packet['records']if x['module']==name);assert name not in mods
 obj=check(row['object']);assert obj['path']==str(Path(provider)/Path(*name.split('.')).with_suffix('.olean'))
 mods[name]=dict(module=name,source=check(row['source']),objects=[obj],actual_imports=imports(row['source']['path']),action='CACHED_ACCEPTED_ROOT_MAIN',historical_provenance=row)
legacy_boundary=[];legacy_pins={(x['path'],x['sha256'])for x in ei['pins']}
for name in ei['external_imports']:
 assert name in bound,name
 m=bound[name]
 for x in [m['object'],*m['companion_observations']]:
  rel=Path(*name.split('.')[:-1])/Path(x['path']).name
  actual=next((Path(q)/rel for q in ei['lean_path'].split(':')if(Path(q)/rel).is_file()),None)
  assert actual is not None,name
  a=check(dict(x,path=str(actual)));check(x)
  legacy_boundary.append(dict(module=name,selected_runtime_record=x,legacy_search_provider=a,
   historically_pinned_in_enum=(str(actual),a['sha256'])in legacy_pins or(x['path'],a['sha256'])in legacy_pins,
   qualification='Current byte comparison against accepted Runtime boundary; missing historical companion capture is not inferred.'))
direct=['DiophantineConsistency.ArithmeticEnumSoundnessPerm222','DiophantineConsistency.ArithmeticRuntime215']
order=[];seen=set();active=set();used=set()
def visit(n):
 if n in seen:return
 if n not in mods:assert n in bound,n;used.add(n);return
 assert n not in active,n;active.add(n);m=mods[n];check(m['source'])
 actual=imports(m['source']['path']);assert actual==m.get('actual_imports',m.get('imports')),n
 assert m['objects']and not m.get('refresh',False),n;m['actual_imports']=actual
 for child in actual:visit(child)
 for x in m['objects']:check(x)
 active.remove(n);seen.add(n);order.append(n)
for n in direct:visit(n)
assert seen==set(mods)and used==set(bound)
providers=[];relative=set();external=[bound[n]for n in sorted(used)]
for n in order:
 for x in mods[n]['objects']:
  rel=str(Path(*n.split('.')).with_suffix(''.join(Path(x['path']).suffixes)));assert rel not in relative;relative.add(rel)
  providers.append(dict(module=n,relative_path=rel,provider=check(x),kind='selected immutable cached object; no overlay'))
for m in external:
 if 'source'in m:check(m['source'])
 for x in [m['object'],*m['companion_observations']]:
  rel=Path(*m['module'].split('.')).with_suffix(''.join(Path(x['path']).suffixes));assert str(rel)not in relative;relative.add(str(rel))
  actual=next((Path(q)/rel for q in base['package_paths']if(Path(q)/rel).is_file()),None)
  assert actual is not None
  providers.append(dict(module=m['module'],relative_path=str(rel),provider=check(dict(x,path=str(actual))),kind='actual first package artifact'))
assert all('/.lake/packages/'in x or x=='/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean'for x in base['package_paths'])
counts=dict(cached_custom=len(order),Foundation=sum(n.startswith('Foundation.')for n in order),cached_artifacts=sum(len(mods[n]['objects'])for n in order),boundary_primaries=len(external),boundary_companions=sum(len(m['companion_observations'])for m in external),selected_first_artifact_providers=len(providers),refresh=0,proposed_new_leaves=2)
assert counts==dict(cached_custom=232,Foundation=95,cached_artifacts=517,boundary_primaries=41,boundary_companions=123,selected_first_artifact_providers=681,refresh=0,proposed_new_leaves=2),counts
proposal=check(rec(D/'research/arithmetic-checker-machine215-proposal.md'));readme=check(rec(HERE/'README.md'));check(rec(__file__));check(base['compiler'])
for x in list(pins.values()):check(x)
assert shutil.disk_usage('/tmp').free>=512*1024**2
result=dict(status='READ_ONLY_NO_LEAN_OVERLAY_OR_REFRESH',direct_imports=direct,counts=counts,modules=[mods[n]for n in order],topological_order=order,external=external,first_providers=providers,package_paths=base['package_paths'],compiler=base['compiler'],base=rec(basep),base_manifest=basemf,accepted_runtime=dict(packet=rec(rp),manifest=rmf,inputs=runtime['inputs'],provider=runtime['provider']),accepted_enum=dict(state=rec(ep),manifest=emf,inputs=enum['inputs'],provider=enum['private']+'/lib'),overlaps=overlap,enum_only_modules=added,legacy_enum_boundary_crosschecks=legacy_boundary,inherited_kzip_qualification='Source-identical unequal historical KZip alternative retained in Runtime/Frame ancestry; accepted Runtime selection unchanged.',proposal=proposal,readme=readme,planner=rec(__file__),authenticated_pins=list(pins.values()),observations=observations,unique_paths=len(pins),free_bytes_observed=shutil.disk_usage('/tmp').free,reserve_bytes=512*1024**2,qualification='Exact two accepted ROOT mains retained; no new source, compiler, overlay, refresh, or Git mutation. Type0 closed IΣ1/PA client only; source-ZFC and polynomial/HA endpoints separate.')
(HERE/'cache-plan.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(counts=counts,overlap=len(overlap),added=added,legacy_boundary_observations=len(legacy_boundary),legacy_boundary_unrecorded=sum(not x['historically_pinned_in_enum']for x in legacy_boundary),observations=observations,unique_paths=len(pins),plan=rec(HERE/'cache-plan.json')),indent=2))
