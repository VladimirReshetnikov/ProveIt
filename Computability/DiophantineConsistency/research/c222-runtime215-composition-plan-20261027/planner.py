"""Metadata-only runtime composition union; no overlay, compiler or Git.
The four Frame constants are filled only from ROOT's accepted freeze notice.
"""
from pathlib import Path
import copy,hashlib,json,re,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=R/'Computability/DiophantineConsistency';REV=D/'reviews';HERE=Path(__file__).resolve().parent
FRAME_PACKET_SHA='f1a02e203c8d6371739a4f7e30a1e2c57ef6b5da52f0255131fb850e92f44b0d'
FRAME_MANIFEST_SHA='6396528358905da4c2d34062938ac6a2eb3b003c946c2c39201e03fb87b0a52b'
FRAME_RECEIPT_SHA='36a41c173b006dbb752b2147c555e41b0e399709cdb5c3d6f512e1819cfedfa3'
FRAME_PROVIDER='/tmp/control-frame215-root-90hncefu/lib'
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
def mf(p,sha):
 rows=load(p,sha);assert isinstance(rows,list)
 for x in rows:check(x)
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
def root_packet(stem,sha,manifest_sha):
 p=REV/(stem+'-root-replay.json');j=load(p,sha);assert j['status']=='PASS'
 m=mf(REV/(stem+'-root-replay/FILES.json'),manifest_sha)
 state=load(j['state']['path'],j['state']['sha256'])
 inp=load(state['inputs']['path'],state['inputs']['sha256'])
 for x in inp['pins']:check(x)
 for row in j['records']:
  assert row['exit_code']==0
  for k in ['source','snapshot','object','log','timing']:check(row[k])
 return j,inp,dict(packet=rec(p),manifest=m,state=j['state'],inputs=state['inputs'])

assert shutil.disk_usage('/tmp').free>=512*1024**2
assert 'PENDING_ROOT'not in [FRAME_PACKET_SHA,FRAME_MANIFEST_SHA,FRAME_RECEIPT_SHA,FRAME_PROVIDER]
basep=D/'research/c222-control-frame215-plan-20261027/cache-plan.json'
base=load(basep,'d0570b2d5abda25e5d4026fa9216f4e41cbb4d80ff17c91368cce973f56e595d')
base_mf=mf(basep.parent/'FILES.json','121f174d0cf117c5b336c7ec767d4dbe8053dc1dd3e89934f8b51d1b2897184e')
for x in base['authenticated_pins']:check(x)
mods={m['module']:copy.deepcopy(m)for m in base['modules']};base_names=set(mods)
bound={x['module']:copy.deepcopy(x)for x in base['external']}
frame,fi,fp=root_packet('arithmetic-control-frame215',FRAME_PACKET_SHA,FRAME_MANIFEST_SHA)
assert frame.get('provider',frame.get('private_provider'))==FRAME_PROVIDER
frame_receipt=check(dict(path=str(REV/'arithmetic-control-frame215-root.md'),sha256=FRAME_RECEIPT_SHA))
runtime,ri,rp=root_packet('arithmetic-dag-runtimeperm222',
 'ffb22a20778f060dbb4fe5f2440ee4d7e6509882878f0e8ce501f13810f83526',
 '053b5ca496ac89eb9244368497964bb6f8244c0ebaee84c85aabf53fca7e1a2a')
bisim,bi,bp=root_packet('arithmetic-control-bisim-perm215',
 '4dac153721bc15d83f4436031a6fa32ed9a8bdfacc384692ce29af969f8eea29',
 '6fd9249160c862daeb34b2530d415ade959d56dada8bb65c19d845504be86c68')
assert runtime['private_provider']=='/tmp/dag-runtimeperm222-root-lxpl7_mz/lib'
assert bisim['private_provider']=='/tmp/control-bisim-perm215-root-1czao7t5/lib'
for name in ['arithmetic-dag-runtimeperm222-root.md','arithmetic-control-bisim-perm215-root.md']:check(rec(REV/name))
overlaps=[];added=[]
def merge(rows,parent):
 for old in rows:
  m=copy.deepcopy(old);n=m['module'];check(m['source'])
  for x in m['objects']:check(x)
  if n in mods:
   a=mods[n];assert a['source']['sha256']==m['source']['sha256'],('source overlap',n)
   artifacts=lambda x:{''.join(Path(v['path']).suffixes):v['sha256']for v in x['objects']}
   assert artifacts(a)==artifacts(m),('object overlap',n)
   overlaps.append(dict(module=n,parent=parent,selected_source=a['source'],selected_objects=a['objects'],
     alternate_source=m['source'],alternate_objects=m['objects'],all_artifact_bytes_equal=True))
  else:
   m['parent_inventory']=parent;mods[n]=m;added.append(n)
merge(ri['profile']['modules'],rp['inputs']);merge(bi['modules'],bp['inputs'])

def leaf(packet,parent,wanted,replace=False):
 row=next(x for x in packet['records']if x['module']==wanted)
 if replace:
  prior=mods[wanted];assert prior['source']['sha256']==row['source']['sha256']and not prior['objects']
 else:assert wanted not in mods;prior=None
 mods[wanted]=dict(module=wanted,source=row['source'],objects=[row['object']],
  actual_imports=imports(row['source']['path']),parent=parent,historical_provenance=row,
  replaced_pre_refresh_record=prior,action='CACHED_ACCEPTED_CURRENT_ROOT')
leaf(runtime,rp['packet'],'BusyBeaver.ZFC.ArithmeticPositiveSimulation254',True)
leaf(runtime,rp['packet'],'BusyBeaver.ZFC.ArithmeticDagRuntimePerm222')
leaf(bisim,bp['packet'],'BusyBeaver.ZFC.ArithmeticControlBisimPerm215')
leaf(frame,fp['packet'],'DiophantineConsistency.ArithmeticControlFrame215')
for inp,external in [(ri,ri['profile']['external']),(bi,bi['external'])]:
 assert inp['compiler']['sha256']==base['compiler']['sha256']
 for x in external:
  assert x['module']in bound
  primary=x.get('object',x);check(primary)
  assert primary['sha256']==bound[x['module']]['object']['sha256']
  for o in x.get('companion_observations',[]):
   check(o);assert o['sha256']in {a['sha256']for a in bound[x['module']]['companion_observations']}

direct=['DiophantineConsistency.ArithmeticControlFrame215','BusyBeaver.ZFC.ArithmeticControlBisimPerm215',
 'BusyBeaver.ZFC.ArithmeticDagRuntimePerm222']
order=[];seen=set();active=set();used=set()
def visit(n):
 if n in seen:return
 if n not in mods:assert n in bound,n;used.add(n);return
 assert n not in active,n;active.add(n);m=mods[n];check(m['source'])
 actual=imports(m['source']['path']);assert actual==m.get('actual_imports',m.get('imports')),n
 m['actual_imports']=actual;assert m['objects']and not m.get('refresh',False),n
 for child in actual:visit(child)
 for x in m['objects']:check(x)
 active.remove(n);seen.add(n);order.append(n)
for n in direct:visit(n)
assert seen==set(mods),(set(mods)-seen)
external=[bound[n]for n in sorted(used)];providers=[];relative=set()
for n in order:
 for obj in mods[n]['objects']:
  rel=str(Path(*n.split('.')).with_suffix(''.join(Path(obj['path']).suffixes)))
  assert rel not in relative;relative.add(rel)
  providers.append(dict(module=n,relative_path=rel,provider=check(obj),kind='selected cached artifact; no overlay'))
for m in external:
 if 'source'in m:check(m['source'])
 for obj in [m['object'],*m['companion_observations']]:
  check(obj);rel=Path(*m['module'].split('.')).with_suffix(''.join(Path(obj['path']).suffixes))
  assert str(rel)not in relative;relative.add(str(rel))
  first=next((Path(p)/rel for p in base['package_paths']if(Path(p)/rel).is_file()),None)
  assert first is not None and rec(first)['sha256']==obj['sha256'],m['module']
  providers.append(dict(module=m['module'],relative_path=str(rel),provider=check(rec(first)),kind='actual first package artifact'))
assert not any(p.endswith('/Proofs/.lake/build/lib/lean')for p in base['package_paths'])
counts=dict(cached_custom=len(order),Foundation=sum(n.startswith('Foundation.')for n in order),
 cached_artifacts=sum(len(mods[n]['objects'])for n in order),boundary_primaries=len(external),
 boundary_companions=sum(len(m['companion_observations'])for m in external),
 selected_first_artifact_providers=len(providers),refresh=0,proposed_new_leaves=2)
assert counts==dict(cached_custom=207,Foundation=95,cached_artifacts=492,boundary_primaries=41,
 boundary_companions=123,selected_first_artifact_providers=656,refresh=0,proposed_new_leaves=2),counts
for x in [base['compiler'],rec(HERE/'PROPOSAL.md'),rec(__file__)]:check(x)
for x in list(pins.values()):check(x)
free=shutil.disk_usage('/tmp').free;assert free>=512*1024**2
result=dict(status='READ_ONLY_NO_LEAN_OVERLAY_OR_REFRESH',direct_imports=direct,counts=counts,
 modules=[mods[n]for n in order],topological_order=order,external=external,first_providers=providers,
 package_paths=base['package_paths'],compiler=base['compiler'],base=rec(basep),base_manifest=base_mf,
 accepted_frame=fp,accepted_frame_receipt=frame_receipt,accepted_runtime=rp,accepted_bisim=bp,
 added_cached_runtime_modules=added,overlap_observations=overlaps,
 inherited_unequal_kzip='Historical alternative retained in Frame base; current accepted selection unchanged.',
 generic_transport='The previously refreshed ec9c249... source is now reused with accepted ROOT 763a59f0... object; no new refresh.',
 proposal=rec(HERE/'PROPOSAL.md'),planner=rec(__file__),authenticated_pins=list(pins.values()),
 observations=observations,free_bytes_observed=free,reserve_bytes=512*1024**2,
 qualification='All three accepted ROOT mains selected; no proof implementation, overlay, compiler or Git operation.')
(HERE/'cache-plan.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(counts=counts,added=added,overlap_comparisons=len(overlaps),observations=observations,
 unique_paths=len(pins),free_bytes=free,plan=rec(HERE/'cache-plan.json')),indent=2))
