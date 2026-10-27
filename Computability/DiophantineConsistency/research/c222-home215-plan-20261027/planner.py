"""Read-only exact Home cache audit; no overlay, compiler or dependency mutation."""
from pathlib import Path
import copy,hashlib,json,re,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=R/'Computability/DiophantineConsistency'
H=Path(__file__).resolve().parent
pins={};observations=0
def rec(p):
 p=Path(p);p=p if p.is_absolute()else R/p;b=p.read_bytes()
 return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def check(x):
 global observations
 a=rec(x['path']);assert a['sha256']==x['sha256'],(x,a)
 if 'bytes'in x:assert a['bytes']==x['bytes']
 pins[a['path']]=a;observations+=1;return a
def load(p,sha):
 check(dict(path=str(p),sha256=sha));return json.loads(Path(p).read_text())
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
 assert depth==0
 return list(dict.fromkeys(['Init']+[n for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',''.join(out),re.M)for n in line.split()]))
basep=D/'research/c222-symbolic-core215-plan-20261027/cache-plan.json'
base=load(basep,'821bf1b4e5d124858d5eb0c6d5540a37a2a2b0299e6fa385d04957890d9660aa')
for x in base['authenticated_pins']:check(x)
rootp=D/'reviews/arithmetic-symbolic-core215-root-replay.json'
root=load(rootp,'8102b4470b0f939c6f88ff551eb5a41d165be8113f3cc8c000b538c2059dce26')
rootmf=D/'reviews/arithmetic-symbolic-core215-root-replay/FILES.json'
for x in load(rootmf,'867910edf7f17797ebb39808990fc5074e95f96427a0e707aaf8052f3a0ad12f'):check(x)
rootreceipt=D/'reviews/arithmetic-symbolic-core215-root.md'
check(dict(path=str(rootreceipt),sha256='9825a5c806bd038f4fca31600c05669b80714c21b2ba62fe6628e7d92dade7d2'))
assert root['status']=='PASS'and root['provider']=='/tmp/symbolic-core215-root-d4b0mp1m/lib'
mods={m['module']:copy.deepcopy(m)for m in base['modules']}
for row in root['records']:
 if row['module'].endswith('Checks'):continue
 assert row['exit_code']==0
 for key in ['source','snapshot','object','log','timing']:check(row[key])
 assert row['object']['sha256']=='8fe5cb749c1cba56a9d9549b78b8ce4cf2dece464b0e711f05e4733630f6938d'
 mods[row['module']]=dict(module=row['module'],source=row['source'],objects=[row['object']],
  actual_imports=imports(row['source']['path']),provider='Accepted independent ROOT SymbolicCore',
  parent=rec(rootp),historical_provenance=row)
peerp=D/'reviews/native-adaptive-current2011-peer-replay.json'
peer=load(peerp,'6661c2f42baa774e9e2844b23e4621ddff2dca161424be140c00c0b0d436db48')
peermf=D/'reviews/native-adaptive-current2011-peer-replay/FILES.json'
for x in load(peermf,'d7c08b0bbc1138055879d9387e67a4d59b007af5b9553e66ce0833ad372d03ae'):check(x)
assert peer['status']=='PASS';check(peer['inputs'])
native=json.loads(Path(peer['inputs']['path']).read_text())
nmods={m['module']:m for m in native['selected_custom']}
added=['BusyBeaver.ZFC.KHome','BusyBeaver.ZFC.FramedWindow','BusyBeaver.ZFC.KZipTape','BusyBeaver.ZFC.KHomeReady']
for n in added:
 m=nmods[n];assert n not in mods
 for key in ['source','object','original_object']:check(m[key])
 assert imports(m['source']['path'])==m['actual_imports']
 mods[n]=dict(module=n,source=m['source'],objects=[m['object']],actual_imports=m['actual_imports'],
  provider='Previously authenticated NativeAdaptiveCurrent peer cache',parent=rec(peerp),historical_provenance=m)
overlaps=[]
for n in ['BusyBeaver.ZFC.KZip','BusyBeaver.ZFC.KRuntimeCore']:
 a=mods[n];b=nmods[n]
 for x in [a['source'],*a['objects'],b['source'],b['object'],b['original_object']]:check(x)
 assert a['source']['sha256']==b['source']['sha256']
 overlaps.append(dict(module=n,current_source=a['source'],selected_objects=a['objects'],
  alternate_source=b['source'],alternate_object=b['object'],
  primary_bytes_equal=a['objects'][0]['sha256']==b['object']['sha256'],
  scope='Source-identical accepted overlap; unequal KZip bytes are explicitly retained, not claimed equal.'))
assert [x['primary_bytes_equal']for x in overlaps]==[False,True]
boundary={x['module']:copy.deepcopy(x)for x in base['external']}
direct=['DiophantineConsistency.ArithmeticSymbolicCore215','BusyBeaver.ZFC.KHomeReady']
seen=set();active=set();used=set();order=[]
def visit(n):
 if n not in mods:assert n in boundary,('unknown',n);used.add(n);return
 if n in seen:return
 assert n not in active;active.add(n);m=mods[n]
 check(m['source']);assert imports(m['source']['path'])==m['actual_imports'],n
 assert not m.get('refresh',False),n
 for child in m['actual_imports']:visit(child)
 for x in m['objects']:check(x)
 active.remove(n);seen.add(n);order.append(n)
for n in direct:visit(n)
assert set(mods)==seen
external=[boundary[n]for n in sorted(used)];providers=[]
for n in order:
 for x in mods[n]['objects']:providers.append(dict(module=n,provider=check(x),kind='selected cached artifact'))
for m in external:
 if 'source'in m:check(m['source'])
 for obj in [m['object'],*m['companion_observations']]:
  check(obj);suffix=''.join(Path(obj['path']).suffixes);rel=Path(*m['module'].split('.')).with_suffix(suffix)
  first=next((Path(p)/rel for p in base['package_paths']if(Path(p)/rel).is_file()),None)
  assert first is not None and rec(first)['sha256']==obj['sha256']
  providers.append(dict(module=m['module'],provider=check(rec(first)),kind='actual first package artifact'))
counts=dict(cached_custom=len(order),Foundation=sum(n.startswith('Foundation.')for n in order),
 cached_artifacts=sum(len(mods[n]['objects'])for n in order),boundary_primaries=len(external),
 boundary_companions=sum(len(m['companion_observations'])for m in external),
 selected_first_artifact_providers=len(providers),refresh=0,new_leaves=2)
assert counts==dict(cached_custom=153,Foundation=95,cached_artifacts=438,boundary_primaries=41,
 boundary_companions=123,selected_first_artifact_providers=602,refresh=0,new_leaves=2),counts
route=[check(rec(R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'/f'{n}.lean'))for n in ['KSim','KSites215','KTable215']]
check(base['compiler']);check(rec(H/'PROPOSAL.md'));check(rec(__file__));check(rec(H/'data-audit.py'))
audit=load(H/'data-audit.json','5607f1331ad19ffabb228d5ccafd0d23a7709227e8ab428e8995ad943038c2a1')
for x in [audit['source'],audit['script'],*audit['contracts']]:check(x)
for x in list(pins.values()):check(x)
assert shutil.disk_usage('/tmp').free>=512*1024**2
result=dict(status='READ_ONLY_NO_COMPILER_OR_OVERLAY',direct_imports=direct,counts=counts,
 modules=[mods[n]for n in order],topological_order=order,external=external,first_providers=providers,
 package_paths=base['package_paths'],compiler=base['compiler'],base=rec(basep),
 accepted_symbolic_root=rec(rootp),accepted_symbolic_manifest=rec(rootmf),accepted_symbolic_receipt=rec(rootreceipt),
 native_cache_peer=rec(peerp),native_cache_manifest=rec(peermf),native_overlap_observations=overlaps,
 added_cached_modules=added,route_sources_not_new_imports=route,data_audit=rec(H/'data-audit.json'),
 proposal=rec(H/'PROPOSAL.md'),planner=rec(__file__),observations=observations,authenticated_pins=list(pins.values()))
(H/'cache-plan.json').write_text(json.dumps(result,indent=2)+'\n')
(H/'FILES.json').write_text(json.dumps([rec(H/n)for n in ['PROPOSAL.md','data-audit.py','data-audit.json','planner.py','cache-plan.json']],indent=2)+'\n')
print(json.dumps(dict(counts=counts,observations=observations,unique_paths=len(pins),
 plan=rec(H/'cache-plan.json'),manifest=rec(H/'FILES.json'))))
