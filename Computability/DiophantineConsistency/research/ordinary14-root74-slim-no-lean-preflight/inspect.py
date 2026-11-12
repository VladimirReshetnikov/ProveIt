#!/usr/bin/env python3
"""Read-only observations; this program cannot launch Lean and always refuses readiness."""
import hashlib,json,os,platform,sys
from pathlib import Path

D=Path(__file__).resolve().parents[2]; ROOT=D.parents[1]
P=D/'research/ordinary14-root74-slim-overlay'
P72=Path('/tmp/p72-current-base-extension-attempt02-20261105/lib')
BASE=Path('/tmp/current14-standard-fresh-build-20261104/lib')
PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
TOOL=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
LEAN=TOOL.parent.parent/'bin/lean'
OUT=Path('/tmp/root74-slim-guarded-build-new')
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash',
          '.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash','.so','.dll','.dylib')
PINS={
 P/'check_source.py':'6c8b79ea7ff66ab7f9e002f5f997426cf57fe2352a1a2528ecdc053899dde205',
 P/'inventory.json':'b3317a1aa674fd67708aef94685af953126fcd1f30ead3bd43a9afb95467583e',
 P/'README.md':'34b9bca6667fe214a34a5a33475c826e5dd69f1dfd4f8df0edfffd9eabf48804',
 D/'reviews/ordinary14-root74-slim-overlay-independent/check.py':'599767e988b611dae62becdf6a590dbf01ec264a251fc98d7084e654879f0553',
 D/'reviews/ordinary14-root74-slim-overlay-independent/observation.json':'c877168d127fc625b21a99e6ee36041af53b79dbcee9fab4dedaac8125c9753c',
 D/'research/ordinary14-root74-provider-survey/inspect.py':'f7d17a0b459c783d9a02540c1a8d0c66b38575fdda7e046e9b3a5777dc2a172d',
 D/'research/ordinary14-root74-provider-survey/observation.json':'14732a54d8f2d3592d31f78d731497a1d804780ca8ec643e3851314868e7b4ab',
 P72.parent/'progress.json':'f4bbe5f0b543497d543f243e10d8ead6d778cc3d0bf0aec96dfa73f7e622dd5a',
 P72.parent/'source-snapshot.json':'4536c44c399dc42037b692a39a36cc74c807693e1e5a76e2f5db299691fff7d8',
 BASE.parent/'state.json':'f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014',
 ROOT/'lean-toolchain':'2773c517aa90b66ea8a2c52bddddf84393157797f8341be0df45294fff7fd32e',
 ROOT/'lake-manifest.json':'95e215b005fe9aacc1e5490c781d57e3044d2da5ca452495cfcd0e4eff908665',
 LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
 P72/'DiophantineConsistency/ModelDifferenceRing.olean':'e52ed546fa3f94d9c3b823ad19286c4c906359efa26c1d67543e9dbfc0f2ecf0',
 P72/'DiophantineConsistency/Compact44/CompactMaskBoundFinish.olean':'ed50724acfc78ac724dfa32b3d04a58802d3ec998de4d90ba5bc4cc60cab93ce',
 P72/'DiophantineConsistency/Compact44/CompactSymbolicPorts.olean':'8877e3a4d8f3866144618efa5070decf6155f77f636692d166d8de9a858bc6ba',
 P72/'DiophantineConsistency/ArithmeticStandardCasts.olean':'c992bafb003c67229c756a634d31c11ecfb942839904367554488ba27ddc597a',
 P72/'DiophantineConsistency/ArithmeticAdaptiveFactorUnits2011.olean':'e357624f5ab38852b316b0b492050dbc1ae4c0f90c90fc8cb0481c9061529f65',
 P72/'DiophantineConsistency/ArithmeticNegativeNorms.olean':'33cf47041c950f77cd4535d629dcddfa27ff9ea1fcd21cc1af0fb732dd5eb319',
 TOOL/'Init.olean':'d2e85d72099f9d869c9582aad5fb13079968d9d121ac6061e8326b00800b306e',
}
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def main():
 if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):
  raise RuntimeError('use python3 -I -S -B')
 pins=[]
 for path,expected in PINS.items():
  actual=sha(path);pins.append({'path':str(path),'realpath':str(path.resolve(strict=True)),'sha256':actual,'matches':actual==expected})
 inv=json.loads((P/'inventory.json').read_text())
 draft=inv['drafts_topological']; assert len(draft)==159
 sources=[]
 for r in draft:
  for kind,path,want in [('overlay',P/r['path'],r['overlay_sha256']),('original',D/r['source_path'],r['source_sha256'])]:
   actual=sha(path)
   if actual!=want:sources.append({'kind':kind,'path':str(path),'sha256':actual,'expected':want})
 for name,r in inv['project_sources'].items():
  path=D/r['path'];actual=sha(path)
  if actual!=r['sha256']:sources.append({'kind':'lexical_project','module':name,'path':str(path),'sha256':actual,'expected':r['sha256']})
 roots=[P72,BASE,PKG,TOOL,ROOT/'.lake/build/lib/lean']
 names=[r['module'] for r in draft]+['DiophantineConsistency.Compact44.FreeJ13','DiophantineConsistency.Compact44.FreeJ13Halt','DiophantineConsistency.DiscreteOrderedRingFacts']
 collisions=[]
 for root in roots:
  for name in names:
   for suffix in SUFFIXES:
    path=root/(name.replace('.','/')+suffix)
    if os.path.lexists(path):collisions.append({'root':str(root),'module':name,'suffix':suffix,'path':str(path),'realpath':str(path.resolve(strict=False))})
 root_paths=[]
 for root in roots:
  root_paths.append({'path':str(root),'exists':root.exists(),'realpath':str(root.resolve(strict=False))})
 stat=os.statvfs('/tmp');free=stat.f_bavail*stat.f_frsize
 memline=next(x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:'))
 mem=int(memline.split()[1])*1024
 live=[];proc_errors=[]
 for p in Path('/proc').iterdir():
  if not p.name.isdigit():continue
  try:
   if (p/'comm').read_text().strip()=='lean':live.append(int(p.name))
  except FileNotFoundError:pass
  except (PermissionError,OSError) as e:proc_errors.append({'pid':p.name,'error':type(e).__name__})
 init_pkg=PKG/'Init.olean'; init_core=TOOL/'Init.olean'
 return {'status':'REFUSED_NOT_LAUNCH_READY','can_launch':False,'scope':'read-only sampled observations; no lock acquired, Lean not invoked, no files created',
  'constants':{'disk_free_must_exceed_bytes':5100000000,'host_mem_available_min_bytes':10*1024**3,'session_rss_stop_bytes':4*1024**3,'stage_timeout_seconds':180,'run_timeout_seconds':21600,'monitor_sample_seconds':0.2},
  'platform':{'system':platform.system(),'machine':platform.machine()},'disk':{'path':'/tmp','available_bytes':free,'above_floor':free>5100000000},
  'host_memory':{'available_bytes':mem,'at_least_floor':mem>=10*1024**3},'observed_lean_pids':sorted(live),'proc_errors':proc_errors,
  'proposed_output':str(OUT),'output_exists_or_is_symlink':os.path.lexists(OUT),'source_mismatches':sources,
  'pins':pins,'candidate_roots':root_paths,'init':{'package_path':str(init_pkg),'package_realpath':str(init_pkg.resolve(strict=True)),'core_realpath':str(init_core.resolve(strict=True)),'same_realpath':init_pkg.resolve(strict=True)==init_core.resolve(strict=True)},
  'collision_check':{'names_count':len(names),'suffixes':list(SUFFIXES),'roots':[str(r) for r in roots],'hits':collisions,'scope':'same-name presence, not proof of actual resolution or incompatibility; source and external transitive dependencies not checked'},
  'resolution_expectations':{'p72_root_exact':str(P72.resolve(strict=True))==str(P72),'base_root_exact':str(BASE.resolve(strict=True))==str(BASE),'package_root_exact':str(PKG.resolve(strict=True))==str(PKG),'tool_root_exact':str(TOOL.resolve(strict=True))==str(TOOL),'standard_casts_uses_base':(P72/'DiophantineConsistency/ArithmeticStandardCasts.olean').resolve(strict=True)==(BASE/'DiophantineConsistency/ArithmeticStandardCasts.olean').resolve(strict=True)},
  'unconditional_blockers':['no external shared Lean-slot allocation or atomic exclusion acquired','no reviewed executable runner or approved stage plan','transitive provider/package/runtime ancestry and all companion inputs not authenticated or immutable','actual Lean import resolution and guarded lean --deps have not been checked','fresh isolated source/output roots have not been created and verified','independent prelaunch review and postflight/axiom replay have not occurred']}
try:
 result=main()
except Exception as e:
 result={'status':'REFUSED_INSPECTION_ERROR','can_launch':False,'error_type':type(e).__name__,'error':str(e),'scope':'read-only; Lean not invoked'}
print(json.dumps(result,sort_keys=True,indent=2))
sys.exit(1)
