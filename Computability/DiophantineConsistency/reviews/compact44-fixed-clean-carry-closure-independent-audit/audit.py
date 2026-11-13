#!/usr/bin/env python3
"""No-Lean fixed clean-carry source/provider topology audit and parent rerun."""
import hashlib,json,os,pathlib,re,subprocess,sys
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('isolated nonoptimized Python required')
P=pathlib.Path;root=P.cwd();base=root/'Computability/DiophantineConsistency';plan=base/'research/ordinary12-ipra-bridge/compact44-fixed-clean-carry-closure-plan';parent=base/'reviews/compact44-rotation-windows-pair-independent-audit';provider=P('/tmp/ipra-rotation-windows-pair-01');old=P('/tmp/ipra-compact-clean-carry-pair-01');H=lambda p:hashlib.sha256(P(p).read_bytes()).hexdigest();scan_sha='d96b527d8a9fce9f187bfa404ed0c939090bbef09e0101b8db84a7f97c32a253';source_sha='24a985bb3ee9ce0b0e508245cdc386a40b1581e2b417902330fdb8b87418b378';compare_sha='1135b7406c62b1aa91310439716a94dd1688caea9536fee4027bd0580a6a9206';parent_script_sha='e8121e39678fcc42114500c92c1b294f2b26fc422569f2b7b70ac3341d09c387';parent_sha='7adb39a15c385f542ff5b8c34db7237a7edff25822d4e49aebdd104689745df0'
def gh(rev,p):return hashlib.sha256(subprocess.run(['git','show',rev+':'+p.relative_to(root).as_posix()],cwd=root,capture_output=True,check=True,timeout=60).stdout).hexdigest()
for p,h in [(plan/'scan.json',scan_sha),(plan/'scan.py',source_sha),(plan/'prior-provider-comparison.json',compare_sha)]:
 if H(p)!=h or gh('4c58391a77',p)!=h:raise ValueError(('plan drift',str(p)))
if H(parent/'audit.py')!=parent_script_sha or H(parent/'CHECK.json')!=parent_sha:raise ValueError('parent audit drift')
scan=json.loads((plan/'scan.json').read_bytes());obs=json.loads((plan/'terminal-observation.json').read_bytes());pa=json.loads((parent/'CHECK.json').read_bytes());pto=json.loads((parent/'terminal-observation.json').read_bytes());comp=json.loads((plan/'prior-provider-comparison.json').read_bytes())
if scan['status']!='PRELIMINARY_FIXED_CLEAN_CARRY_SOURCE_CLOSURE_NOT_A_BUILD' or scan['parent_audit_sha256']!=parent_sha or scan['parent_receipt_sha256']!='87bd0f6934145714f41f18e339f66b325bcb90f3da8fc44402ce3ff21b3d1e4d':raise ValueError('scan receipt')
if type(obs['observed_exit']) is not int or obs['observed_exit']!=0 or obs['optimized_exit']!=1 or obs['lean_launched'] is not False or obs['parent_audit_rerun'] is not False or obs['scan_sha256']!=scan_sha or pto['check_sha256']!=parent_sha or type(pto['observed_exit']) is not int or pto['observed_exit']!=0 or pa['status']!='PASS_INDEPENDENT_ROTATION_WINDOWS_PAIRED_ARTIFACT_AUDIT':raise ValueError('observation')
names=['CompactSymbolicGraphSaturation','CompactSameWitnessSaturation2','CompactPositionIncrement','CompactPositionGraph','CleanGeometry','CleanMaskClasses','CleanModelSupport','FixedGraphSupportCarry','CleanPhaseChoice','CleanTargetPhase','CleanPhaseNeighbors','CyclicPhaseTransport','CleanSafeSource','CyclicAnyPhase','FixedGraphSafeSource','TemporalShiftSplit','TemporalCleanNumerics','TemporalWindowFormula','TemporalOtherWindows','TemporalStraddleWindow','TemporalSourceNonwrap','TemporalSourceWrapped','TemporalSourceStraddle','TemporalSourceUnified','TemporalSourcePredecessor','TemporalSafeDigit','TemporalSafeCyclic','FixedGraphTemporalClean','CompactCarryReset','TemporalCarryReset','ConcreteCarryRoom','TemporalCarryExact','FixedGraphCleanCarry'];counts=[1,2,1,2,4,3,2,1,3,3,2,1,2,1,1,1,3,2,2,1,1,1,1,1,2,1,2,1,2,1,1,1,1];rows=scan['source_order'];allnames={'DiophantineConsistency.'+x for x in names};available=set();external=set();summaries=[]
if len(rows)!=33 or [r['module'] for r in rows]!=['DiophantineConsistency.'+x for x in names] or sum(counts)!=54:raise ValueError('source order')
for row,rc in zip(rows,counts):
 p=P(row['source']);s=p.read_text();imports=[l[7:] for l in s.splitlines() if l.startswith('import ')];reports=re.findall(r'^#print axioms\s+(\S+)',s,re.M)
 if H(p)!=row['source_sha256'] or gh(row['source_commit'],p)!=row['source_sha256'] or imports!=row['imports'] or reports!=row['axiom_reports'] or len(reports)!=rc:raise ValueError(('source/import/report drift',row['module']))
 for dep in imports:
  if dep not in available:
   if dep in allnames:raise ValueError(('forward import',dep))
   external.add(dep)
 available.add(row['module']);summaries.append({'module':row['module'],'sha256':row['source_sha256'],'imports':imports,'reports':reports})
expected={'DiophantineConsistency.RotationAdjacent','DiophantineConsistency.CompactHighResidue','DiophantineConsistency.CompactLowExact','DiophantineConsistency.CompactSymbolicPorts','DiophantineConsistency.ArithmeticStandardCasts','DiophantineConsistency.FreeJGraphCongruenceExplore','DiophantineConsistency.CompactMixedIncrement','DiophantineConsistency.WrappedAdjacent','DiophantineConsistency.ArithmeticCyclicWord','DiophantineConsistency.CompactModelStencilSlack','DiophantineConsistency.GenericBandCarryFamily','DiophantineConsistency.RotationIndexBounds','DiophantineConsistency.RotationStraddling','DiophantineConsistency.CompactDummyBound','DiophantineConsistency.ArithmeticModularCancellation','DiophantineConsistency.CompactHeterogeneousCarry','DiophantineConsistency.FixedGraphIndexedCarry','DiophantineConsistency.CompactLowEven','DiophantineConsistency.CompactConcreteIndexedMass','DiophantineConsistency.CompactConcreteMask','DiophantineConsistency.FreeJConcreteDigitsClient'}
if external!=expected:raise ValueError(('external imports',external))
if comp['older_provider']!=str(old):raise ValueError('old provider path')
prev=None;diffs={}
for side in ('author','peer'):
 lib=provider/side/'lib';oldlib=old/side/'lib';live={x.relative_to(lib).as_posix():x for x in lib.rglob('*.olean') if x.is_file()};oldfiles={x.relative_to(oldlib).as_posix():x for x in oldlib.rglob('*.olean') if x.is_file()};rec={x['path']:x for x in scan['parent_objects'][side]}
 if len(live)!=203 or len(oldfiles)!=117 or set(live)!=set(rec):raise ValueError(('provider inventory',side))
 pairs=[]
 for name,p in sorted(live.items()):
  item=rec[name];digest=H(p)
  if str(p.resolve())!=item['realpath'] or digest!=item['sha256']:raise ValueError(('parent drift',side,name))
  pairs.append((name,digest))
 if prev is not None and pairs!=prev:raise ValueError('same-side hash discrepancy')
 prev=pairs;common=live.keys()&oldfiles.keys();different=[{'path':name,'rotation_sha256':H(live[name]),'older_clean_carry_sha256':H(oldfiles[name])} for name in sorted(common) if H(live[name])!=H(oldfiles[name])];recorded=comp['sides'][side]
 if len(common)!=92 or len(different)!=4 or recorded['rotation_objects']!=203 or recorded['older_objects']!=117 or recorded['overlap']!=92 or recorded['different']!=different:raise ValueError(('prior provider comparison drift',side))
 diffs[side]=different
for k,count in [('external_direct_slots',420),('target_slots',660),('package_slots',10)]:
 if len(scan[k])!=count:raise ValueError(('slot count',k))
 for name,item in scan[k].items():
  p=P(name)
  if item is None:
   if os.path.lexists(p):raise ValueError(('unexpected companion',name))
  elif not p.is_file() or str(p.resolve())!=item['realpath'] or H(p)!=item['sha256']:raise ValueError(('companion drift',name))
if any(x is not None for x in scan['target_slots'].values()):raise ValueError('target occupied')
r=subprocess.run([sys.executable,'-I','-S','-B',str(parent/'audit.py')],cwd=root,capture_output=True,timeout=2400)
if r.returncode!=0 or r.stderr or json.loads(r.stdout)!=pa:raise ValueError(('parent audit rerun',r.returncode,r.stderr))
print(json.dumps({'status':'PASS_INDEPENDENT_FIXED_CLEAN_CARRY_SOURCE_CLOSURE','reviewed_commit':'4c58391a77','scan_sha256':scan_sha,'comparison_sha256':compare_sha,'parent_audit_sha256':parent_sha,'parent_receipt_sha256':scan['parent_receipt_sha256'],'source_modules':33,'named_reports':sum(counts),'parent_objects_per_side':203,'old_objects_per_side':117,'old_overlap_per_side':92,'old_differing_per_side':4,'provider_differences':diffs,'external_direct_slots':420,'target_slots':660,'package_slots':10,'parent_audit_rerun_exit':r.returncode,'lean_launched':False,'source_rows':summaries,'review_scope':'Source/artifact closure verification only, not independent mathematical review or paired rebuild; retained-byte/display binding, raw-column decoder identity, machine and internal iPRA remain open.'},indent=2,sort_keys=True))
