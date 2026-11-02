#!/usr/bin/env python3
"""No-Lean indexed mass/carry source/provider inventory and parent rerun."""
import hashlib,json,os,pathlib,re,subprocess,sys
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('isolated nonoptimized Python required')
P=pathlib.Path;root=P.cwd();base=root/'Computability/DiophantineConsistency';plan=base/'research/ordinary12-ipra-bridge/compact44-indexed-mass-carry-closure-plan';parent=base/'reviews/compact44-graph-temporal-carry-pair-independent-audit';provider=P('/tmp/ipra-graph-temporal-carry-pair-01');old=P('/tmp/compact44-aligned-family-plan/lib');H=lambda p:hashlib.sha256(P(p).read_bytes()).hexdigest();scan_sha='b7d32838dd73738bbebc89242f015071c1fe66864468287516181eb7b15ad8fc';source_sha='627725437b7faece938d2151a471f5607b7487c9e38d4e95d1fd0da7ada1d904';compare_sha='9451bfcaae2a6ca757480789145fa2ae351c08b7e6cb783a6474305cb403e121';parent_script_sha='f2e8fc237ae73ba58e54a3b0fc68a49d4d348d61ebbbea9ebe1284ccb88b2781';parent_sha='eab1a508f2b84c27883f526e882bf0852045580fa690f86948bf834b4557cb0e'
def gh(rev,p):return hashlib.sha256(subprocess.run(['git','show',rev+':'+p.relative_to(root).as_posix()],cwd=root,capture_output=True,check=True,timeout=60).stdout).hexdigest()
for p,h in [(plan/'scan.json',scan_sha),(plan/'scan.py',source_sha),(plan/'prior-provider-comparison.json',compare_sha)]:
 if H(p)!=h or gh('98fdf29c89',p)!=h:raise ValueError(('plan drift',str(p)))
if H(parent/'audit.py')!=parent_script_sha or H(parent/'CHECK.json')!=parent_sha:raise ValueError('parent audit drift')
scan=json.loads((plan/'scan.json').read_bytes());obs=json.loads((plan/'terminal-observation.json').read_bytes());pa=json.loads((parent/'CHECK.json').read_bytes());pto=json.loads((parent/'terminal-observation.json').read_bytes());comp=json.loads((plan/'prior-provider-comparison.json').read_bytes())
if scan['status']!='PRELIMINARY_INDEXED_MASS_CARRY_SOURCE_CLOSURE_NOT_A_BUILD' or scan['parent_audit_sha256']!=parent_sha or scan['parent_receipt_sha256']!='d4221b3e0919af4718ecb92fc731aceec96ad3472ea75b2d846fb69814ac0c14':raise ValueError('scan receipt')
if type(obs['observed_exit']) is not int or obs['observed_exit']!=0 or obs['optimized_exit']!=1 or obs['lean_launched'] is not False or obs['parent_audit_rerun'] is not False or obs['scan_sha256']!=scan_sha or pto['check_sha256']!=parent_sha or type(pto['observed_exit']) is not int or pto['observed_exit']!=0 or pa['status']!='PASS_INDEPENDENT_GRAPH_TEMPORAL_CARRY_PAIRED_ARTIFACT_AUDIT':raise ValueError('observation')
names=['CompactModelStencilSlack','CompactGenericAlignedMass','CompactSelectorMassBridge','CompactIndexedMass','CompactFinIndexedMass','CompactConcreteIndexedMass','CompactConcreteIndexedModel','CompactIndexedFlatten','CompactTwoBandFlatten','CompactTwoBandCarry','FixedGraphIndexedCarry'];counts=[3,1,4,2,1,1,1,2,1,1,1];rows=scan['source_order'];allnames={'DiophantineConsistency.'+x for x in names};available=set();external=set();summaries=[]
if len(rows)!=11 or [r['module'] for r in rows]!=['DiophantineConsistency.'+x for x in names]:raise ValueError('source order')
for row,rc in zip(rows,counts):
 p=P(row['source']);s=p.read_text();imports=[l[7:] for l in s.splitlines() if l.startswith('import ')];reports=re.findall(r'^#print axioms\s+(\S+)',s,re.M)
 if H(p)!=row['source_sha256'] or gh(row['source_commit'],p)!=row['source_sha256'] or imports!=row['imports'] or reports!=row['axiom_reports'] or len(reports)!=rc:raise ValueError(('source/import/report drift',row['module']))
 for dep in imports:
  if dep not in available:
   if dep in allnames:raise ValueError(('forward import',dep))
   external.add(dep)
 available.add(row['module']);summaries.append({'module':row['module'],'sha256':row['source_sha256'],'imports':imports,'reports':reports})
expected={'DiophantineConsistency.ArithmeticStandardCasts','DiophantineConsistency.ArithmeticWindowCarry','DiophantineConsistency.CompactCoefficientMass','DiophantineConsistency.GenericBandCarryFamily','DiophantineConsistency.FixedGraphTemporal','DiophantineConsistency.TwoBand','Mathlib.Algebra.BigOperators.Fin','Mathlib.Data.Fintype.BigOperators'}
if external!=expected:raise ValueError(('external imports',external))
oldfiles={p.relative_to(old).as_posix():p for p in old.rglob('*.olean') if p.is_file()}
if len(oldfiles)!=134 or comp['old_exploratory_provider']!=str(old):raise ValueError('old provider inventory')
prev=None;diffs={}
for side in ('author','peer'):
 lib=provider/side/'lib';live={x.relative_to(lib).as_posix():x for x in lib.rglob('*.olean') if x.is_file()};entries=scan['parent_objects'][side];rec={x['path']:x for x in entries}
 if len(live)!=178 or set(live)!=set(rec):raise ValueError(('parent inventory',side))
 pairs=[]
 for name,p in sorted(live.items()):
  item=rec[name];digest=H(p)
  if str(p.resolve())!=item['realpath'] or digest!=item['sha256']:raise ValueError(('parent drift',side,name))
  pairs.append((name,digest))
 if prev is not None and pairs!=prev:raise ValueError('same-side hash discrepancy')
 prev=pairs;common=live.keys()&oldfiles.keys();different=[{'path':name,'graph_temporal_sha256':H(live[name]),'old_exploratory_sha256':H(oldfiles[name])} for name in sorted(common) if H(live[name])!=H(oldfiles[name])]; recorded=comp['sides'][side]
 if len(common)!=102 or len(different)!=15 or recorded['current_object_count']!=178 or recorded['old_object_count']!=134 or recorded['overlap_count']!=102 or recorded['different']!=different:raise ValueError(('prior provider comparison drift',side))
 diffs[side]=different
for k,count in [('external_direct_slots',120),('target_slots',220),('package_slots',30)]:
 if len(scan[k])!=count:raise ValueError(('slot count',k))
 for name,item in scan[k].items():
  p=P(name)
  if item is None:
   if os.path.lexists(p):raise ValueError(('unexpected companion',name))
  elif not p.is_file() or str(p.resolve())!=item['realpath'] or H(p)!=item['sha256']:raise ValueError(('companion drift',name))
if any(x is not None for x in scan['target_slots'].values()):raise ValueError('target occupied')
r=subprocess.run([sys.executable,'-I','-S','-B',str(parent/'audit.py')],cwd=root,capture_output=True,timeout=1800)
if r.returncode!=0 or r.stderr or json.loads(r.stdout)!=pa:raise ValueError(('parent audit rerun',r.returncode,r.stderr))
print(json.dumps({'status':'PASS_INDEPENDENT_INDEXED_MASS_CARRY_SOURCE_CLOSURE','reviewed_commit':'98fdf29c89','scan_sha256':scan_sha,'comparison_sha256':compare_sha,'parent_audit_sha256':parent_sha,'parent_receipt_sha256':scan['parent_receipt_sha256'],'source_modules':11,'named_reports':sum(counts),'parent_objects_per_side':178,'old_objects':134,'overlap_per_side':102,'differing_per_side':15,'provider_differences':diffs,'external_direct_slots':120,'target_slots':220,'package_slots':30,'parent_audit_rerun_exit':r.returncode,'lean_launched':False,'source_rows':summaries,'review_scope':'Source and artifact closure verification only, not independent mathematical review or paired rebuild; retained-byte/display binding, clean predecessor, decoder, machine and internal iPRA remain open.'},indent=2,sort_keys=True))
