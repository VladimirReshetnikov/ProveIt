#!/usr/bin/env python3
"""Independent read-only twelve-source and same-side provider inventory audit."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S')
ROOT=Path(__file__).resolve().parents[4];PLAN=ROOT/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/compact44-common-period-closure-plan';H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for name in ('scan.py','scan.json','README.md','terminal-observation.json'):
 p=PLAN/name;blob=subprocess.run(['git','show','efd80cc5dc:'+p.relative_to(ROOT).as_posix()],cwd=ROOT,capture_output=True,check=True).stdout;assert hashlib.sha256(blob).hexdigest()==H(p),name
scan=json.loads((PLAN/'scan.json').read_bytes());q=subprocess.run([sys.executable,'-I','-S','-B',str(PLAN/'scan.py')],cwd=ROOT,capture_output=True,text=True,timeout=180);assert q.returncode==0 and not q.stderr and json.loads(q.stdout)==scan
q=subprocess.run([sys.executable,'-I','-S','-O','-B',str(PLAN/'scan.py')],cwd=ROOT,capture_output=True,text=True,timeout=180);assert q.returncode!=0 and 'optimized Python rejected' in q.stderr
names=['FreeJGraphCongruenceExplore','CompactSymbolicGraphSaturation','CompactSameWitnessSaturation2','CompactPositionIncrement','CompactPositionGraph','CompactSelectorMask','CompactSelectorGraph','CompactSupportSlot','CompactCopySupport','CompactPeriodCopy','CompactSelectorPeriod','CompactCommonPeriodBits']
imports=[['CompactGraphDerivedRadix','ArithmeticModularCancellation'],['FreeJConcreteDigitsClient','CompactLowExact','CompactLowEven','CompactHighResidue'],['FreeJGraphCongruenceExplore','CompactSymbolicGraphSaturation'],['CompactMixedIncrement'],['CompactSameWitnessSaturation2','CompactPositionIncrement'],['CompactPositionGraph'],['CompactSelectorMask'],['CompactSelectorGraph'],['CompactSupportSlot','CompactSymbolicKernel'],['CompactCopySupport'],['CompactSelectorGraph'],['CompactPeriodCopy','CompactSelectorPeriod']]
expected_reports=[
['FreeJGraphCongruenceExplore.fixed_symbolic_aligned','FreeJGraphCongruenceExplore.symbolic_aligned','FreeJGraphCongruenceExplore.first_pair_mod','FreeJGraphCongruenceExplore.graph_congruence','FreeJGraphCongruenceExplore.graph_aligned_congruence'],
['CompactSymbolicGraphSaturation.graph_saturation'],['CompactSameWitnessSaturation.fixed_graph_saturation','CompactSameWitnessSaturation.generic_graph_saturation'],['CompactPositionCarry.increment_digits'],['CompactPositionCarry.generic_position_noCarry','CompactPositionCarry.fixed_position_noCarry'],['CompactSelectorMask.selector_mask_digit','CompactSelectorMask.absent_mask_digit'],['CompactSelectorGraph.selector_slot','CompactSelectorGraph.excluded_slot','CompactSelectorGraph.fixed_graph_selector_bounds'],['CompactSupportSlot.support_mask_digit','CompactSupportSlot.support_slot','CompactSupportSlot.fixed_graph_support_bounds'],['CompactCopySupport.position_good','CompactCopySupport.fixed_graph_copy_bounds'],['CompactPeriodCopy.period_index','CompactPeriodCopy.position_pos','CompactPeriodCopy.fixed_graph_period_copies'],['CompactSelectorPeriod.period_index_zero_allowed','CompactSelectorPeriod.fixed_graph_period_selectors'],['CompactCommonPeriodBits.fixed_graph_common_period_bits']]
counts=[5,1,2,1,2,2,3,3,2,3,2,1];assert len(scan['source_order'])==12 and sum(counts)==27
for row,name,imps,count,expected in zip(scan['source_order'],names,imports,counts,expected_reports):
 p=Path(row['source']);assert row['module']=='DiophantineConsistency.'+name and H(p)==row['source_sha256'];blob=subprocess.run(['git','show',row['source_commit']+':'+p.relative_to(ROOT).as_posix()],cwd=ROOT,capture_output=True,check=True).stdout;assert hashlib.sha256(blob).hexdigest()==row['source_sha256']
 assert [line[7:] for line in p.read_text().splitlines() if line.startswith('import ')]==['DiophantineConsistency.'+x for x in imps]==row['imports']
 reports=re.findall(r'^#print axioms\s+(\S+)',p.read_text(),re.M);assert reports==row['axiom_reports']==expected and len(reports)==count and len(set(reports))==count
for side in ('author','peer'):
 rows=scan['objects'][side];assert len(rows)==150
 for z in rows:
  p=Path(z['resolved']);assert p.is_file() and H(p)==z['sha256']
assert [(z['path'],z['sha256']) for z in scan['objects']['author']]==[(z['path'],z['sha256']) for z in scan['objects']['peer']]
for key,count in [('external_direct_slots',160),('target_slots',240),('init_slots',10)]:
 slots=scan[key];assert len(slots)==count
 for name,prior in slots.items():
  p=Path(name)
  if prior is None:assert not os.path.lexists(p),name
  else:assert p.is_file() and str(p.resolve())==prior['resolved'] and H(p)==prior['sha256'],name
assert all(v is None for v in scan['target_slots'].values())
external={'CompactGraphDerivedRadix','ArithmeticModularCancellation','FreeJConcreteDigitsClient','CompactLowExact','CompactLowEven','CompactHighResidue','CompactMixedIncrement','CompactSymbolicKernel'}
for side in ('author','peer'):
 lib=Path('/tmp/ipra-direct-symbolic-k-pair-01')/side/'lib'/'DiophantineConsistency';available=set(external)
 for name,imps in zip(names,imports):
  for dep in imps:
   assert dep in available,(name,dep)
   if dep in external:assert (lib/(dep+'.olean')).is_file()
  available.add(name)
print(json.dumps({'status':'PASS_INDEPENDENT_COMMON_PERIOD_SOURCE_CLOSURE','reviewed_commit':'efd80cc5dc','source_modules':12,'source_order':names,'source_report_counts':counts,'parent_objects_per_side':150,'direct_slots':160,'target_slots':240,'init_slots':10,'lean_launched':False,'scope':'Point-in-time same-side source and provider inventory only, not a parent audit rerun or paired build. Final graph theorem has one N,w, symbolic masks and arbitrary K, with no retained-byte binding, graph-column decoder, machine or iPRA theorem.'},indent=2))
