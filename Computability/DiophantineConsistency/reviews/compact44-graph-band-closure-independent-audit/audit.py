#!/usr/bin/env python3
"""Independent point-in-time review of the 21-source graph-band closure; no Lean."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S -B')
REPO=Path.cwd();ROOT=REPO/'Computability/DiophantineConsistency';BASE=ROOT/'research/ordinary12-ipra-bridge';PLAN=BASE/'compact44-graph-band-closure-plan';OLD=BASE/'compact44-direct-k-band-join-plan';EXPL=BASE/'compact44-direct-k-band-join-exploration';HERE=Path(__file__).resolve().parent;PARENT=Path('/tmp/ipra-direct-symbolic-k-pair-01');OTHER=Path('/tmp/ipra-compact-coefficient-decomposition-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');AUDIT=ROOT/'reviews/compact44-direct-symbolic-k-pair-independent-audit/CHECK.json'
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
def h(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(ok,msg):
 if not ok:raise ValueError(msg)
need(h(PLAN/'scan.json')=='f5c34a67f1e065dfd7801e35bc661706699edc291f8515743dfe9074f0626a18','scan drift');scan=json.loads((PLAN/'scan.json').read_bytes());obs=json.loads((PLAN/'terminal-observation.json').read_bytes())
need(scan['status']=='PRELIMINARY_GRAPH_BAND_21_SOURCE_CLOSURE_NOT_A_BUILD' and type(obs['observed_exit']) is int and obs['observed_exit']==0 and obs['optimized_exit']==1 and obs['lean_launched'] is False and obs['scan_sha256']==h(PLAN/'scan.json'),'scan receipt')
need((HERE/'observations/scan-rerun.stdout').read_bytes()==(PLAN/'scan.json').read_bytes() and not (HERE/'observations/scan-rerun.stderr').read_bytes(),'normal scan mismatch')
need(h(OLD/'scan.json')==scan['base_scan_sha256']=='2048ee458a2f49755858e991e3837b71aab244ce9c8521e483e6cdea6282616d' and h(AUDIT)==scan['parent_audit_sha256']=='5aecb3c05962fd5f13650899bac9ce6f2406827a8d08f43714ddd2966716a634','parent input pin')
parent=json.loads(AUDIT.read_bytes());need(parent['status']=='PASS_INDEPENDENT_DIRECT_SYMBOLIC_K_PAIR_AUDIT' and type(parent['recorded_outer_exit']) is int and parent['recorded_outer_exit']==0,'parent receipt')
rows=scan['source_order'];need(len(rows)==21 and len({r['module'] for r in rows})==21,'source inventory count');first=json.loads((OLD/'scan.json').read_bytes())['source_order'];need(rows[:14]==first,'base source list drift');expected_reports=0;available=set();external=set();allnames={r['module'] for r in rows}
for row in rows:
 src=Path(row['source']);need(src.is_file() and h(src)==row['source_sha256'],('source digest',row['module']));git=subprocess.run(['git','show',f"{row['source_commit']}:{src.relative_to(REPO)}"],cwd=REPO,capture_output=True,check=True,timeout=30);need(hashlib.sha256(git.stdout).hexdigest()==row['source_sha256'],('git source',row['module']))
 text=src.read_text();imports=[line[7:] for line in text.splitlines() if line.startswith('import ')];reports=re.findall(r'^#print axioms\s+(\S+)',text,re.M);need(imports==row['imports'] and reports==row['axiom_reports'],('imports or reports',row['module']));expected_reports+=len(reports)
 for dep in imports:
  if dep not in available:need(dep not in allnames,('out of order',row['module'],dep));external.add(dep)
 available.add(row['module'])
expected_external={'DiophantineConsistency.ArithmeticWindowDigits','DiophantineConsistency.Compact943Data','DiophantineConsistency.CompactCoefficientMass','DiophantineConsistency.CompactSymbolicKernelOpaque','DiophantineConsistency.CompactGraphDerivedRadix','DiophantineConsistency.ArithmeticModularCancellation','Mathlib.Algebra.BigOperators.Ring.Finset','Mathlib.Algebra.BigOperators.Fin'};need(external==expected_external and expected_reports==35,('external or report inventory',external,expected_reports))
for side in ('author','peer'):
 lib=PARENT/side/'lib';items={str(f.relative_to(lib)):f for f in lib.rglob('*.olean')};recorded=scan['parent_objects'][side];need(len(items)==150 and len(recorded)==150,('provider count',side))
 for row in recorded:
  f=items.get(row['path']);need(f is not None and h(f)==row['sha256'] and str(f.resolve())==row['realpath'],('provider object',side,row['path']))
 old=OTHER/side/'lib';other={str(f.relative_to(old)):f for f in old.rglob('*.olean')};div=[{'path':rel,'coefficient_sha256':h(other[rel]),'direct_k_sha256':h(items[rel])} for rel in sorted(items.keys()&other.keys()) if h(items[rel])!=h(other[rel])];need(div==scan['divergent_overlap'][side] and {x['path'].split('/')[-1] for x in div}=={'ArithmeticBinaryCarry.olean','ArithmeticBinomLegendre.olean','Compact943Data.olean','CompactCoefficientMass.olean'},('provider divergences',side,div))
def stems(stems):return {str(stem)+suf for stem in stems for suf in SUFFIXES}
project=[x for x in external if x.startswith('DiophantineConsistency.')];package=['Init']+sorted(x for x in external if x.startswith('Mathlib.'))
expected_direct=stems([PARENT/side/'lib'/Path(*n.split('.')) for side in ('author','peer') for n in project]);expected_targets=stems([PARENT/side/'lib'/Path(*r['module'].split('.')) for side in ('author','peer') for r in rows]);expected_package=stems([PACKAGE/Path(*n.split('.')) for n in package])
for key,expected in [('external_direct_slots',expected_direct),('target_slots',expected_targets),('package_slots',expected_package)]:
 slots=scan[key];need(set(slots)==expected,('slot set',key));
 for name,old in slots.items():
  f=Path(name)
  if old is None:need(not os.path.lexists(f),('unexpected slot',name))
  else:need(f.is_file() and str(f.resolve())==old['realpath'] and h(f)==old['sha256'],('slot drift',name))
need(len(expected_direct)==120 and len(expected_targets)==420 and len(expected_package)==30 and all(x is None for x in scan['target_slots'].values()),'slot count or target collision')
survey=json.loads((EXPL/'direct-k-band-warning-survey.json').read_bytes());need(survey['status']=='PASS_HISTORICAL_SOURCE_MATCHED_WARNING_SURVEY' and len(survey['entries'])==14,'warning survey');prog=json.loads((EXPL/'attempt-03/progress.json').read_bytes());need(len(prog)==14,'exploratory progress count');warning_inventory=[]
for row,entry,step in zip(rows[:14],survey['entries'],prog):
 name=row['module'].split('.')[-1];need(entry['module']==name and entry['source_sha256']==row['source_sha256']==step['source_sha256'] and step['module']==row['module'] and type(step['compiler_exit']) is int and step['compiler_exit']==0 and step['stop_reason'] is None,('exploratory source/exit',name));log=EXPL/'attempt-03'/(name+'.log');text=log.read_text();need(h(log)==step['log_sha256'] and 'error:' not in text and 'sorryAx' not in text,('exploratory log',name));warns=re.findall(r'^.*warning:.*$',text,re.M)
 if name in ('ArithmeticCyclicWord','ArithmeticWindowCarry'):
  suffix=entry['warning_suffixes'];need(len(suffix)==1 and len(warns)==1 and text=='/dev/shm/ipra-direct-k-band-explore-03/frozen/DiophantineConsistency/'+name+'.lean'+suffix[0],('warning exact text',name));warning_inventory.append({'module':name,'suffix':suffix[0]})
 else:need(not warns and not entry['warning_suffixes'],('unexpected historical warning',name))
expected_warnings={'ArithmeticCyclicWord':':145:38: warning: Variable name `hn` is not explicitly referenced.','ArithmeticWindowCarry':':162:29: warning: Variable name `h` is not explicitly referenced.'};need({r['module']:r['suffix'].splitlines()[0] for r in warning_inventory}==expected_warnings,'warning location/text')
logs=['compact44-two-band-rotation-prototype/observations/attempt04.log','compact44-k-cast-pieces-prototype/observations/attempt05.log','compact44-symbolic-k-band-cast-prototype/observations/attempt08.log','compact44-model-band-cut-prototype/observations/attempt15.log','free-j-symbolic-congruence-prototype/observations/attempt01.log','compact44-graph-band-client-prototype/observations/attempt16.log','compact44-graph-band-client-prototype/observations/attempt17.log']
for row,path in zip(rows[14:],logs):
 text=(BASE/path).read_text();need(not re.search(r'(?m)^.*(?:error:|warning:)|\bsorryAx\b|\bsorry\b',text),('later source diagnostics',row['module']));rep=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",text,re.M);need(len(rep)==len(row['axiom_reports']) and {n for n,_ in rep}==set(row['axiom_reports']) and all({v.strip() for v in ax.split(',')}=={'propext','Classical.choice','Quot.sound'} for _,ax in rep),('later report mismatch',row['module']))
print(json.dumps({'status':'PASS_INDEPENDENT_GRAPH_BAND_21_SOURCE_CLOSURE','reviewed_commit':'98ad9ab262','scan_sha256':h(PLAN/'scan.json'),'source_modules':21,'named_reports':35,'parent_objects_per_side':150,'provider_divergences_per_side':4,'external_direct_slots':120,'target_slots':420,'package_slots':30,'normal_scan_session':6527,'normal_scan_exit':0,'first_14_warning_inventory':warning_inventory,'later_seven_author_logs_checked':True,'lean_launched':False,'scope':'Point-in-time source/provider review; 14-source warning inventory and seven author-only prior logs, not a paired build. Graph zero/positivity, symbolic K distinct from retained bytes, fractional temporal residual, full graph column, decoder, machine and internal iPRA remain open.'},indent=2,sort_keys=True))
