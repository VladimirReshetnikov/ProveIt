from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,re,ast,difflib
P=Path('/tmp/gowers-merge68ad-post-native-tools');N=Path('/tmp/gowers-merge68ad-native-tools');O=Path('/tmp/gowers-merge68ad-post-native-independent-review');R=Path('/home/codex/.codex/worktrees/9c9b/Proofs')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def unique(items):
 d={}
 for k,v in items:assert k not in d;d[k]=v
 return d
def read(p):return json.loads(Path(p).read_text(),object_pairs_hook=unique)
def bound(row):assert sha(row['path'])==row['sha256'];return read(row['path'])
def write(name,data):
 with (O/name).open('x') as f:json.dump(data,f,indent=2);f.write('\n')
assert sha(P/'freeze.json')=='9a442d499748afa256ba9d957c2bbe4d29480317745e2c30cd4ae9ec98372734'
freeze=read(P/'freeze.json');assert len(freeze)==6
assert {f.name for f in P.iterdir() if f.is_file()}==set(freeze)|{'freeze.json'}
for n,h in freeze.items():assert sha(P/n)==h,n
prep=read(P/'preparation.json');led=read(P/'source-ledger.json')
old=Path(prep['previous_archive_helper']['path']);assert sha(old)==prep['previous_archive_helper']['sha256']=='120df53838bf541de6cd88d4298d513211059ea6e0938e362b95b17b159a1b0f'
oldtext=old.read_text();newtext=(P/'archive.py').read_text()
subs=[("Path('/tmp/gowers-next829-native-tools')","Path('/tmp/gowers-merge68ad-native-tools')"),("'5e5af281970d9f5c1ea637fa6b32fa7c4551a810'","'a87906dc3960604bc3a0b423868d392b43ba85c0'")]
expected=oldtext
for before,after in subs:assert expected.count(before)==1;expected=expected.replace(before,after)
assert newtext==expected
assert (P/'changes.patch').read_text()==''.join(difflib.unified_diff(oldtext.splitlines(True),newtext.splitlines(True),fromfile=str(old),tofile=str(P/'archive.py')))
assert sha(P/'archive.py')==prep['archive_sha256']=='71c60153a33e2677fc15dd81c675866b51eb0d37271f66346af1eaaae574573b'
assert sha(P/'source-ledger.json')==prep['source_ledger_sha256']=='0ace4e6a88c3633aa16bf157464d1ccbb388289f66b42b4a6770fc353a0820c1'
archive_ast=ast.parse(newtext)
pins=next(ast.literal_eval(n.value) for n in archive_ast.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='PINS' for t in n.targets))
assert set(pins)=={'common.py','capture.py','run.py'}
assert prep['native_helper_toolpins']=={str(N/n):h for n,h in pins.items()}
for n,h in pins.items():assert sha(N/n)==h
nf=read(N/'freeze.json')
for n,h in nf.items():assert sha(N/n)==h,n
measurement=read(N/'measurement.json');owners=read(N/'changed-owners.json');fullgraph=read(N/'fullgraph-imports.json');source_rows=read(N/'source-rows.json');modes=read(N/'mode-closures.json')
commit='a87906dc3960604bc3a0b423868d392b43ba85c0'
assert led['source_commit']==prep['source_commit']==measurement['merge_commit']==commit
assert led['parents']==[measurement['comparison_commit'],measurement['incoming_commit']]
assert led['previous_verified_source']=='5e5af281970d9f5c1ea637fa6b32fa7c4551a810'
snap=bound(led['snapshot']);assert led['snapshot']['sha256']==prep['snapshot_sha256']=='9b7d20d2722fca5919816d0b3ecd4f151d99cb28a6f1ce300f11a9667429768d'
assert snap['source_commit']==commit and snap['root']==str(R)
assert snap['tools']==prep['native_helper_toolpins']
assert sha(snap['plan']['path'])==snap['plan']['sha256']==sha(N/'plan.json')
assert snap['modes']==modes
assert len(snap['graph'])==1964 and len(snap['source_hashes'])==1971
assert all(fullgraph[k]==v for k,v in snap['graph'].items())
for rel,h in snap['source_hashes'].items():assert sha(R/rel)==h,rel
assert led['changed_production_owners']==owners and len(owners)==153
assert led['global_source_line_delta']==sum(v['source_lines_delta'] for v in owners)==-93
for owner in owners:
 assert source_rows[owner['module']]['sha256']==owner['current_sha256']==snap['source_hashes'][owner['path']]
 assert owner['imports_before']==owner['imports_current']
 assert owner['selected_modes']==[k for k,v in snap['modes'].items() if owner['module'] in v['modules']]
 assert owner['selected_modes']
review=bound(led['all_nine_overlap_review'])
assert review['reviewed_actual_merge']==commit and review['reviewed_incoming']==led['parents'][1]
assert review['status']=='PASS_BOUNDED_INCOMING_AND_MERGE_SOURCE_REVIEW_NATIVE_PENDING' and review['findings']==[]
assert review['incoming_summary']['import_changes']==[] and review['incoming_summary']['retained_header_or_variable_context_changes_detected']==[]
assert led['imports_and_retained_headers_unchanged'] is True
assert led['incoming_public_helpers_removed']==[v['name'].rsplit('.',1)[1] for v in review['incoming_summary']['deleted_public_wrappers']]
conflicts=bound(review['merge_assessment']['root_resolution_ledger']);assert conflicts==led['merge_conflicts'] and len(conflicts)==3
for c in conflicts:assert c['sha256']==snap['source_hashes'][c['path']]
assert len(review['merge_assessment']['all_nine_exact_expected_three_way_comparisons'])==9
for r in review['merge_assessment']['all_nine_exact_expected_three_way_comparisons']:
 assert r['staged_sha256']==snap['source_hashes'][r['file']] and r['exact_read_only_merge_with_local_conflict_block'] is True
assert led['final_statement_protection']==review['final_statement_protection']
for r in led['final_statement_protection']:assert r['sha256']==snap['source_hashes'][r['file']] and r['baseline_incoming_local_staged_byte_exact'] is True
memo={};active=set()
def closure(m):
 if m in memo:return memo[m]
 assert m not in active;active.add(m);mods={m}
 for d in fullgraph[m]:
  if d in fullgraph:mods.update(closure(d))
 active.remove(m);memo[m]=mods;return mods
routes={};union=set()
for mode,spec in snap['modes'].items():
 mods=set().union(*(closure(r) for r in spec['roots']));union.update(mods)
 assert spec['modules']==sorted(mods)
 lines=sum(source_rows[m]['source_lines'] for m in mods)
 assert spec['source_lines']==lines
 routes[mode]={'root_count':len(spec['roots']),'modules':len(mods),'source_lines':lines}
for label,target in [('original_final','GowersSzemeredi.Final'),('stronger_final','GowersSzemeredi.Proofs18CoverFejerAllDegrees')]:
 mods=closure(target);routes[label]={'root':target,'modules':len(mods),'source_lines':sum(source_rows[m]['source_lines'] for m in mods)}
routes['union']={'modules':len(union),'source_lines':sum(source_rows[m]['source_lines'] for m in union)}
assert routes==led['routes']==prep['root_routes']
inv=led['inventory'];compare=bound(inv['comparison'])
assert inv['sha256']==snap['source_hashes'][inv['path']]==compare['normalized_sha256']
assert inv['ordered_rows']==compare['row_count']==120
assert inv['companion_occurrences']==compare['companion_occurrences']==544
assert inv['whole_object_permutations']==len(compare['whole_object_permutations'])==4
assert inv['line_leaf_changes']==len(compare['location_leaf_changes'])==30
assert compare['base_commit']==led['parents'][0] and compare['merge_head']==led['parents'][1]
for p,h in compare['source_location_pins'].items():assert sha(p)==h
coverage=read(N/'consumer-coverage.json');assert len(coverage)==1671
expected_scope={'root_counts':[len(v['roots']) for v in snap['modes'].values()],'module_counts':[v['module_count'] for v in snap['modes'].values()],'union_modules':len(union),'protected_inputs':len(snap['source_hashes']),'full_graph_modules':len(fullgraph),'dependent_consumers':len(coverage),'covered_consumers':sum(bool(v['selected_modes']) for v in coverage),'excluded_facades':[v['module'] for v in coverage if not v['selected_modes']]}
assert led['validation_scope']==expected_scope
assert led['historical_retention_planned'] is False and led['full_native_success_claimed'] is False
assert prep['native_validation_completed'] is False
assert prep['status']=='SOURCE-ONLY PREPARATION; NOT EXECUTED'
# Parse command-line declarations without importing/executing the helper.
arguments={}
for node in ast.walk(archive_ast):
 if isinstance(node,ast.Call) and isinstance(node.func,ast.Attribute) and node.func.attr=='add_argument' and node.args and isinstance(node.args[0],ast.Constant):
  arguments[node.args[0].value]={kw.arg:ast.literal_eval(kw.value) for kw in node.keywords if kw.arg in ['required','nargs']}
assert arguments['--source-ledger']=={'nargs':2,'required':True}
assert arguments['--snapshot']=={'nargs':2,'required':True}
assert arguments['--output']['required'] is True
assert "for mode in ('core', 'shared', 'supplemental'):" in newtext
assert "parser.add_argument('--' + mode, nargs=2, metavar=('RECEIPT', 'SHA256'), required=True)" in newtext
assert "'per_root_closures_are_metadata_only': True" in newtext
report={'status':'PASS: static archive preparation only; actual native outcomes remain pending','reviewed_at':datetime.now(timezone.utc).isoformat(),'package':str(P),'package_freeze_sha256':sha(P/'freeze.json'),'archive_sha256':sha(P/'archive.py'),'source_ledger_sha256':sha(P/'source-ledger.json'),'source_commit':commit,'exact_archive_substitutions':[{'before':b,'after':a} for b,a in subs],'native_helpers_exact_pins':pins,'native_plan_sha256':sha(N/'plan.json'),'native_package_freeze_sha256':sha(N/'freeze.json'),'snapshot':led['snapshot'],'source_owner_rows_verified':153,'protected_current_source_hashes_verified':1971,'root_routes_recomputed':routes,'inventory':{'ordered_rows':120,'occurrences':544,'permutations':4,'line_leaves':30,'source_location_pins_verified':len(compare['source_location_pins']),'sha256':inv['sha256'],'comparison_sha256':inv['comparison']['sha256']},'incoming_review':led['all_nine_overlap_review'],'overlap_source_rows_verified':9,'conflict_resolutions_bound':3,'final_statement_hashes_verified':4,'validation_scope':expected_scope,'mandatory_source_ledger_argument':True,'native_receipts_are_mandatory_and_not_supplied_by_this_preparation':True,'historical_native_retention_planned':False,'actual_native_outcomes_reviewed':False,'metadata_is_not_native_success':True,'findings':[],'limitations':['No archive, capture, runner, worker, or source_guard helper was imported or executed. No native receipt/log/cache was read.','This review verifies static preparation, not the ongoing native invocation or eventual archive output.','Mandatory ledger bytes and source metadata are validated here; the archive helper itself pins the supplied ledger hash and checks its source commit, without independently reconstructing every ledger field.','The four upstream public helper-wrapper removals are disclosed in the ledger/review; unchanged retained headers do not mean an identical public export-name set.','The separately pinned extra-evidence manifest and eventual actual receipts/archive require their own final binding checks.'],'actions':{'git_invocations':False,'repository_mutations':False,'cache_access':False,'native_invocations':False,'helper_import_or_execution':False,'writes_only':str(O)}}
write('report.json',report)
write('freeze.json',{p.name:sha(p) for p in sorted(O.iterdir()) if p.is_file() and p.name!='freeze.json'})
for p in O.iterdir():
 if p.is_file():p.chmod(0o444)
print(json.dumps({'status':'PASS','report_sha256':sha(O/'report.json'),'freeze_sha256':sha(O/'freeze.json'),'routes':routes},indent=2))
