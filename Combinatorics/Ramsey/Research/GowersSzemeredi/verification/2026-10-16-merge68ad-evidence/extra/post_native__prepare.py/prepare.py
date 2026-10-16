from pathlib import Path
import json,hashlib,datetime,functools,difflib,subprocess
root=Path('/home/codex/.codex/worktrees/9c9b/Proofs')
out=Path('/tmp/gowers-merge68ad-post-native-tools');assert not out.exists();out.mkdir()
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
source='a87906dc3960604bc3a0b423868d392b43ba85c0'
snapshot=Path('/tmp/gowers-merge68ad-a879-source-snapshot.json');snap=read(snapshot)
assert snap['source_commit']==source and sha(snapshot)=='9b7d20d2722fca5919816d0b3ecd4f151d99cb28a6f1ce300f11a9667429768d'
assert subprocess.check_output(['git','rev-parse','HEAD']).decode().strip()==source
assert subprocess.check_output(['git','status','--porcelain'])==b''
old=Path('/tmp/gowers-next829-post-native-tools-repaired5e5a/archive.py')
assert sha(old)=='120df53838bf541de6cd88d4298d513211059ea6e0938e362b95b17b159a1b0f'
s=old.read_text();updated=s.replace("Path('/tmp/gowers-next829-native-tools')","Path('/tmp/gowers-merge68ad-native-tools')").replace("'5e5af281970d9f5c1ea637fa6b32fa7c4551a810'","'a87906dc3960604bc3a0b423868d392b43ba85c0'")
assert s.count("Path('/tmp/gowers-next829-native-tools')")==s.count("'5e5af281970d9f5c1ea637fa6b32fa7c4551a810'")==1
compile(updated,'archive.py','exec')
(out/'archive.py').write_text(updated)
(out/'changes.patch').write_text(''.join(difflib.unified_diff(s.splitlines(True),updated.splitlines(True),fromfile=str(old),tofile=str(out/'archive.py'))))
@functools.lru_cache(None)
def closure(m):return frozenset({m}).union(*(closure(d) for d in snap['graph'][m] if d in snap['graph']))
def path(m):return root/('Combinatorics/Ramsey/Lean' if m.split('.')[0]=='GowersSzemeredi' else 'lib/openai-math/lean')/(m.replace('.','/')+'.lean')
routes={k:{'root_count':len(v['roots']),'modules':v['module_count'],'source_lines':v['source_lines']} for k,v in snap['modes'].items()}
for label,m in [('original_final','GowersSzemeredi.Final'),('stronger_final','GowersSzemeredi.Proofs18CoverFejerAllDegrees')]:
 mods=closure(m);routes[label]={'root':m,'modules':len(mods),'source_lines':sum(len(path(x).read_text().splitlines()) for x in mods)}
routes['union']={'modules':len(snap['graph']),'source_lines':sum(len(path(x).read_text().splitlines()) for x in snap['graph'])}
review=read('/tmp/gowers-incoming68ad-static-review/report.json')
for item in review['final_statement_protection']:assert sha(root/item['file'])==item['sha256']
inv=Path('/tmp/gowers-merge68ad-inventory-actual')
ledger={'status':'Committed merged source ledger; actual native outcomes must be supplied separately','recorded_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_commit':source,'parents':['685a309568b28cc4914662c144f38bcda92ce4a1','68ad8d39173bf0494fa46154869ccea9b1a3c623'],'previous_verified_source':'5e5af281970d9f5c1ea637fa6b32fa7c4551a810','snapshot':{'path':str(snapshot),'sha256':sha(snapshot)},'changed_production_owners':read('/tmp/gowers-merge68ad-native-tools/changed-owners.json'),'global_source_line_delta':-93,'incoming_public_helpers_removed':['section5_image_mono','polynomialOn_section5NatIndexPoint','section16FibreClassSet_mono','one_le_lsNestThr'],'imports_and_retained_headers_unchanged':True,'merge_conflicts':read('/tmp/gowers-merge68ad-conflict-resolutions.json'),'all_nine_overlap_review':{'path':'/tmp/gowers-incoming68ad-static-review/report.json','sha256':sha('/tmp/gowers-incoming68ad-static-review/report.json')},'final_statement_protection':review['final_statement_protection'],'routes':routes,'inventory':{'path':'Combinatorics/Ramsey/gowers-proof-status.json','sha256':sha(root/'Combinatorics/Ramsey/gowers-proof-status.json'),'ordered_rows':120,'companion_occurrences':544,'whole_object_permutations':4,'line_leaf_changes':30,'comparison':{'path':str(inv/'comparison.json'),'sha256':sha(inv/'comparison.json')}},'validation_scope':{'root_counts':[1,65,18],'module_counts':[572,1915,351],'union_modules':1964,'protected_inputs':1971,'full_graph_modules':6021,'dependent_consumers':1671,'covered_consumers':1668,'excluded_facades':['GowersSzemeredi','GowersSzemeredi.Audit','GowersSzemeredi.PortImportAudit']},'historical_retention_planned':False,'full_native_success_claimed':False,'limitations':['Native validation of merged source is still running. The older 5e5a receipts are not a validation of a879.','Catalogue coverage is not a certificate of fidelity to every original paper statement.','Prospective simplification drafts are separate, unapplied, and have no native validation.']}
(out/'source-ledger.json').write_text(json.dumps(ledger,indent=2)+'\n')
(out/'README.txt').write_text('''Prepared archive helper for merged source a87906dc. Do not execute it while any native worker is live. It requires actual sequential passing core/shared/supplemental receipts and fresh combined artifacts, then writes only a new /tmp archive. It does not edit repository files or claim a pass in advance. Root may copy its actual output into the repository after success. The native directory and exact source commit are the only archive.py changes from the reviewed 5e5a helper. Add static evidence through a separately pinned manifest; receipts and source-ledger are mandatory explicit arguments. The source ledger records metadata, not native success. No live native tools or source files were changed by this preparation.\n''')
(out/'preparation.json').write_text(json.dumps({'status':'SOURCE-ONLY PREPARATION; NOT EXECUTED','source_commit':source,'previous_archive_helper':{'path':str(old),'sha256':sha(old)},'archive_changes':['native tool directory','expected source commit'],'archive_sha256':sha(out/'archive.py'),'source_ledger_sha256':sha(out/'source-ledger.json'),'snapshot_sha256':sha(snapshot),'native_helper_toolpins':snap['tools'],'root_routes':routes,'native_validation_completed':False},indent=2)+'\n')
(out/'prepare.py').write_bytes(Path(__file__).read_bytes())
freeze={p.name:sha(p) for p in sorted(out.iterdir()) if p.is_file()};(out/'freeze.json').write_text(json.dumps(freeze,indent=2)+'\n')
for p in out.iterdir():p.chmod(0o444)
print(json.dumps({'archive_sha256':sha(out/'archive.py'),'source_ledger_sha256':sha(out/'source-ledger.json'),'freeze_sha256':sha(out/'freeze.json'),'routes':routes},indent=2))
