#!/usr/bin/env python3
"""Own receipt audit and evidence-only packaging; runs no supplied code."""
from pathlib import Path
import ast,difflib,gzip,hashlib,json,shutil
D=Path(__file__).resolve().parent;A=Path('/tmp/zfc-intake191/K217_Search_Round_2026-10-20/K217_Search_Round_2026-10-20');C=D/'replay1/copy'
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
r=json.loads((D/'replay1/result.json').read_text()); assert r['status']=='EIGHT_SELECTED_LEAVES_PASS' and len(r['jobs'])==8 and all(x['accepted']and x['exit_code']==0 for x in r['jobs'])
checks=['eight terminal jobs, exit0 and required JSON gates']
for x in r['jobs']:
 p=C/x['receipt'];assert H(p)==x['receipt_sha256'];assert json.loads(p.read_text())['status']==x['receipt_status']
 script=Path(x['argv'][-1]);rel=script.relative_to(C);assert H(script)==x['script_sha256']==H(A/rel)
 for ext in ('stdout','stderr'):assert (D/'replay1/logs'/f"{x['name']}.{ext}").is_file()
 assert (D/'replay1/logs'/f"{x['name']}.stderr").read_bytes()==b''
 checks.append('script unchanged, fresh receipt and clean stderr: '+x['name'])
proof=json.loads((C/'research217_bootstrap/crossover30/INITIALIZED217_TAG_PROOF.json').read_text());cases=json.loads((C/'research217_bootstrap/crossover30/INITIALIZED217_TAG_CASES.json').read_text());sites=json.loads((C/'research217_encoding/crossover30_primary/sites.json').read_text())
expected=[(i,pos)for i,s in enumerate(sites)for pos in ((False,True)if s[1]=='CD'else(False,))]
assert [(x['index'],x['positive'])for x in cases]==expected and len(cases)==6167
assert sum(x['symbolic_steps']for x in cases)==1515251 and min(x['duration'][0]for x in cases)==12
assert proof['failure'] is None and proof['unknown_windows']==[] and proof['symbolic_q51_read0_events']==4795 and proof['right1_events']==4747 and proof['right0_events']==48
assert proof['boot_left4']==[0,5,6,7] and proof['decoder_left4']==[1,3,9,11]
mp={int(k):v for k,v in json.loads((C/'research218_encoding/NATIVE_TO_LEGACY.json').read_text()).items()}
assert all(row[1][0]!=mp[51]for b in proof['fresh_block_certificates']for row in b['trace'])
checks+=['all4744 sites and exact CD zero/positive case census','symbolic rule and positive-clock totals independently summed','q51 observer counts and disjoint four-bit masks','q51 is absent from accelerated block interiors']
bind=json.loads((C/'research217_bootstrap/crossover30/CONTEXT_BINDING.json').read_text());ray=json.loads((C/'research217_bootstrap/crossover30/FOLDED217_BLANK_RAY.json').read_text());z=json.loads((C/'research217_pairing_macros/ZERO_FLOW_PROOF.json').read_text())
assert bind['blank_endpoint']['step']==312909 and bind['blank_endpoint']['clean']['registers']==[3,0,0,0,3,0,0,0,0]
assert [e['step']for e in bind['boot_exceptions']]==[79,160,306,471,1496]
assert (ray['prefix_steps'],ray['state'],ray['head'],ray['ones'])==(85,35,7,[-3,-2])
assert [z[k]for k in ['virtual_primitives','virtual_macro_calls','enabled_edges']]==[2576,260,3215]
checks+=['raw218 accepted root seed and five regenerated bootstrap exceptions','folded217 exact85 ray scope remains separate','codec abstract2576/260/3215 census']
source=(D/'replay_selected.py').read_text();portable=source.replace("P=Path('/tmp/zfc-intake191/K217_Search_Round_2026-10-20/K217_Search_Round_2026-10-20')","P=Path(sys.argv[1]).resolve()").replace("D=Path(sys.argv[1]).resolve(); D.mkdir(exist_ok=False)","D=Path(sys.argv[2]).resolve(); D.mkdir(exist_ok=False)")
assert portable!=source and portable.replace('P=Path(sys.argv[1]).resolve()',"P=Path('/tmp/zfc-intake191/K217_Search_Round_2026-10-20/K217_Search_Round_2026-10-20')").replace('D=Path(sys.argv[2]).resolve(); D.mkdir(exist_ok=False)','D=Path(sys.argv[1]).resolve(); D.mkdir(exist_ok=False)')==source
ast.parse(portable);(D/'replay_portable.py').write_text(portable);(D/'portable-path-only.diff').write_text(''.join(difflib.unified_diff(source.splitlines(True),portable.splitlines(True),fromfile='actual/replay_selected.py',tofile='portable/replay_portable.py')))
docs=json.loads((D/'literal-review.json').read_text())['reviewed_document_pins']
review={'status':'FULL_SOURCE_REVIEW_AND_SELECTED_FRESH_REPLAY_PASS','reviewer':'drop_contract','source_number':148,'archive':'K217_Search_Round_2026-10-20.zip','arrival':'7071e5041ee316d087661b658362feed159901ef','placement_commit':'4a1218d87802388107b2b6a922af47faf5b53b83','ordinary_full_read_pins':docs,'full_read_additional':['research217_bootstrap/README.md','research217_bootstrap/crossover30/README.md','research217_hb_rbc/RESULTS.md'],'executable_closure_review':'All eight direct leaves and their local imported closure were fully read before execution; see dossier and source-pins.json. No delivered code changed.','actual_aggregate_sha256':H(D/'replay1/result.json'),'actual_jobs':8,'actual_failures':0,'new_runtime':{k:proof[k]for k in ['cases','rules','row_coverage','minimum_duration','unknown_windows','seconds','cases_sha256']},'independent_own_metadata_parser':{'path':'review_metadata.py','result':'literal-review.json','scope':'Inert literal/source/CFG comparison; no supplied import or machine execution.'},'final_consistency_checks':checks,'findings':['No mathematical blocker found in the fully read ordinary arguments.','No blank217 consistency candidate: exact folded-table ray at85; raw218 startup at312909 belongs to a different table.','H/PW uniform native/enumerator proof is substantive but source prices do not meet allocation target.','Membership/mixed invariants retain stated axiom restrictions; code4 finite proof is not alone a universal obstruction.','Codec theorem transports syntax and labels, not raw pairing, addition or whole enumerator.','Bounded searches and allocator failures are not lower bounds.'],'independent_peer_status':'This is drop_contract’s source review and own execution audit. No new second-agent review of this whole dossier is claimed. Submitted independent reviews remain submitted evidence.','second_read_targets':['research217_native_basis_review/NATIVE_CALIBRATION.md','research217_native_basis_review/THREE_FIELD_ENUMERATOR_BRIDGE.md','research218_round2_rho8/MIXED_ORIENTATION_UNION_OBSTRUCTION.md','research218_round2_rho8/ALL_MEMBERSHIP_FOURTH_OBSTRUCTION.md','research217_mixed_tag_basis/MIXED_R_I_OBSTRUCTION.md','research217_codec_pairing/CODEC_ISOMORPHISM.md'],'exclusions':['No Lean/Coq/Rocq','No delivery manifest or wrapper replay','No broad searches','No unchanged primary initialized runtime','No modified relay runtime','No candidate acceptance or lower bound']}
(D/'review.json').write_text(json.dumps(review,indent=2)+'\n')
closure=[Path(x['argv'][-1]).relative_to(C).as_posix()for x in r['jobs']]+['research217_encoding/prefix_kernel.py','k223_merged_runtime_audit/runtime/symbolic_runtime.py','k223_merged_runtime_audit/runtime/independent_runtime.py','research218_published_encoding/audit_construction.py','research218_encoding/price_sources.py','research218_encoding/direct_screen.py','research218_encoding/mixed_detours.py','research218_round2_encoding/reassociate_four_increments.py','research218_round2_encoding/compose_rho_nop.py']
pins={p:H(A/p)for p in closure};assert all(H(C/p)==h for p,h in pins.items());(D/'source-pins.json').write_text(json.dumps({'scope':'Selected reviewed direct leaf and local code-closure pins; inherited modules may be retained elsewhere by intake.','files':pins},indent=2)+'\n')
B=D/'publication-bundle';B.mkdir(exist_ok=False);maps=[]
def put(src,rel,compress=False):
 dst=B/rel;dst.parent.mkdir(parents=True,exist_ok=True)
 if compress:dst.write_bytes(gzip.compress(src.read_bytes(),mtime=0))
 else:shutil.copyfile(src,dst)
 maps.append({'actual_path':str(src),'bundle_path':rel,'source_sha256':H(src),'published_sha256':H(dst),'encoding':'gzip exact original bytes'if compress else 'exact bytes','bytes':dst.stat().st_size})
for name in ['dossier.md','reproduction.md','review.json','literal-review.json','source-pins.json','replay_selected.py','replay_portable.py','portable-path-only.diff','review_metadata.py','finalize_bundle.py']:put(D/name,name)
put(D/'replay1/result.json','actual.json')
for p in sorted((D/'replay1/logs').iterdir()):put(p,'logs/'+p.name)
outputs=[x['receipt']for x in r['jobs']]+['research217_encoding/crossover30_primary/sites.json','research217_encoding/crossover30_primary/raw218.native.tm','research217_bootstrap/crossover30/initialized217.native.tm','research217_bootstrap/crossover30/INITIALIZED217_TAG_CASES.json']
for rel in outputs:
 p=C/rel;gz=p.stat().st_size>200000;put(p,'output/'+rel+('.gz'if gz else ''),gz)
publication={'status':'EVIDENCE_ONLY_BUNDLE_READY','destination_proposed':'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake191-source148','files':maps,'copied_pristine_or_execution_inputs':False,'delivered_code_edits':[],'own_portable_adapter':'Two literal path substitutions in own runner only; exact inverse verified and AST parsed, not executed. Original runner/actual paths retained.','scope':'No maintained files or Git mutation. Gzip recovers exact large JSON bytes; all raw stdout/stderr included. All machine/source outputs and selected receipts included.'}
(B/'publication-map.json').write_text(json.dumps(publication,indent=2)+'\n')
print(json.dumps({'status':publication['status'],'mapped_files':len(maps),'bytes':sum(x['bytes']for x in maps),'review_sha256':H(D/'review.json'),'publication_map_sha256':H(B/'publication-map.json')},indent=2))
