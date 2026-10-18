#!/usr/bin/env python3
"""Own static intake-plan writer: no delivery imports, execution, or repo writes."""
from pathlib import Path
import json,hashlib,collections,subprocess,re
W=Path('/tmp/zfc-intake-165-planning'); R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
I=json.loads((W/'inventory.json').read_text()); H=json.loads((W/'history-matches.json').read_text()); A=I['archives'][0]
P=Path(A['extraction'])/A['roots'][0]; HOST='SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels'
def d(p):
 p=Path(p); b=p.read_bytes();return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)}
def write(name,v):
 p=W/name;assert not p.exists();p.write_text(json.dumps(v,indent=2)+'\n');return d(p)
files=[];targets=set()
code_ext={'.py','.sh','.ps1','.wl','.wls','.lean','.cpp','.cc','.c','.h','.v','.hs','.ml','.mli','.smt2'}
archive_readmes={'README.md','reference/context246/README.md'}
for m in A['members']:
 p=Path(m['archive_member']).relative_to(A['roots'][0]); s=str(p); ext=p.suffix.lower()
 q={k:m[k] for k in ('archive_member','sha256','git_blob','bytes')};q['original_relative']=s;q['source_path']=m['path']
 if ext in {'.tex','.pdf'} or s in archive_readmes:
  q.update(disposition='archive_only',reason='Addition main manuscript/PDF/TeX source or nested reference delivery README; recover unchanged from arrival archive.')
 else:
  folder='code/' if ext in code_ext or p.name in {'Makefile','makefile','GNUmakefile','CMakeLists.txt'} else '' if ext in {'.md','.rst'} or p.name.lower().startswith(('notice','license','copying','readme')) else 'data/'
  slug='69-blocks-'+s.replace('/','-')
  if slug.endswith('.log'):slug += '.txt'
  target=HOST+'/'+folder+slug
  if len('C:\\ProveIt\\'+target)>199:
   # Explicit shortened basename plus identity suffix; full original path remains in map.
   slug='69-blocks-'+p.stem[:65]+'-'+hashlib.sha256(s.encode()).hexdigest()[:10]+''.join(p.suffixes)
   if slug.endswith('.log'):slug+='.txt'
   target=HOST+'/'+folder+slug
  assert target not in targets and not (R/target).exists(),target;targets.add(target)
  q.update(disposition='place_unchanged',target=target,windows_path_length=len('C:\\ProveIt\\'+target),renamed=s!=target)
 files.append(q)
count=collections.Counter(q['disposition'] for q in files)
placement={'status':'PROPOSAL_ONLY_NO_PLACEMENT','batch':165,'batch_manuscript':'01','host_source':69,'host':HOST,'prefix':'69-blocks-','archive':{k:A[k] for k in ('archive','archive_blob','sha256','bytes','first_arrival')},'inspected_proveit_pin':'8cdc55ff9281b0aaba49bf74b0b225d57f12b893','files':files,'counts':{'total':len(files),'placed':count['place_unchanged'],'archive_only':count['archive_only'],'history_hit_members':A['member_history_hits'],'new_blob_members':len(files)-A['member_history_hits'],'max_windows_path_length':max(q.get('windows_path_length',0) for q in files)},'retire_only_after_exact_placement':[A['archive'],H['exact_reintroduced_archive']['path']],'duplicate_retirement_evidence':d(W/'history-matches.json'),'checksum_manifest_work':False,'line_ending_work':False,'root_only_next_steps':['Freshly re-extract committed archive before copying/staging; retain byte identity.','Use existing ignore/attribute rules; never force a checksum or line-ending exception.','Verify all staged ancillary blobs against fresh arrival; commit placement before reconciliation.','Retire only these two tracked ZIPs in that placement commit; preserve incoming README.']}
write('placement-proposal.json',placement)
# Commands use the same complete disposable package copy. Inherited verifier coverage is de-duplicated, no missing suite silently omitted.
jobs=[]
def job(key,argv,cwd='.',timeout=120,scope='',writes=None,postcheck=None,read='entrypoint read; reached inherited proof-engine closure inventoried, not freshly re-proved'):
 jobs.append({'key':key,'argv':['python3','-B',*argv],'cwd_relative_to_copy':cwd,'process_group_timeout_seconds':timeout,'scope':scope,'writes':writes or [],'postcheck':postcheck,'source_read_scope':read})
job('main', ['code/verify_all.py'],timeout=180,scope='14 named jobs:11 subprocess checks plus3 in-process checks. Original246 folds/macros/8391 guards/410735 blank; invariant recomputation;8385 admitted guards and block/workspace/arithmetic controls; exact rejected-table and reachable-reference witness; recorded action-domain identity only.',writes=['results/','code/source-exactroot-affine-verification.json','temporary nested context246 copy'],postcheck={'results/verification-summary.json':{'status':'PASS','new_sub246_consistency_machine':False,'new_kernel_endpoint':False,'jobs_length':14}})
base='reference/context246'
job('reference-rebuild', ['code/rebuild_machines.py','--check'],base,scope='Exact reference table reconstruction; complements four reference jobs already called by main.')
job('reference-rendered-table', ['code/render_table.py','--check'],base,scope='Exact TeX transition-table content comparison; does not run TeX.')
job('reference-literal-instructions', ['code/check_literal_instructions.py','--program','sources/Prog254.v','--table','machine/zfc_prefix246_old.tm','--output','results/literal-instructions.json'],base,scope='Full delivered finite literal instruction regression, without --quick; supplements universal affine audit.',writes=['reference/context246/results/literal-instructions.json'])
job('reference-local-contracts', ['code/check_local_contracts.py'],base,scope='Delivered finite local-contract regression.',writes=['reference/context246/results/literal-local-contracts.json'])
job('reference-prefix-boxes', ['code/check_prefix_boxes.py'],base,scope='Delivered finite prefix-box regression.',writes=['reference/context246/results/prefix-box-regression.json'])
job('reference-independent-audit', ['reviews/audit246.py','reviews/prior250'],base,scope='Independent macro proof engine, all8391 guards, sparse/dense410735 blank; consumes archived prior250 proof code after substituting exact246 table.',writes=['reference/context246/reviews/audit246-results.json'])
job('reference-independent-rebuild', ['code/independent_rebuild.py','--baseline','sources/prefix250_old.tm','--output','review-rebuilt246'],base,scope='Second table reconstruction and full blank support. Compare its two table outputs against delivered246 tables.',writes=['reference/context246/review-rebuilt246/'],postcheck={'byte_equal_pairs':[['review-rebuilt246/zfc_fold246_old.tm','machine/zfc_prefix246_old.tm'],['review-rebuilt246/zfc_fold246.tm','machine/zfc_prefix246.tm']]})
job('emitter-baseline', ['search/context/recompile_decoder.py','--output','results/recomputed-emitter-baseline.json'],scope='Complete original contextual-emitter initialized baseline. Exit0 alone is insufficient: explicitly require203decoder nodes,246runtime states,8391cases,empty failures. No source-change proof or blank initialization follows.',writes=['results/recomputed-emitter-baseline.json'],postcheck={'results/recomputed-emitter-baseline.json':{'decoder_nodes':203,'states':246,'cases':8391,'failures':[]}})
# Only recorded durations; do not present as fresh or promise a runtime.
delivered=json.loads((P/'results/verification-summary.json').read_text());ref=json.loads((P/base/'results/verification-summary.json').read_text())
plan={'status':'SOURCE_ONLY_ROOT_EXECUTION_PROPOSAL_NO_PROGRAM_RUN','package':str(P),'main_manuscript':d(P/'report.tex'),'main_driver':d(P/'code/verify_all.py'),'additional_source_read':['README.md','report.tex (all942 lines)','results.tex','NOTICE.md','PROVENANCE.json','reviews/source-block-workspace-audit.md','search/README.md','rejected/README.md','code/verify_all.py','all code/check_*.py','code/verify_union_obstructions.py','code/threshold_literal_witness.py','code/program.py','code/common.py','code/source_abstract_invariant.py','code/source_constant_domains.py','code/arithmetic_blocks.py','code/workspace_affine.py','code/workspace_block_affine.py','code/arithmetic_affine.py','reference/context246/code/verify_all.py','reference/context246/code/check_folds.py','reference/context246/reviews/audit246.py','search/context/recompile_decoder.py','search/context/search_common.py'],'runtime_dependencies':{'python':'>=3.10, standard library only, assertions enabled','network':False,'proof_compiler':False,'cpp_compiler':False,'tex_engine':False},'execution_policy':{'copy_only':True,'create_new_output_directory':True,'use_new_disposable_copy_per_attempt':True,'preserve_stdout_stderr_terminal_status_per_job':True,'clear_environment':['PYTHONOPTIMIZE','PYTHONPATH'],'PYTHONDONTWRITEBYTECODE':'1','do_not_run':['reference/context246/code/check_hashes.py','make integrity','optional discovery/search families','Lean/Rocq compilers','make pdf'],'no_source_adapter_required':True,'identity_checks_note':'No SHA256SUMS/delivery checksum wrapper runs. Existing semantic source/table identity checks inside the substantive algorithms remain; no separate manifest audit or line-ending work is proposed.'},'commands':jobs,'coverage_accounting':{'main_named_jobs':14,'supplemental_jobs':8,'inherited_verify_all':{'nine_commands':9,'already_covered_by_main':4,'five_missing_commands_listed_above':True},'checksum_only_wrapper_excluded':True,'recorded_domain_comparison_is_not_replay':True,'discovery_searches_not_default_verification':True,'prior250_induction_and_instruction_engines':'Executed through reference-independent-audit with exact246 substitution; their standalone250 wrapper is not an additional new246 suite.'},'delivered_durations_only':{'main_summary_seconds':delivered['seconds'],'reference_nine_job_summary_seconds':ref['seconds'],'root_suggested_main_bound_seconds':180,'root_suggested_supplemental_each_seconds':120,'fresh_measurement':None},'unexecuted_scope':'This plan does not claim any fresh PASS; root must inspect commands and relevant code before executing supplied programs. Complete proof-engine soundness is not re-established by this preflight inventory.'}
write('execution-plan.json',plan)
queue=[]
for a in I['archives']:
 top=[m for m in a['members'] if m['archive_member'].count('/')==1 and (m['archive_member'].endswith('.tex') or Path(m['archive_member']).name.lower().startswith('readme'))]
 oldtrees=sorted({t['commit'] for t in H['placement_tree_checks'] if {m['git_blob'] for m in a['members']} & {m['git_blob'] for m in t['matching_tree_members']}})
 queue.append({'queue_index':a['queue_index'],'archive':a['archive'],'archive_blob':a['archive_blob'],'archive_sha256':a['sha256'],'arrival':a['first_arrival'],'members':a['member_count'],'member_history_hits':a['member_history_hits'],'new_member_blobs':a['member_count']-a['member_history_hits'],'prior_placement_trees':oldtrees,'top_delivery_files':[{'path':m['archive_member'],'git_blob':m['git_blob'],'historical_placed_blob':bool(H['hits'].get(m['git_blob']))} for m in top],'disposition':'SELECT_BATCH165_LOCAL69' if a['queue_index']==1 else 'EXACT_SOURCE68_DUPLICATE_RETIRE_NO_NEW_NUMBER' if a['archive']==H['exact_reintroduced_archive']['path'] else 'QUEUED_UNPROCESSED_NO_LOCAL_NUMBER_ASSIGNED'})
write('queue.json',{'inventory':d(W/'inventory.json'),'history':d(W/'history-matches.json'),'archives':queue,'count':len(queue),'caution':'Missing top-main history hits alone do not prove novelty: report.tex/README/PDF of additions were intentionally archive-only. Exact duplicate decision uses original full archive and all273 original ancillary tree bindings. Other queued archives have new delivered ancillary blobs and remain unprocessed; titles have not been treated as theorem identities.'})
print(json.dumps({'placement':placement['counts'],'execution_jobs':len(jobs),'queue':len(queue)},indent=2))
