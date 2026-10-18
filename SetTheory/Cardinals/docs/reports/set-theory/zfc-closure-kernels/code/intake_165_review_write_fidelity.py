"""Independent source-fidelity and existing metadata review; never imports delivery code."""
from pathlib import Path
import hashlib,json,re,subprocess,difflib,ast

R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
B=Path('/tmp/zfc-intake-165-planning');F=B/'write-final'
H=R/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels'
P=B/'extracted/zfc-sub246-research-20261018/zfc-sub246-research-20261018'
checks=[]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(Path(p).read_text())
def desc(p):return dict(path=str(p),sha256=sha(p))
def ok(v,s):
    assert v,s
    checks.append(s)
def pin(p,h):ok(sha(p)==h,'hash '+str(p))
def git(*args):return subprocess.run(['git',*args],cwd=R,check=True,capture_output=True).stdout
def stripped(x):
    if isinstance(x,dict):return {k:stripped(v) for k,v in x.items() if k not in ['seconds','time_seconds','elapsed_seconds']}
    if isinstance(x,list):return [stripped(v) for v in x]
    return x

pin(F/'publication-map.json','a6ad444ec7dd923ce928db1b526b2d9863d72366f6349bab8734d0e85a26f483')
m=load(F/'publication-map.json');ready=load(F/'readiness.json')
ok(m['batch']==165 and (m['host_sources'],m['collection_reports'],m['total_files'])==(69,290,88),'publication census')
planned={};total=0
for d in m['files']:
    target=(R/d['target']).resolve();ok(target.is_relative_to(H),'host-only target')
    ok(target not in planned,'unique target');planned[target]=Path(d['source'])
    pin(d['source'],d['sha256']);ok(Path(d['source']).stat().st_size==d['bytes'],'mapped byte count');total+=d['bytes']
ok(total==m['total_bytes'],'total mapped bytes')
for d in ready['files']:pin(d['path'],d['sha256'])
hr=m['host_readme_replacement'];pin(hr['source'],hr['sha256']);pin(R/hr['target'],hr['before_sha256'])
ok(hr['before_sha256']==ready['host_readme_before'],'host predecessor pinned')
patch=''.join(difflib.unified_diff((R/hr['target']).read_text().splitlines(True),Path(hr['source']).read_text().splitlines(True),fromfile=hr['target'],tofile=hr['target']))
ok(patch==Path(hr['patch']).read_text(),'exact README patch')
pin(R/ready['base_article']['path'],ready['base_article']['sha256'])
ok(all(p.name not in ['article.tex','article.pdf'] for p in planned),'base article excluded from writes')
planned[(R/hr['target']).resolve()]=Path(hr['source'])
link_count=0
for name in ['intake-165.md','intake-165-reproduction.md','README.md']:
    text=(F/name).read_text()
    for link in re.findall(r'\]\(([^)]+)\)',text):
        if '://' in link or link.startswith('#'):continue
        target=(H/link.split('#')[0]).resolve()
        ok(target in planned or target.is_file(),'resolved local link '+link);link_count+=1
ok(link_count==67==len(m['link_checks']),'67 independently resolved local links')
for d in m['link_checks']:
    ok((H/d['link'].split('#')[0]).resolve()==(R/d['target']).resolve(),'recorded link target')

placement=load(B/'placement-proposal.json');pin(B/'placement-proposal.json','c07a9154bf8d11513e6c57a94583366371945d938470d59e23d881b4f942a71e')
ok((placement['counts']['total'],placement['counts']['placed'],placement['counts']['archive_only'])==(466,454,12),'466/454/12')
ok(m['placement']==ready['placement']=='500381f8f1b4f450870895a642a2845a15a008ea','actual placement pin')
placed_tree={}
for line in git('ls-tree','-r',m['placement'],'--',str(H.relative_to(R))).decode().splitlines():
    meta,path=line.split('\t');placed_tree[path]=meta.split()[2]
recovery_row=next(d for d in m['files'] if d['target'].endswith('/intake-165-recovery.json'));recovery=load(recovery_row['source'])
ok(recovery['status']=='RECOVERED_AND_PLACED_BYTES_MATCH' and (recovery['files_recovered'],recovery['placed_pairs_compared'])==(466,454),'root recovery result')
recovered=Path(recovery['package_root']);placed=0;executable=[]
for d in placement['files']:
    p=P/d['original_relative'];pin(p,d['sha256']);pin(recovered/d['original_relative'],d['sha256'])
    if p.suffix in ['.py','.v','.lean','.cpp']:executable.append(d)
    if d['disposition']=='place_unchanged':
        pin(R/d['target'],d['sha256']);ok(placed_tree[d['target']]==d['git_blob'],'original placement blob');placed+=1
ok(placed==454 and len(executable)==93,'placed count and93 executable inputs')
hist=load(B/'history-matches.json');dup=hist['exact_reintroduced_archive']
ok(len(dup['placement_members'])==273 and dup['all_273_ancillary_placement_blobs_equal_archive'],'273 duplicate ancillary evidence')
for commit in [dup['original_arrival'],dup['reintroduced_arrival']]:
    ok(git('rev-parse',commit+':'+dup['path']).decode().strip()==dup['original_and_current_blob'],'duplicate exact Git archive blob')
prior_tree={}
for line in git('ls-tree','-r',dup['original_placement'],'--',str(H.relative_to(R))).decode().splitlines():
    meta,path=line.split('\t');prior_tree[path]=meta.split()[2]
for d in dup['placement_members']:ok(prior_tree[d['path']]==d['git_blob'],'duplicate original273 placement blob')
helper=(B/'recover_165.py').read_text();ast.parse(helper)
ok("MAP_SHA='"+sha(B/'placement-proposal.json')+"'" in helper,'recovery selected map')
ok("subprocess.check_output(['git'" in helper and 'exec(' not in helper and 'importlib' not in helper,'recovery read-only Git/data extraction scope')

main=load('/tmp/zfc-intake-165-source69-main-run1/execution.json');supp=load('/tmp/zfc-intake-165-source69-supplemental-run1/execution.json')
plan=load(B/'execution-plan.json');main_review=load(B/'source69-main-replay-review.json');supp_review=load(B/'source69-supplemental-replay-review.json')
ok(main['status']=='PASS' and main['exit_code']==0 and not main['timed_out'] and main['seconds']<main['timeout_seconds']==180,'main actual terminal')
ok(main['command']==['python3','-B','code/verify_all.py'],'main unchanged command')
ok(len(main['summary']['jobs'])==14 and all(d['status']=='PASS' for d in main['summary']['jobs']),'14 named jobs')
ok(not main['summary']['new_sub246_consistency_machine'] and not main['summary']['new_kernel_endpoint'],'main nonclaims')
ok(Path(main['stderr']).read_bytes()==b'' and Path(main['stdout']).read_text().count('PASS ')==14,'main raw14 PASS lines')
ok(load(Path(main['copy'])/'results/verification-summary.json')==main['summary'],'actual summary exact')
changed=[]
for d in placement['files']:
    rel=d['original_relative'];p=Path(main['copy'])/rel
    if sha(p)!=d['sha256']:
        ok(rel.startswith('results/') or rel=='code/source-exactroot-affine-verification.json','changed output location')
        if p.suffix=='.json':ok(stripped(load(p))==stripped(load(P/rel)),'changed JSON semantics after durations')
        changed.append(rel)
ok(sorted(changed)==sorted(main_review['changed_delivered_outputs']),'original twelve output differences')
ok(supp['status']=='PASS' and len(supp['records'])==8,'eight supplements')
for actual,j,review in zip(supp['records'],plan['commands'][1:],supp_review['jobs']):
    ok(actual['key']==j['key']==review['key'] and actual['command']==j['argv'],'supplement command')
    ok(actual['status']=='PASS' and actual['exit_code']==0 and not actual['timed_out'] and actual['seconds']<actual['timeout_seconds']==120,'supplement terminal')
    cwd=Path(actual['copy'])/j['cwd_relative_to_copy'];ok(cwd.resolve()==Path(actual['cwd']).resolve(),'supplement cwd')
    for role in ['stdout','stderr']:pin(actual[role],review[role]['sha256'])
    ok(Path(actual['stderr']).read_bytes()==b'','supplement stderr')
    for d in executable:pin(Path(actual['copy'])/d['original_relative'],d['sha256'])
    for k,v in (j.get('postcheck') or {}).items():
        if k=='byte_equal_pairs':
            for left,right in v:ok((cwd/left).read_bytes()==(cwd/right).read_bytes(),'independent table reconstruction bytes')
        else:
            data=load(Path(actual['copy'])/k);ok(all(data[q]==z for q,z in v.items()),'emitter203/246/8391/no failures')
    for role in ['stdout','stderr']:ok(Path(actual[role]) in planned.values(),'mapped supplemental raw '+role)
for review in [main_review,supp_review]:
    pin(review['execution']['path'],review['execution']['sha256']);pin(review['reviewer_source']['path'],review['reviewer_source']['sha256'])
ok(m['fresh_checks']==dict(main_named_jobs=14,supplemental_jobs=8,optional_searches_replayed=False,proof_or_TeX_builds=False),'publication replay scope')

ar=load(P/'results/arithmetic-block-controls.json');quiet=load(P/'results/quiet-blocks-rechecked.json')
ok((ar['blocks']['endpoint_count'],ar['blocks']['cases_with_extra_endpoints'],ar['blocks']['maximum_source_steps'])==(17643,4856,13),'arithmetic block counts')
ok(ar['blocks']['termination_reasons']==dict(undecidable_CD=8383,before_CH=1,CH_at_entry=1),'no cap stops')
ok(all((d['cases'],d['total_endpoints'],d['expanded_cases'],d['maximum_source_instructions'])==(8385,10563,2050,5) for d in quiet['records']),'quiet counts')
graphs=load(P/'results/union-obstructions.json');ok(len(graphs)==8 and sum(d['boundary_nodes'] for d in graphs)==19 and sum(d['edges'] for d in graphs)==128,'obstruction counts')
witness=load(P/'results/threshold-literal-witness.json');ok((witness['instructions_before_failure'],witness['absolute_binary_time'])==(1700,6012481),'reference witness counts')
ok(witness['original_source_at_mutant_pc']['source_steps']==146 and witness['original_source_at_mutant_pc']['physical_registers'][0]==10,'later theorem-stack discrepancy')
row_usage=load(P/'results/source-invariant-row-usage.json');ok(row_usage['symbolic_rows_all']==row_usage['symbolic_rows_valid']==472,'472 inspected rows retained')
domains=[load(P/'results'/x) for x in ['incoming-action-results.json','invariant-incoming-action-results.json','quiet-incoming-action-results.json','workspace-incoming-action-results.json','workspace-block-incoming-action-results.json','arithmetic-incoming-action-results.json']]
ok(all(d['tested']==254856 and d['states']==domains[0]['states'] for d in domains),'six recorded action domains, not search replay')
runtime=R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RuntimePerm252.lean'
ok('step : ∀ a b c, R a c → next a = some b →' in runtime.read_text(),'existing one-source-step interface')
ok('theorem halts_iff' in runtime.read_text(),'existing generic halting equivalence')
docs=[F/'intake-165.md',F/'intake-165-reproduction.md',F/'README.md',F/'host-readme.patch']
out=B/'independent-write-fidelity-review.json';ok(not out.exists(),'new immutable receipt')
result=dict(status='INDEPENDENT_SOURCE_FIDELITY_WRITE_REVIEW_PASS',findings=[],reviewer_role='Independent source-fidelity and existing metadata reviewer; no manuscript/prose/map/recovery/checker authorship, no supplied execution, no maintained edits.',
    publication_map=desc(F/'publication-map.json'),documents=[desc(p)for p in docs],source_manuscript=desc(P/'report.tex'),source_audit=desc(P/'reviews/source-block-workspace-audit.md'),notice=desc(P/'NOTICE.md'),recovery_helper=desc(B/'recover_165.py'),recovery_record=desc(recovery_row['source']),main_execution=desc('/tmp/zfc-intake-165-source69-main-run1/execution.json'),supplemental_execution=desc('/tmp/zfc-intake-165-source69-supplemental-run1/execution.json'),prior_replay_reviews=[desc(B/'source69-main-replay-review.json'),desc(B/'source69-supplemental-replay-review.json')],runtime_interface=desc(runtime),reviewer_source=desc(Path(__file__)),checks=len(checks),
    counts=dict(new_write_files=88,host_readme_replacement=1,mapped_bytes=total,links=67,source_files=466,placed_unchanged=454,archive_only=12,duplicate_ancillaries=273,main_jobs=14,supplemental_jobs=8),
    source_fidelity=['Full942-line manuscript and complete source audit read; delivered counts and substantive positive/negative claims retained.', 'Positive finite multi-source-block progress and whole-tape primary-value/offset relation kept distinct from existing checked one-source-step runtime API.', 'All-values mask closure distinguished from finite sampled controls; exact-root restriction, six prior exclusions, spare nonemptiness and reference gap40 are retained.', 'Closed tail trap rejects its consistency calibration under Con(ZFC); shortened-detector witness comes from the reference246 run and refutes the intended simulation, not every calibration.', 'Recorded search domains, finite sufficient screens, changed-macro exploratory cases, incomplete explorations and unverified changed blank starts are not upgraded to universal results.', 'Current routed245 external Lean endpoint and open internal PA comparison distinguished from historical reference246 and the delivery ordinary ZFC target; bare consistency/two-sided independence caveat retained.'],
    scope='Pre-installation write-map/source-fidelity/link review, not a full audit of every historical host paragraph or optional search checker. All88 proposed file bytes plus README successor/patch,466 recovered source members,454 current/original-placement pairs and273 prior duplicate placements bound. Existing14+8 raw records, executable inputs and semantic output/postchecks independently inspected without rerunning delivery code. Historical dossier/proposal pending labels remain unchanged records, with actual completion separately bound. No article/PDF rewrite, TeX/Lean/Rocq build, checksum-manifest verification, new machine bound or PA theorem follows.',
    supplied_execution=False,maintained_edits=False)
out.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n');print(json.dumps(desc(out)))
