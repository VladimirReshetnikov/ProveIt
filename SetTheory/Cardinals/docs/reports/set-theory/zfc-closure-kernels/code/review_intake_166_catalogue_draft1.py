"""Own metadata review of existing root catalogue outputs; no builder invoked."""
from pathlib import Path
import difflib
import hashlib
import json
import re

W = Path('/tmp/zfc244-248bc05936-inspection/intake')
R = Path('/home/codex/.codex/worktrees/ec20/Proofs')
F = Path('/tmp/zfc-intake-166-catalogue-final')
B = Path('/tmp/zfc-intake-166-catalogue-build')
A = Path('/tmp/zfc-intake-166-catalogue-audit.json')
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
desc = lambda p: dict(path=str(p), sha256=sha(p))
checks = []
def check(value, label):
    assert value, label
    checks.append(label)

final = json.loads((F/'replacement-map.json').read_text())
preview = json.loads((W/'catalogue-preview-v2/replacement-map.json').read_text())
check(final['write']=='be13ec69d7e74fd69674966e4c88698400e4066f', 'exact actual write commit')
check(len(final['files'])==4, 'exact four authored catalogue text replacements')
for p,f in zip(preview['files'], final['files']):
    check(p['target']==f['target'] and p['before_sha256']==f['before_sha256'], f['target']+' mapping')
    check(sha(p['replacement'])==p['after_sha256'] and sha(f['replacement'])==f['after_sha256'], f['target']+' exact proposed and final bytes')
    check(Path(f['replacement']).read_text()==Path(p['replacement']).read_text().replace('WRITE166SHA',final['write'][:10]),f['target']+' only finalized commit substitution')
    check(sha(R/f['target']) in (f['before_sha256'],f['after_sha256']),f['target']+' current maintained before or installed exact final')
check(sha(F/'catalogue.patch')==final['patch_sha256'],'final patch hash')
audit=json.loads(A.read_text())
check(audit['status']=='PASS' and audit['batch']==166,'root actual audit terminal PASS')
check((audit['host_sources'],audit['collection_reports'],audit['placed'],audit['archive_only_at_collection_placement'],audit['recovered'])==(70,290,170,21,191),'source, placement and report census')
check(sum(audit['categories'].values())==290,'category sum')
check((audit['full_cases'],audit['full_rules'],audit['full_binary_rows'],audit['portable_smoke_cases'])==(8391,2315075,488,1),'fresh replay scope')
check(audit['retained_four_jobs_are_evidence_retention_not_additional_independent_engine'],'retained replay scope')
check(audit['subsequent_external_endpoint_record_sha256']=='313c078f066db3452a5e6cb37ef5b8dbb6b515f302a0350b9fd3c0f3ad4abf34' and audit['internal_PA_open'],'dated endpoint and PA scope')
check(not audit['pdf_build_or_visual_review_claimed'],'audit does not substitute for build or visual review')
build=json.loads((B/'verification.json').read_text())
check(build['status']=='BUILT_VISUAL_REVIEW_PENDING' and build['batch']==166,'root actual completed build record')
manifest=F/'files/SetTheory/Cardinals/docs/reports/manifest.tex'
check(sha(manifest)==sha(B/'manifest.tex')==build['source_sha256']==build['built_source_sha256'],'exact authored and built manifest source')
check(sha(B/'manifest.pdf')==build['pdf_sha256'],'exact built PDF')
check(not build['preview_with_write_placeholder'] and 'WRITE166SHA' not in manifest.read_text(),'actual commit in built source')
check(len(build['commands'])==3,'three recorded TeX passes')
for i,c in enumerate(build['commands'],1):
    log=B/f'pass{i}.txt'
    check(c['pass_number']==i and c['returncode']==0 and c['command']==['pdflatex','-interaction=nonstopmode','-halt-on-error','manifest.tex'],'pass '+str(i)+' exact command and success')
    check(sha(log)==c['log_sha256'],'pass '+str(i)+' raw output identity')
    check('Output written on manifest.pdf (130 pages,' in log.read_text(),'pass '+str(i)+' terminal output')
bad=[line for line in (B/'manifest.log').read_text().splitlines() if re.search(r'(^!|LaTeX Warning|Package .* Warning|Overfull|Underfull|undefined|multiply defined|duplicate.*destination)',line)]
check(not bad and not build['final_warnings_or_boxes'],'no final diagnostics')
check(build['pages']==130 and 'Pages:           130' in (B/'pdfinfo.txt').read_text(),'PDF page count')
fontrows=[re.search(r'\s+(yes|no)\s+(yes|no)\s+(yes|no)\s+\d+\s+\d+\s*$',s) for s in (B/'pdffonts.txt').read_text().splitlines()[2:]]
check(len(fontrows)==build['font_records']==29 and all(x and x.group(1)=='yes' for x in fontrows),'all 29 font records embedded')
check(build['rendered_pages']==[1,2,41,122,123,124,125,126,127,128,129,130],'all changed/host pages rendered')
pages=[]
for i in build['rendered_pages']:
    p=B/f'page-{i}.png'
    check(p.read_bytes().startswith(b'\x89PNG\r\n\x1a\n'),'page '+str(i)+' available PNG')
    pages.append(desc(p))
check(build['visual_review_pending'],'no actual visual-review claim by this metadata reviewer')
check(build['proof_compiler_calls']==audit['proof_compiler_calls']==0,'no proof compiler in catalogue workflow')
support=json.loads((W/'catalogue-preview-v2/additive-review-map.json').read_text())
for x in support['files']:
    check(sha(x['source'])==sha(R/x['target'])==x['sha256'],x['target']+' installed additive review bytes')

record=dict(status='EXISTING_CATALOGUE_AUDIT_BUILD_METADATA_REVIEW_PASS',findings=[],
            reviewer_role='Author of catalogue prose and audit/build helper adaptations; independent of root execution. This is metadata review, not an independent source-fidelity or visual review.',
            reviewer_source=desc(Path(__file__)),final_map=desc(F/'replacement-map.json'),audit=desc(A),build=desc(B/'verification.json'),
            selected_manifest=desc(manifest),pdf=desc(B/'manifest.pdf'),rendered_pages=pages,
            checks=checks,check_count=len(checks),supplied_execution=False,build_invoked=False,proof_compiler_invoked=False,
            visual_review_performed=False,visual_review_left_to_root=True)
out=W/'catalogue-audit-build-metadata-review.json'
check(not out.exists(),'new immutable reviewer record')
out.write_text(json.dumps(record,indent=2)+'\n')

# A separate source-only recommendation; frozen catalogue replacements are untouched.
product=F/'files/Computability/README.md'
old=product.read_text()
current='''external equivalence between the exact routed 245-state machine's blank
nonhalting and Con(ZFC), improving its earlier 246- and 252-state endpoints. The user's target remains an equivalence provable inside PA.'''
replacement='''external equivalence between the exact compensated 244-state machine's blank
nonhalting and the stated ZF and ZFC consistency propositions, improving its
earlier routed 245-, 246- and 252-state endpoints. The user's target remains an
equivalence provable inside PA.'''
assert old.count(current)==1
new=old.replace(current,replacement)
current='''attributed literal 254-state baseline and the checked 252-, 246- and routed
245-state external successors.'''
replacement='''attributed literal 254-state baseline and the checked 252-, 246-, routed
245- and compensated 244-state external successors.'''
assert new.count(current)==1
new=new.replace(current,replacement)
current='''The exact 246 and routed 245 tables now have complete external simulations
and blank startups. The displayed local 250 results, separate 247 candidate,
and internally provable PA comparison retain their stated limits.'''
replacement='''The exact 246 and routed 245 tables have complete external simulations and
blank startups. Checked positive-block transport from routed 245 establishes
the compensated 244 external endpoint. The displayed local 250 results,
separate 247 candidate, and internally provable PA comparison retain their
stated limits.'''
assert new.count(current)==1
new=new.replace(current,replacement)
recommendation=W/'computability-current-status-recommendation.diff'
recommendation.write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='catalogue-final/Computability/README.md',tofile='root-proposed/Computability/README.md')))
print(json.dumps(dict(review=desc(out),recommendation=desc(recommendation),check_count=len(checks)),indent=2))
