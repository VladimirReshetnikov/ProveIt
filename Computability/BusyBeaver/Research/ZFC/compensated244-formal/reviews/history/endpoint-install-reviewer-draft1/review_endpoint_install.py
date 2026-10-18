#!/usr/bin/env python3
"""Own installed bytes and unbuilt default evidence review; no supplied execution."""
from pathlib import Path
import hashlib,json,ast,re,difflib
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');D=R/'Computability/BusyBeaver/Research/ZFC';B=Path('/tmp/zfc244-endpoint');O=Path(__file__).parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();d=lambda p:dict(path=str(p),sha256=sha(p));load=lambda p:json.loads(Path(p).read_text())
checks=[]
def check(x,s):
 assert x,s
 checks.append(s)
M=Path('/tmp/zfc244-endpoint-publication-paths.json');rows=load(M)
check(len(rows)==26 and len({q['path'] for q in rows})==26,'26 distinct mapped files')
for q in rows:
 p=R/q['path'];check(sha(p)==q['sha256'],'installed mapped '+q['path'])
 if q['origin'].startswith('/'):check(p.read_bytes()==Path(q['origin']).read_bytes(),'exact origin '+q['path'])
 check(p.suffix not in ['.olean','.ilean'] and '/cache/' not in str(p),'no distributed objects '+q['path'])
old=(B/'check.py').read_text();G=D/'check_binary_compensated244.py';new=G.read_text()
def cfg(text):return next(ast.literal_eval(n.value) for n in ast.parse(text).body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='CFG' for t in n.targets))
a,b=cfg(old),cfg(new);expected=dict(a,source=str(R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/BinaryCompensated244.lean'),audit=str(D/'binary_compensated244_audit.lean'))
check(b==expected,'exact two CFG path defaults only')
check(old.replace(repr(a),repr(b),1)==new,'all non-CFG execution bytes exact')
delta=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='actual-guard',tofile='maintained-guard'))
check(delta==(D/'compensated244-formal/endpoint/publication-defaults.diff').read_text(),'published default diff exact')
P=Path('/tmp/zfc244-maintained-prepare/endpoint/verification.json');r=load(P);actual=load(B/'run1/verification.json')
check(r['status']=='PREPARED_NOT_BUILT' and r['prepare_only'] and r['commands']==r['fresh_modules']==[],'unbuilt preparation has no proof commands/objects')
check(r['before']==r['after'] and r['all_input_provider_postchecks'],'before/after exact')
for p,h in r['before'].items():check(sha(p)==h,'prepared current input '+p)
check(len(r['before'])==1734,'1734 current preparation inputs')
for k in ['source','audit']:
 check(r[k]['path']==b[k] and sha(r[k]['path'])==sha(r[k]['snapshot'])==r[k]['sha256']==actual[k]['sha256'],'maintained '+k+' selection/snapshot/actual bytes')
check(r['reused_modules']==actual['reused_modules'] and r['toolchain_providers']==actual['toolchain_providers'],'exact actual dependency pairs and tools')
check(r['provider_evidence']==actual['provider_evidence'],'same pinned parent records')
check(r['project_module_count']==857 and r['exact_project_import_closure'] and len(r['reused_modules'])==857 and r['candidate_provider_count']==857 and not r['excluded_candidate_modules'],'857 exact selected providers')
projects={q['module']:q for q in r['reused_modules']};seen=set();tools={'Init'}
def visit(m):
 if m not in projects:tools.add(m);return
 if m in seen:return
 seen.add(m)
 for n in re.findall(r'^import\s+(\S+)\s*$',Path(projects[m]['source']).read_text(),re.M):visit(n)
for m in b['imports']:visit(m)
check(seen==set(projects)==set(b['expected_modules']) and tools=={'Init','Lean.Elab.Tactic.Omega'},'independent installed-provider DFS')
for q in r['actual_first_providers']:
 check(Path(q['actual_first']).resolve()==Path(projects[q['module']]['object']).resolve() and sha(q['actual_first'])==q['sha256'],'prepared actual first '+q['module'])
check(r['limits']==actual['limits'] and r['shared_wall_seconds']==120,'unchanged default resource/proof limits')
check(not any(r[k] for k in ['source_overridden','audit_overridden','compiler_version_query_performed','dependency_build','downloads']),'no overrides/version/build/download')
reviews=[]
for name in ['endpoint-source-review.json','endpoint-audit-repair-review.json','endpoint-guard-preparation-review.json','endpoint-actual-review.json','review_global_source.py','review_endpoint_guard.py','review_endpoint_actual.py']:
 p=D/'compensated244-formal/reviews'/name
 check(p.is_file() and p.read_bytes()==(O/name).read_bytes(),'exact preserved review/script '+name);reviews.append(d(p))
docs=[D/'compensated244_binary.md',D/'candidate-compensated244/README.md',D/'README.md',D/'compensated244_foundations.md',D/'compensated244_simulation.md'];links=[]
for p in docs:
 s=p.read_text()
 if p==D/'README.md':s=s[:s.index('The earlier external Lean baseline')]
 for link in re.findall(r'\]\(([^)]+)\)',s):
  if '://' in link or link.startswith('#'):continue
  target=(p.parent/link.split('#')[0]).resolve();check(target.exists(),'doc local link '+str(target));links.append(str(target))
page=docs[0].read_text();check(sha(B/'run1/verification.json') in page and actual['source']['sha256'] in page and actual['fresh_modules'][0]['sha256'] in page,'doc actual record/source/object pins')
check('857' in page and '1,734' in page and 'six named axiom probes and six' in page and '**zero warnings**' in page,'doc exact evidence census')
check('proof inside PA remains open' in page and 'not a fresh recompilation of all 857 providers' in page,'doc formal boundary')
receipt=dict(status='ENDPOINT_INSTALLED_DEFAULTS_AND_FINAL_DOCS_REVIEW_PASS',findings=[],reviewer_source=d(__file__),reviewer_role='Independent endpoint/publication/default/document reviewer; author of separate invariant prerequisite, not endpoint or publisher/guard/execution.',map=d(M),maintained_guard=d(G),preparation=d(P),actual_review=d(O/'endpoint-actual-review.json'),preserved_reviews=reviews,documents=[d(p) for p in docs],prior_document_receipts=[d(O/'foundations-installed-default-review.json'),d(O/'simulation-doc-supplement.json')],counts=dict(mapped_files=26,prepared_inputs=1734,project_providers=857,toolchain_providers=2,actual_probes=6,actual_callers=6,actual_warnings=0,preparation_proof_commands=0,preparation_fresh_modules=0),scope='The exact external244 blank/refutation and nonhalting/consistency calibration is now closed; ordinary all-function-tape proof, executable replay and Core finite-support Lean theorem remain distinguished. Internal PA proof, absolute consistency/nonhalting and unsupported independence claims are not inferred. Earlier immutable documentation reviews bind their earlier page versions.',supplied_execution=False,checks=checks,check_count=len(checks))
p=O/'endpoint-installed-default-doc-review.json';p.write_text(json.dumps(receipt,indent=2)+'\n');print(d(p))
