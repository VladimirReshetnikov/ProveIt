#!/usr/bin/env python3
"""Own metadata-only guard emission from the actual Rotation244 parent."""
from pathlib import Path
import ast,difflib,hashlib,json,re
H=Path(__file__).resolve().parent
P=H.parent/'table-rotation/run2/verification.json'
U=Path('/tmp/zfc-routing245-endpoint-actual/run2/verification.json')
T=Path('/tmp/zfc244-compensated-lean/blocks/check.py')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
desc=lambda p:dict(path=str(p),sha256=sha(p))
assert sha(P)=='339ac1eb684bf2b0e2dca81f6a5d693abf2f3fe7079d0c924e5cf2ab870f3466'
assert sha(U)=='41ff9364f37d9eb33ff1eb2b4bbc0e5f17f0a44ac02a4a7dcdbdfa6c5b1ccf87'
e=json.loads(P.read_text());u=json.loads(U.read_text());inv=json.loads((H/'source-inventory.json').read_text())
assert e['status']=='PASS' and e['named_axiom_probes']==7 and e['callers']==7 and e['warnings']==0
assert e['compiler']==u['compiler'] and e['before']==e['after']
f=e['fresh_modules'][0]
rows=e['reused_modules']+[dict(module=f['module'],source=e['source']['path'],source_sha256=f['source_sha256'],object=f['path'],object_sha256=f['sha256'])]
assert {q['module']for q in rows}=={'BusyBeaver.Core','BusyBeaver.ZFC.TableRotation244'}
for q in rows:
 for k in ['source','object']:assert sha(q[k])==q[k+'_sha256']
tools=u['toolchain_providers'];assert {q['module']for q in tools}=={'Init','Lean.Elab.Tactic.Omega'}
assert all(q in tools for q in e['toolchain_providers'])
b=dict(parent=desc(P),tool_parent=desc(U),compiler=e['compiler'],reused_modules=rows,toolchain_providers=tools,
 scope='Core and fresh TableRotation244 selected from actual run2; exact Init+Omega tool objects additionally selected from passed BinaryRouting245. No project provider from the broad binary endpoint is imported.',
 static_inputs=[desc(H/'source-inventory.json'),inv['generator']]+inv['inputs'])
(H/'boundary.json').write_text(json.dumps(b,indent=2)+'\n')
s=T.read_text()
def sub(old,new):
 global s
 assert old in s,old
 s=s.replace(old,new)
sub('Seven exact compensated244 blocks and their endpoints; three project providers.','Exact Combined243 table/embedding; Core+Rotation244 with Init+Omega.')
sub('/tmp/zfc244-compensated-lean/blocks',str(H))
sub('Compensated244Blocks','TableCombined243')
sub("PREFIX='SetTheory.BusyBeaver.ZFC.TableCombined243.'","PREFIX='SetTheory.BusyBeaver.ZFC.'")
probes=[q.removeprefix('SetTheory.BusyBeaver.ZFC.')for q in inv['probe_names']]
s=re.sub(r'^PROBES=.*$','PROBES='+repr(probes),s,flags=re.M)
for key,p in [('SOURCE_SHA',H/'TableCombined243.lean'),('AUDIT_SHA',H/'Audit.lean'),('BOUNDARY_SHA',H/'boundary.json'),('PARENT_SHA',P)]:
 s=re.sub('^'+key+'=.*$',key+'='+repr(sha(p)),s,flags=re.M)
sub("==(53,6),'Wrong parent.'","==(7,7),'Wrong parent.'")
sub('len(ns)==53','len(ns)==7')
sub("imports(S)==['BusyBeaver.ZFC.TableCompensated244']","imports(S)==['BusyBeaver.ZFC.TableRotation244','Lean.Elab.Tactic.Omega']")
sub("==14,'Typed callers changed.'","==6,'Typed callers changed.'")
sub("len(reused)==3 and set(projects)=={'BusyBeaver.Core','BusyBeaver.ZFC.TableRouting245','BusyBeaver.ZFC.TableCompensated244'}","len(reused)==2 and set(projects)=={'BusyBeaver.Core','BusyBeaver.ZFC.TableRotation244'}")
sub("q['module'] == 'BusyBeaver.ZFC.TableCompensated244'","q['module'] == 'BusyBeaver.ZFC.TableRotation244'")
sub("    require(tools==e['toolchain_providers']and {q['module']for q in tools}=={'Init','Lean.Elab.Tactic.Omega'},'Wrong tool boundary.')",'''    TP=pin(b['tool_parent']['path'],'41ff9364f37d9eb33ff1eb2b4bbc0e5f17f0a44ac02a4a7dcdbdfa6c5b1ccf87')
    require(b['tool_parent']['sha256']=='41ff9364f37d9eb33ff1eb2b4bbc0e5f17f0a44ac02a4a7dcdbdfa6c5b1ccf87','Tool evidence descriptor changed.')
    te=json.loads(TP.read_text())
    require(te['status']=='PASS'and te['compiler']==b['compiler']and te['before']==te['after']and te['all_input_provider_postchecks']and te['all_fresh_objects_unchanged_after_audit']and te['only_standard_axioms'],'Incomplete tool parent.')
    require(tools==te['toolchain_providers']and {q['module']for q in tools}=={'Init','Lean.Elab.Tactic.Omega'},'Wrong tool boundary.')
    require({q['module']for q in e['toolchain_providers']}=={'Init'}and all(q in tools for q in e['toolchain_providers']),'Rotation tool parent changed.')''')
sub("require(e['before'].get(str(pp))==e['after'].get(str(pp))==q['object_sha256'],'Absent parent tool input.')","require(te['before'].get(str(pp))==te['after'].get(str(pp))==q['object_sha256'],'Absent parent tool input.')")
sub("scope='Seven paired positive blocks and seven new endpoint identities on arbitrary Core finite-support tapes; explicit finite read premises; no whole-run theorem.'","scope='Exact486-row Combined243 table; embedding into Rotation244;480 common actions and local row facts. No runtime or halting equivalence theorem.'")
sub('provider_evidence=[dict(path=str(E),sha256=PARENT_SHA)]','provider_evidence=[dict(path=str(E),sha256=PARENT_SHA),dict(path=str(TP),sha256=b[\'tool_parent\'][\'sha256\'])]')
sub('exact_project_prerequisite_count=3','exact_project_prerequisite_count=2')
sub('named_axiom_probes=14,callers=14','named_axiom_probes=53,callers=6')
sub("obj=cache/rel(MODULE);require(not obj.exists(),'Target already exists.');run('source',ss,obj)","obj=cache/rel(MODULE);require(not obj.exists(),'Target already exists.');obj.parent.mkdir(parents=True,exist_ok=True);run('source',ss,obj)")
ast.parse(s);assert not(H/'check.py').exists();(H/'check.py').write_text(s)
(H/'guard-from-blocks.diff').write_text(''.join(difflib.unified_diff(T.read_text().splitlines(True),s.splitlines(True),fromfile=str(T),tofile=str(H/'check.py'))))
tail=s[s.index('    def save():'):].replace('named_axiom_probes=53,callers=6','named_axiom_probes=14,callers=14').replace('obj.parent.mkdir(parents=True,exist_ok=True);','')
assert tail==T.read_text()[T.read_text().index('    def save():'):]
out=dict(status='AUTHOR_SOURCE_ONLY_GUARD_REVIEW_PASS',guard=desc(H/'check.py'),boundary=desc(H/'boundary.json'),source=inv['source'],audit=inv['audit'],parent=desc(P),tool_parent=desc(U),template=desc(T),emitter=desc(Path(__file__)),projects=2,tools=['Init','Lean.Elab.Tactic.Omega'],probes=53,callers=6,execution_tail_exact_except_census_and_output_parent_creation=True,findings=[],execution='Own metadata emitter only; no guard/compiler/version query.')
(H/'guard-author-review.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
