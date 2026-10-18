#!/usr/bin/env python3
"""Own metadata-only guard emitter; never executes guard or compiler."""
from pathlib import Path
import ast,difflib,hashlib,json,re
H=Path(__file__).resolve().parent
P=Path('/tmp/zfc-routing245-endpoint-actual/run2/verification.json')
T=Path('/tmp/zfc244-compensated-lean/table/check.py')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
desc=lambda p:dict(path=str(p),sha256=sha(p))
assert sha(P)=='41ff9364f37d9eb33ff1eb2b4bbc0e5f17f0a44ac02a4a7dcdbdfa6c5b1ccf87'
e=json.loads(P.read_text());inv=json.loads((H/'source-inventory.json').read_text())
row=next(q for q in e['reused_modules']if q['module']=='BusyBeaver.Core')
tools=[q for q in e['toolchain_providers']if q['module']=='Init'];assert len(tools)==1
for k in ['source','object']:
 p=Path(row[k]).resolve();assert sha(p)==row[k+'_sha256']==e['before'][str(p)]==e['after'][str(p)]
assert not re.findall(r'^import\s+(\S+)',Path(row['source']).read_text(),re.M)
first=next(q for q in e['actual_first_providers']if q['module']==row['module'])
assert Path(first['actual_first']).resolve()==Path(row['object']).resolve() and first['sha256']==row['object_sha256']
b=dict(parent=desc(P),compiler=e['compiler'],reused_modules=[row],toolchain_providers=tools,
 scope='Only exact import-free Core plus Init selected from passed BinaryRouting245. No broad dependency rebuild.',
 static_inputs=[desc(H/'source-inventory.json'),inv['generator']]+inv['inputs'])
(H/'boundary.json').write_text(json.dumps(b,indent=2)+'\n')
s=T.read_text()
def sub(old,new):
 global s
 assert old in s,old
 s=s.replace(old,new)
sub('Exact compensated244 table+embedding; Core+TableRouting245 only, no builds.','Exact Rotation244 table; only Core+Init, no builds.')
sub('/tmp/zfc244-compensated-lean/table',str(H))
sub('TableCompensated244','TableRotation244')
probes=[q.removeprefix('SetTheory.BusyBeaver.ZFC.')for q in inv['probe_names']]
s=re.sub(r'^PROBES=.*$','PROBES='+repr(probes),s,flags=re.M)
for k,p in [('SOURCE_SHA',H/'TableRotation244.lean'),('AUDIT_SHA',H/'Audit.lean'),('BOUNDARY_SHA',H/'boundary.json')]:
 s=re.sub('^'+k+'=.*$',k+'='+repr(sha(p)),s,flags=re.M)
sub("imports(S)==['BusyBeaver.ZFC.TableRouting245','Lean.Elab.Tactic.Omega']","imports(S)==['BusyBeaver.Core']")
sub("==6,'Typed callers changed.'","==7,'Typed callers changed.'")
sub("len(reused)==2 and set(projects)=={'BusyBeaver.Core','BusyBeaver.ZFC.TableRouting245'}","len(reused)==1 and set(projects)=={'BusyBeaver.Core'}")
sub("tools==e['toolchain_providers']and {q['module']for q in tools}=={'Init','Lean.Elab.Tactic.Omega'}","all(q in e['toolchain_providers']for q in tools)and {q['module']for q in tools}=={'Init'}")
sub("scope='Exact488-row compensated244 canonical table, retained-state embedding,482 common actions and literal local rows. No runtime or halting-equivalence theorem.'","scope='Exact488-row Rotation244 canonical table and old-label inverse/start/dispatch/halt facts. No runtime, source-equivalence or nonhalting theorem.'")
sub('exact_project_prerequisite_count=2','exact_project_prerequisite_count=1')
sub('named_axiom_probes=53,callers=6','named_axiom_probes=7,callers=7')
ast.parse(s);assert not(H/'check.py').exists();(H/'check.py').write_text(s)
(H/'guard-from-compensated.diff').write_text(''.join(difflib.unified_diff(T.read_text().splitlines(True),s.splitlines(True),fromfile=str(T),tofile=str(H/'check.py'))))
assert s[s.index('    def save():'):].replace('named_axiom_probes=7,callers=7','named_axiom_probes=53,callers=6')==T.read_text()[T.read_text().index('    def save():'):]
out=dict(status='AUTHOR_STATIC_GUARD_REVIEW_ONLY',source=inv['source'],audit=inv['audit'],guard=desc(H/'check.py'),boundary=desc(H/'boundary.json'),
 parent=desc(P),template=desc(T),emitter=desc(Path(__file__)),probes=7,callers=7,projects=1,tools=['Init'],
 execution_tail_exact_except_census=True,compiler_executed=False,guard_executed=False,findings=[])
(H/'guard-author-review.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
