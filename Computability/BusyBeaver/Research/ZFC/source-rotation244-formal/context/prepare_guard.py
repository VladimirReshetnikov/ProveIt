#!/usr/bin/env python3
"""Own metadata/source writer, no guard/compiler invocation."""
from pathlib import Path
import hashlib,json,re,ast,difflib
B=Path('/tmp/zfc-rmdag-context-substitution');E=Path('/tmp/zfc-routing245-endpoint-actual/run2/verification.json');H='41ff9364f37d9eb33ff1eb2b4bbc0e5f17f0a44ac02a4a7dcdbdfa6c5b1ccf87'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def d(p):return dict(path=str(p),sha256=sha(p))
assert sha(E)==H;e=json.loads(E.read_text());assert e['status']=='PASS' and e['before']==e['after']
q=next(x for x in e['reused_modules'] if x['module']=='BusyBeaver.ZFC.RMDag')
for k in ['source','object']:assert sha(q[k])==q[k+'_sha256']==e['before'][str(Path(q[k]).resolve())]
assert not re.findall(r'^import\s+(\S+)\s*$',Path(q['source']).read_text(),re.M)
a=next(x for x in e['actual_first_providers'] if x['module']==q['module']);assert Path(a['actual_first']).resolve()==Path(q['object']).resolve() and a['sha256']==q['object_sha256']
tools=[x for x in e['toolchain_providers'] if x['module']=='Init'];assert len(tools)==1
for t in tools:assert sha(t['object'])==t['object_sha256']
assert sha(e['compiler']['path'])==e['compiler']['sha256']
boundary=dict(parent=d(E),compiler=e['compiler'],reused_modules=[q],toolchain_providers=tools,scope='Exact import-free RMDag plus Init selected from actual BinaryRouting245. Historical recorded source/object and first-provider binding reused; no new RMDag compilation or broad851-provider validation.',static_inputs=[d(B/'source-inventory.json'),d(Path(__file__))])
assert not (B/'check.py').exists() and not (B/'boundary.json').exists();(B/'boundary.json').write_text(json.dumps(boundary,indent=2)+'\n')
T=Path('/tmp/zfc243-combined-lean/table-rotation/check-v2.py');raw=T.read_text();s=raw.replace('/tmp/zfc243-combined-lean/table-rotation',str(B)).replace('TableRotation244','RMDagContextSubstitution').replace('BusyBeaver.Core','BusyBeaver.ZFC.RMDag')
s=s.replace('Exact Rotation244 table; only Core+Init, no builds.','Generic RMDag context substitution; exact RMDag+Init provider, no builds.')
s=s.replace("PREFIX='SetTheory.BusyBeaver.ZFC.'","PREFIX='SetTheory.BusyBeaver.ZFC.RMDagContextSubstitution.'")
for k,v in [('PROBES',['Replacement.symm','forward','run_iff','iter_forward','iterHalts_iff']),('SOURCE_SHA',sha(B/'RMDagContextSubstitution.lean')),('AUDIT_SHA',sha(B/'Audit.lean')),('BOUNDARY_SHA',sha(B/'boundary.json'))]:
 s,n=re.subn(r'^'+k+r'=.*$',lambda m:k+'='+repr(v),s,count=1,flags=re.M);assert n==1
old="==7,'Typed callers changed.'";assert s.count(old)==1;s=s.replace(old,"==6,'Typed callers changed.'")
s=s.replace('named_axiom_probes=7,callers=7','named_axiom_probes=5,callers=6')
s=s.replace('Exact488-row Rotation244 canonical table and old-label inverse/start/dispatch/halt facts. No runtime, source-equivalence or nonhalting theorem.','Generic safe-context Run and root IterHalts transfer under explicit equivalent-macro, safe-child and unchanged-row hypotheses. No concrete WF, path, binary or PA calibration.')
ast.parse(s);(B/'check.py').write_text(s)
(B/'guard-from-rotation-table.diff').write_text(''.join(difflib.unified_diff(raw.splitlines(True),s.splitlines(True),fromfile=str(T),tofile=str(B/'check.py'))))
(B/'guard-proposal.json').write_text(json.dumps(dict(status='STRICT_GUARD_SOURCE_ONLY_NOT_EXECUTED',guard=d(B/'check.py'),boundary=d(B/'boundary.json'),source=d(B/'RMDagContextSubstitution.lean'),audit=d(B/'Audit.lean'),parent=d(E),template=d(T),projects=1,tools=['Init'],probes=5,callers=6,source_proof_limits='defaults',shared_timeout_seconds=120,compiler_flags=['-j1','-M4096'],dependency_build=False,compiler_version_query=False,prepare_command=['python3','-B',str(B/'check.py'),'--prepare-only','--output',str(B/'prepared1')],actual_command=['python3','-B',str(B/'check.py'),'--output',str(B/'run1')],writer=d(__file__)),indent=2)+'\n')
print(json.dumps({k:d(B/k) for k in ['check.py','boundary.json','guard-proposal.json']},indent=2))
