#!/usr/bin/env python3
"""Own metadata/text adaptation only; does not execute guard or Lean."""
from pathlib import Path
import ast,difflib,hashlib,json,re
B=Path('/tmp/zfc243-calibration-plan')
OLD=Path('/tmp/zfc243-combined-lean/invariant/check.py')
P=Path('/tmp/zfc-routing245-lean/program/run3/verification.json')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
desc=lambda p:dict(path=str(p),sha256=sha(p))
assert sha(OLD)=='754da77c20e690d71cf7f5814739a5a0bdda8aba76e070d82a83bc746c357c94'
assert sha(P)=='1efd9f64fc8067e85518fc9968752a9a10f78cdeb4f24aa8dd9e8c58d2a53c71'
e=json.loads(P.read_text());assert e['status']=='PASS' and e['before']==e['after']
S=B/'ProgramRotation244.lean';A=B/'Audit.lean';f,=e['fresh_modules']
for p,h in e['before'].items():assert sha(p)==h
assert sha(f['path'])==f['sha256']
pairs=e['reused_modules']+[dict(module=f['module'],source=e['source']['path'],source_sha256=f['source_sha256'],object=f['path'],object_sha256=f['sha256'])]
modules={q['module'] for q in pairs}
assert modules=={'BusyBeaver.ZFC.ProgramRouting245','BusyBeaver.ZFC.RMBisim','BusyBeaver.ZFC.RMEquiv','BusyBeaver.ZFC.RMDag','BusyBeaver.ZFC.RegisterPath'}
for q in pairs:
 for k in ('source','object'):assert sha(q[k])==q[k+'_sha256']
probes=[n.rsplit('.',1)[1]for n in re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)]
assert len(probes)==7 and len(re.findall(r'^example\b',A.read_text(),re.M))==7
oldnames=re.findall(r'^#print axioms (\S+)$',Path(e['audit']['snapshot']).read_text(),re.M)
assert oldnames==['ProgramRouting245.program_root','ProgramRouting245.program_nnodes','ProgramRouting245.nodes_default','TreeRouting245.tree_eq_fuel','TreeRouting245.tree_eq','TreeRouting245.walk_eq_tree','TreeRouting245.step_eq_tree','TreeRouting245.leaf_count','TreeRouting245.node_count','TreeRouting245.depth_eq','TreeRouting245.halt_count']
boundary=dict(parent=desc(P),compiler=e['compiler'],reused_modules=pairs,toolchain_providers=e['toolchain_providers'],scope='Exact actual ProgramRouting245 run3 fresh source/object and its four project providers; only Init tool boundary. Historical audit uses explicit short names under SetTheory.BusyBeaver.ZFC; reports are fully qualified. Fresh first-provider capture has actual_first/resolved fields.',static_inputs=[desc(p)for p in [Path(__file__),B/'validate_dag_v2.py',B/'static-dag-review.json',B/'parser-v2-correction.json',B/'wf-candidate-tables.json']])
bp=B/'boundary.json';assert not bp.exists();bp.write_text(json.dumps(boundary,indent=2)+'\n')
old=OLD.read_text();g=old
changes=[
 ('Rotation244 local tape invariant; exact Core+Rotation244 and Init providers.','Two-row rotated logical program interface; five exact project providers and Init.'),
 ("HERE=Path('/tmp/zfc243-combined-lean/invariant')",f'HERE=Path({str(B)!r})'),
 ("MODULE='BusyBeaver.ZFC.Rotation244Invariant'","MODULE='BusyBeaver.ZFC.ProgramRotation244'"),
 ("PREFIX='SetTheory.BusyBeaver.ZFC.Rotation244Invariant.'","PREFIX='SetTheory.BusyBeaver.ZFC.ProgramRotation244.'"),
 ("PROBES=['start_holds', 'initial_holds', 'step_holds', 'runFrom_holds', 'run_holds']",'PROBES='+repr(probes)),
 ("SOURCE_SHA='c697cfad7c70aecc3422f482161f7ffb43f6f0c39ee0c78cb6e56fdc70abb2da'",'SOURCE_SHA='+repr(sha(S))),
 ("AUDIT_SHA='585b3b9dfd0af05323f4fa062bdb383fe0fed7aec6f8a8c0fa5d0ca22328882f'",'AUDIT_SHA='+repr(sha(A))),
 ("BOUNDARY_SHA='ec223b4d5fd91a509e766d1e7d7df91af310affdf69a8d52f09cc79f658ffd92'",'BOUNDARY_SHA='+repr(sha(bp))),
 ("PARENT_SHA='339ac1eb684bf2b0e2dca81f6a5d693abf2f3fe7079d0c924e5cf2ab870f3466'",'PARENT_SHA='+repr(sha(P))+'\nPARENT_AUDIT_NAMES='+repr(oldnames)),
 ("default=HERE/'Rotation244Invariant.lean'","default=HERE/'ProgramRotation244.lean'"),
 ("(e['named_axiom_probes'],e['callers'])==(7,7)","(e['named_axiom_probes'],e['callers'])==(11,13)"),
 ("require(len(ns)==7 and [q['name']for q in rr]==ns and all(set(q['axioms'])<=STANDARD for q in rr),'Parent raw reports.')", "require(ns==PARENT_AUDIT_NAMES and 'open SetTheory.BusyBeaver.ZFC' in Path(e['audit']['snapshot']).read_text() and [q['name']for q in rr]==['SetTheory.BusyBeaver.ZFC.'+n for n in ns] and all(set(q['axioms'])<=STANDARD for q in rr),'Parent raw reports.')\n    require(len(re.findall(r'^example\\b',Path(e['audit']['snapshot']).read_text(),re.M))==13,'Parent caller census.')\n    for c in e['commands']:\n        pin(c['log'],hashlib.sha256(c['output'].encode()).hexdigest())"),
 ("imports(S)==['BusyBeaver.ZFC.TableRotation244']","imports(S)==['BusyBeaver.ZFC.ProgramRouting245']"),
 ("len(re.findall(r'^example\\b',A.read_text(),re.M))==8","len(re.findall(r'^example\\b',A.read_text(),re.M))==7"),
 ("len(reused)==2 and set(projects)=={'BusyBeaver.Core','BusyBeaver.ZFC.TableRotation244'}","len(reused)==5 and set(projects)=="+repr(set(sorted(modules)))),
 ("q['module'] == 'BusyBeaver.ZFC.TableRotation244'","q['module'] == 'BusyBeaver.ZFC.ProgramRouting245'"),
 ("Path(cap['path']).resolve()==Path(q['object']).resolve()", "Path(cap['actual_first']).resolve()==Path(cap['resolved']).resolve()==Path(q['object']).resolve()"),
 ("scope='Local invariant at old68/81/167 on arbitrary Core finite-support tapes, preserved for every natural run duration. No calibration or machine comparison.'", "scope='Exact two-row logical program override and local row equalities. No full-tree certificate, source halting transfer, binary simulation, or consistency calibration.'"),
 ("exact_project_prerequisite_count=2", "exact_project_prerequisite_count=5"),
 ("named_axiom_probes=5,callers=8", "named_axiom_probes=7,callers=7")]
for a,z in changes:
 assert g.count(a)==1,(a,g.count(a));g=g.replace(a,z)
ast.parse(g)
out=B/'check.py';assert not out.exists();out.write_text(g)
(B/'guard-from-invariant.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),g.splitlines(True),fromfile=str(OLD),tofile=str(out))))
(B/'guard-proposal.json').write_text(json.dumps(dict(status='SOURCE_ONLY_UNEXECUTED',source=desc(S),audit=desc(A),guard=desc(out),boundary=desc(bp),parent=desc(P),template=desc(OLD),probes=7,callers=7,project_count=5,tools=['Init'],shared_seconds=120,limits='-j1 -M4096; default proof limits',schema_adaptations=['Exact historical11 short audit names under explicit namespace open map to corresponding full reports.','Historical fresh first provider has actual_first/resolved; both are required to identify the exact fresh object.','Historical command logs lack independent log_sha256; pin exact raw bytes to SHA256 of the recorded output.'],execution_tail_unchanged_except_census=True,supplied_execution=False),indent=2)+'\n')
print(json.dumps(dict(guard=desc(out),boundary=desc(bp)),indent=2))
