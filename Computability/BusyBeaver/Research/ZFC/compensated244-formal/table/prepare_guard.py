from pathlib import Path
import hashlib,json,re,ast,difflib
H=Path(__file__).parent;R=Path('/home/codex/.codex/worktrees/ec20/Proofs');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();E=R/'Computability/BusyBeaver/Research/ZFC/results/routing245-binary-verification.json';e=json.loads(E.read_text())
mods=['BusyBeaver.Core','BusyBeaver.ZFC.TableRouting245'];rows=[next(q for q in e['reused_modules']if q['module']==m)for m in mods]
b=dict(parent=dict(path=str(E),sha256=sha(E)),compiler=e['compiler'],reused_modules=rows,toolchain_providers=e['toolchain_providers'],scope='Only Core and checked exact TableRouting245 selected from Binary245; no other851-provider ancestor replay.',static_inputs=[dict(path=str(p),sha256=sha(p))for p in [H/'source-inventory.json',H/'prepare_source.py']]+json.loads((H/'source-inventory.json').read_text())['inputs'])
(H/'boundary.json').write_text(json.dumps(b,indent=2)+'\n')
s=Path('/tmp/zfc244-positive-blocks/check.py').read_text();s=s.replace('Positive-block halting equivalence; exactly Core+RuntimePerm252, no builds.','Exact compensated244 table+embedding; Core+TableRouting245 only, no builds.')
s=s.replace('/tmp/zfc244-positive-blocks','/tmp/zfc244-compensated-lean/table').replace('BusyBeaver.ZFC.PositiveBlockBisimulation','BusyBeaver.ZFC.TableCompensated244').replace("PREFIX='SetTheory.BusyBeaver.ZFC.PositiveBlockBisimulation.'","PREFIX='SetTheory.BusyBeaver.ZFC.'")
s=s.replace("HERE/'PositiveBlockBisimulation.lean'","HERE/'TableCompensated244.lean'")
# Prefix replacement above is deliberately exact; ensure final public namespace.
s=s.replace("PREFIX='SetTheory.BusyBeaver.ZFC.TableCompensated244.'","PREFIX='SetTheory.BusyBeaver.ZFC.'")
probes=[n.removeprefix('SetTheory.BusyBeaver.ZFC.')for n in re.findall(r'^#print axioms (\S+)$',(H/'Audit.lean').read_text(),re.M)];assert len(probes)==53
s=re.sub(r'^PROBES=.*$','PROBES='+repr(probes),s,flags=re.M)
for key,p in [('SOURCE_SHA',H/'TableCompensated244.lean'),('AUDIT_SHA',H/'Audit.lean'),('BOUNDARY_SHA',H/'boundary.json')]:s=re.sub(r'^'+key+r'=.*$',key+'='+repr(sha(p)),s,flags=re.M)
s=s.replace("b=json.loads(B.read_text());E=pin", "b=json.loads(B.read_text())\n    for q in b['static_inputs']:pin(q['path'],q['sha256'])\n    E=pin")
s=s.replace("imports(S)==['BusyBeaver.ZFC.RuntimePerm252']","imports(S)==['BusyBeaver.ZFC.TableRouting245','Lean.Elab.Tactic.Omega']")
s=s.replace("==PROBES,'Audit short names changed.'","==[PREFIX+n for n in PROBES],'Audit names changed.'")
s=s.replace("==4,'Typed callers changed.'","==6,'Typed callers changed.'").replace("{'BusyBeaver.Core','BusyBeaver.ZFC.RuntimePerm252'}","{'BusyBeaver.Core','BusyBeaver.ZFC.TableRouting245'}")
s=s.replace("scope='Generic positive-block halting equivalence for Core finite-support tapes. No concrete244 simulation claimed.'","scope='Exact488-row compensated244 canonical table, retained-state embedding,482 common actions and literal local rows. No runtime or halting-equivalence theorem.'")
s=s.replace('named_axiom_probes=4,callers=4','named_axiom_probes=53,callers=6')
ast.parse(s);(H/'check.py').write_text(s)
(H/'guard-from-positive.diff').write_text(''.join(difflib.unified_diff(Path('/tmp/zfc244-positive-blocks/check.py').read_text().splitlines(True),s.splitlines(True),fromfile='PositiveBlock/check.py',tofile='Table244/check.py')))
for q in rows:
 for k in ['source','object']:
  pp=Path(q[k]).resolve();assert sha(pp)==e['before'][str(pp)]==e['after'][str(pp)]==q[k+'_sha256']
 old=next(r for r in e['actual_first_providers']if r['module']==q['module']);assert Path(old['actual_first']).resolve()==Path(q['object']).resolve() and old['sha256']==q['object_sha256']
o=dict(status='AUTHOR_SOURCE_ONLY_GUARD_REVIEW_PASS',guard=dict(path=str(H/'check.py'),sha256=sha(H/'check.py')),boundary=dict(path=str(H/'boundary.json'),sha256=sha(H/'boundary.json')),source=dict(path=str(H/'TableCompensated244.lean'),sha256=sha(H/'TableCompensated244.lean')),audit=dict(path=str(H/'Audit.lean'),sha256=sha(H/'Audit.lean')),probes=53,callers=6,projects=2,tools=2,findings=[],execution='Own pure guard writer/static checks only. No supplied guard/compiler/preparation.')
(H/'guard-author-review.json').write_text(json.dumps(o,indent=2)+'\n');print(json.dumps(o))
