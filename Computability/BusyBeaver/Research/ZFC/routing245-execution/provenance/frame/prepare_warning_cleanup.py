#!/usr/bin/env python3
"""Preserve Frame run1 and remove exactly its one reported unused simp argument."""
from pathlib import Path
import hashlib,json,shutil,difflib,ast
B=Path('/tmp/zfc-routing245-lean/frame');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();S=B/'Routing245Simulation.lean';A=B/'Audit.lean';G=B/'check.py';P=B/'run1/verification.json'
assert sha(S)=='dea64229b0eb2b5438eb2b513a63bb92596b241107e8e40566709e1400b965a4';assert sha(A)=='96f700e3d6c57f374a886a0017e14c524c31570c14f12d0d59ee579fa463a113';assert sha(G)=='8274dd41aebe3d1372af8dc8cea1b76f2179154769748d8524510b6251afd034';assert sha(P)=='66e5ca46a2389056302ed85a09f7fd4b2b2518fb61a214b1484d9665ad00e964'
d=json.loads(P.read_text());assert d['status']=='PASS' and d['warnings']=={'source':1,'audit':0};assert(d['named_axiom_probes'],d['callers'])==(14,15)
H=B/'history/attempt1-before-warning-cleanup';assert not H.exists()
inputs=[p for p in B.iterdir()if p.is_file()and p.name!='prepare_warning_cleanup.py']+[p for p in (B/'run1').rglob('*')if p.is_file()and 'cache'not in p.relative_to(B/'run1').parts]
kept=[]
for p in inputs:
 q=H/p.relative_to(B);q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q);assert sha(q)==sha(p);kept.append({'original':str(p),'archived':str(q),'sha256':sha(q)})
s=S.read_text();old='simp only [Nat.pred_eq_sub_one, List.append_assoc, registerBits_eq]';new='simp only [Nat.pred_eq_sub_one, registerBits_eq]';assert s.count(old)==1;t=s.replace(old,new)
D=B/'source-v2';D.mkdir();S2=D/S.name;S2.write_text(t);assert t.replace(new,old)==s
u=G.read_text();v=u.replace("SOURCE_SHA='"+sha(S)+"'","SOURCE_SHA='"+sha(S2)+"'");assert v!=u;assert v.count("HERE/'Routing245Simulation.lean'")==1;v=v.replace("HERE/'Routing245Simulation.lean'","HERE/'source-v2/Routing245Simulation.lean'");ast.parse(v);G2=B/'check-v2.py';assert not G2.exists();G2.write_text(v)
assert v.replace("SOURCE_SHA='"+sha(S2)+"'","SOURCE_SHA='"+sha(S)+"'").replace("HERE/'source-v2/Routing245Simulation.lean'","HERE/'Routing245Simulation.lean'")==u
(B/'source-warning-cleanup.diff').write_text(''.join(difflib.unified_diff(s.splitlines(True),t.splitlines(True),fromfile=str(S),tofile=str(S2))))
(B/'guard-warning-cleanup.diff').write_text(''.join(difflib.unified_diff(u.splitlines(True),v.splitlines(True),fromfile=str(G),tofile=str(G2))))
r={'status':'SOURCE_ONLY_SUCCESSOR_NOT_EXECUTED','prior_record':{'path':str(P),'sha256':sha(P),'status':'PASS','warnings':d['warnings']},'old_source':{'path':str(S),'sha256':sha(S)},'new_source':{'path':str(S2),'sha256':sha(S2)},'audit_unchanged':{'path':str(A),'sha256':sha(A)},'old_guard':{'path':str(G),'sha256':sha(G)},'new_guard':{'path':str(G2),'sha256':sha(G2)},'exact_edit':'Remove only List.append_assoc from decrement_rebase final simp list (source line184).','theorem_statements_unchanged':True,'guard_change':'Only source SHA and default source path.','archived':kept,'compiled_object':'Original run1 object remains at recorded path; not copied.','proof_execution':False};(B/'source-warning-cleanup.json').write_text(json.dumps(r,indent=2)+'\n');print('source',sha(S2));print('guard',sha(G2));print('archived',len(kept))
