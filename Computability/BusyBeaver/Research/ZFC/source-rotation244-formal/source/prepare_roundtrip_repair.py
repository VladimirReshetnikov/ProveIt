#!/usr/bin/env python3
"""Preserve actual first failure and emit an unexecuted one-proof successor."""
from pathlib import Path
import ast,difflib,hashlib,json,shutil
B=Path('/tmp/zfc243-source-bridge')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
d=lambda p:dict(path=str(p),sha256=sha(p))
S=B/'SourceRotation244.lean';A=B/'Audit.lean';G=B/'check.py';Q=B/'boundary.json'
assert sha(S)=='1841efd5e21b70b4384c61cff06f5efe525388f7d0838c0767cc85d28abaafe7'
assert sha(G)=='bb063edcaf0d4a32d368b2ef6ebc8614e5de156ed4e405927af8742e54c322df'
V=B/'run1/verification.json';v=json.loads(V.read_text())
assert v['status']=='FAIL' and len(v['commands'])==1 and v['commands'][0]['label']=='source' and v['commands'][0]['exit_code']==1
assert v['fresh_modules']==[] and v['before']==v['after']
assert v['commands'][0]['output']==(B/'run1/source.log').read_text()
assert 'Tactic `rewrite` failed' in v['commands'][0]['output'] and 'ofProgram' in v['commands'][0]['output']
H=B/'history/attempt1-before-roundtrip-unfold';assert not H.exists();H.mkdir(parents=True)
names=['SourceRotation244.lean','Audit.lean','check.py','boundary.json','source-inventory.json','prepare_guard.py','guard-proposal.json','guard-from-simulation.diff','review_finite_data.py','author-finite-data-review.json','independent-source-guard-review.json']
for directory in ['prepared1','run1']:
 names += [str(p.relative_to(B)) for p in (B/directory).rglob('*') if p.is_file() and not p.is_symlink() and 'cache' not in p.relative_to(B).parts]
review=json.loads((B/'independent-source-guard-review.json').read_text())
rp=Path(review['reviewer_source']['path'])
if rp.is_relative_to(B):names.append(str(rp.relative_to(B)))
rows=[]
for n in dict.fromkeys(names):
 src=B/n;dst=H/n;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);assert sha(src)==sha(dst)
 rows.append(dict(original=d(src),preserved=d(dst)))
(H/'archive.json').write_text(json.dumps(dict(status='ACTUAL_SOURCE_FAILURE_PRESERVED',actual=d(V),files=rows,compiled_cache_copied=False),indent=2)+'\n')
old=S.read_text();needle='      rw [hn]\n';assert old.count(needle)==1
new=old.replace(needle,'      dsimp only [ofProgram]\n'+needle)
D=B/'source-v2';assert not D.exists();D.mkdir();S2=D/'SourceRotation244.lean';S2.write_text(new)
diff=B/'roundtrip-unfold-repair.diff';diff.write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile=str(S),tofile=str(S2))))
inv=json.loads((B/'source-inventory.json').read_text());inv['source']=d(S2);inv['source_repair']='Only explicit dsimp only [ofProgram] before the existing node-function equality rewrite; no statement, certificate, audit or option change.';inv['original_inventory']=d(B/'source-inventory.json');I=B/'source-v2-inventory.json';I.write_text(json.dumps(inv,indent=2)+'\n')
repair=dict(status='UNEXECUTED_ONE_PROOF_SUCCESSOR',original_source=d(S),source=d(S2),audit=d(A),actual_failure=d(V),raw_failure_log=d(B/'run1/source.log'),archive=d(H/'archive.json'),diff=d(diff),repair_writer=d(Path(__file__)),mathematical_statement_changed=False,finite_certificates_changed=False,limits_changed=False,proof_execution=False,description=inv['source_repair'])
R=B/'roundtrip-unfold-repair.json';R.write_text(json.dumps(repair,indent=2)+'\n')
b=json.loads(Q.read_text());b['static_inputs'] += [d(p)for p in [Path(__file__),I,diff,R]];Q2=B/'boundary-v2.json';Q2.write_text(json.dumps(b,indent=2)+'\n')
oldg=G.read_text();newg=oldg
edits=[('SOURCE_SHA='+repr(sha(S)),'SOURCE_SHA='+repr(sha(S2))),('BOUNDARY_SHA='+repr(sha(Q)),'BOUNDARY_SHA='+repr(sha(Q2))),("default=HERE/'SourceRotation244.lean'","default=HERE/'source-v2/SourceRotation244.lean'"),("default=HERE/'boundary.json'","default=HERE/'boundary-v2.json'")]
for a,z in edits:assert newg.count(a)==1;newg=newg.replace(a,z)
inverse=newg
for a,z in reversed(edits):inverse=inverse.replace(z,a)
assert inverse==oldg;ast.parse(newg);G2=B/'check-v2.py';G2.write_text(newg)
GD=B/'guard-roundtrip-unfold.diff';GD.write_text(''.join(difflib.unified_diff(oldg.splitlines(True),newg.splitlines(True),fromfile=str(G),tofile=str(G2))))
(B/'guard-v2-proposal.json').write_text(json.dumps(dict(status='SOURCE_ONLY_UNEXECUTED',guard=d(G2),boundary=d(Q2),source=d(S2),audit=d(A),original_guard=d(G),original_boundary=d(Q),guard_diff=d(GD),repair=d(R),original_source_review=d(B/'independent-source-guard-review.json'),projects=8,tools=['Init'],probes=9,callers=10,shared_seconds=120,execution_body_unchanged=True),indent=2)+'\n')
print(json.dumps(dict(source=d(S2),guard=d(G2),boundary=d(Q2),repair=d(R)),indent=2))
