#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re
B=Path('/tmp/zfc244-compensated-lean/blocks');O=Path(__file__).parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
d=lambda p:dict(path=str(p),sha256=sha(p))
s=(B/'Compensated244Blocks.lean').read_text();old=(B/'history/unexecuted-seven-pair-draft/Compensated244Blocks.lean').read_text()
# Independently constrain the pre-wrapper successor to the exact two reviewed style changes.
cut=s.index('theorem enter122_from104_read0_new_endpoint')
base=s[:cut]+'end SetTheory.BusyBeaver.ZFC.Compensated244Blocks\n'
expected=old.replace(', (show h + 1 = (h + 1) by omega)','').replace(', (show h - 1 = (h - 1) by omega)','')
expected=expected.replace('private theorem enter92_from81_one_new (h : Int) (t : Tape)\n    (hm2 :','private theorem enter92_from81_one_new (h : Int) (t : Tape)\n    (_hm2 :')
assert base==expected
names=re.findall(r'^theorem (\S+)',s,re.M);assert len(names)==14
for n in names[7:]:
 stem=n.removesuffix('_endpoint')
 block=s[s.index('theorem '+n):]
 block=block.split('\ntheorem ',1)[0].split('\nend ',1)[0]
 assert re.search(r'\n  '+stem+r' h t ',block)
assert not re.search(r'\b(sorry|admit|native_decide)\b|set_option',s)
a=(B/'Audit.lean').read_text();assert len(re.findall(r'^example\b',a,re.M))==14
assert [n.rsplit('.',1)[-1] for n in re.findall(r'^#print axioms (\S+)',a,re.M)]==names
r=dict(status='SOURCE_AND_GUARD_REVIEW_PASS',findings=[],reviewer_role='Independent source/API and guard reviewer; not proof/guard author.',reviewer_source=d(__file__),source=d(B/'Compensated244Blocks.lean'),audit=d(B/'Audit.lean'),guard=d(B/'check.py'),boundary=d(B/'boundary.json'),history_source=d(B/'history/unexecuted-seven-pair-draft/Compensated244Blocks.lean'),delta=d(B/'endpoint-wrapper.diff'),guard_delta=d(B/'guard-from-positive.diff'),counts=dict(paired_equalities=7,new_endpoint_wrappers=7,probes=14,callers=14,project_providers=3,toolchain_providers=2),review=['Full original seven-pair source and emitter read; exact tape writes and positive old/new durations match literal rows.','Complete successor diff and typed audit read. The original public seven equalities are unchanged; private proof simplification removes reflexive head rewrites and renames one unused hypothesis.','All seven endpoint wrappers directly reuse the private new-run calculations with identical premises and exact whole configurations.','Guard delta reuses the previously read bounded runner, selects exact actual table parent and its fresh pre-audit/first-provider object; 120 seconds shared, -j1, -M4096, default proof limits.'],scope='Arbitrary Core finite-support tape and head with explicit finite bit premises. Seven local pairs/endpoints only; no global halting-equivalence claim.',supplied_execution=False)
p=O/'blocks-source-review.json';p.write_text(json.dumps(r,indent=2)+'\n');print(d(p))
