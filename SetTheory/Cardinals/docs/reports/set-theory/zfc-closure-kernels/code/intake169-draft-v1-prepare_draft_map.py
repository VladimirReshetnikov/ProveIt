#!/usr/bin/env python3
"""Own metadata-only draft inventory; copies no maintained files, invokes no supplied code."""
from pathlib import Path
import hashlib, json, re

HERE = Path('/tmp/zfc-intake169-drafts-v1')
REPO = Path('/home/codex/.codex/worktrees/ec20/Proofs')
HOST = Path('SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels')
entries = []
def add(source, destination, role):
    p = Path(source)
    assert p.is_file(), p
    assert destination not in {r['target_relative_to_host'] for r in entries}, destination
    entries.append(dict(source=str(p), target=str(HOST/destination),
        target_relative_to_host=destination, sha256=hashlib.sha256(p.read_bytes()).hexdigest(),
        bytes=p.stat().st_size, role=role))

for p in sorted(HERE.glob('intake-169*.md')):
    add(p,p.name,'New reconciliation prose, source dossiers or reproduction; placement placeholders intentional.')

explicit = {
 '/tmp/zfc-compare-d584512002/table-comparison-root.json':'data/intake169-table-comparison-root.json',
 '/tmp/zfc-d584-reflection-review/review.json':'data/intake169-return-branch-review.json',
 '/tmp/zfc-d584-reflection-review/review.md':'data/intake169-return-branch-review.md',
 '/tmp/zfc-compare-d584512002/drop-review/review.json':'data/intake169-context-review.json',
 '/tmp/zfc-compare-d584512002/drop-review/review.md':'data/intake169-context-review.md',
 '/tmp/zfc-compare-d584512002/drop-review/table-comparison.json':'data/intake169-context-table-comparison.json',
 '/tmp/zfc-d584-opening-review/review.json':'data/intake169-detour-zero-review.json',
 '/tmp/zfc-d584-opening-review/review.md':'data/intake169-detour-zero-review.md',
 '/tmp/zfc-d584-opening-review/secondary-search-supplement.md':'data/intake169-secondary-search-supplement.md',
 '/tmp/zfc-d584-opening-review/secondary-search-supplement.json':'data/intake169-secondary-search-supplement.json',
 '/tmp/zfc-joint-equational-packet/build_joint.py':'code/intake169-build-joint.py',
 '/tmp/zfc-joint-equational-packet/proof.md':'data/intake169-joint-proof-proposal.md',
 '/tmp/zfc-joint-equational-packet/source-proposal.json':'data/intake169-joint-source-proposal.json',
 '/tmp/zfc-joint-equational-proof-review/horn_certificates.py':'code/intake169-horn-certificates.py',
 '/tmp/zfc-joint-equational-proof-review/joint-builder-source-review.json':'data/intake169-joint-builder-source-review.json',
 '/tmp/zfc-joint-equational-proof-review/joint-actual-review.json':'data/intake169-joint-actual-review.json',
 '/tmp/zfc-joint-equational-packet-root1/output/verification.json':'data/intake169-joint-verification.json',
 '/tmp/zfc-joint-equational-packet-root1/execution.json':'data/intake169-joint-execution.json',
 '/tmp/zfc-joint-equational-packet-root1/stdout.log':'data/intake169-joint-stdout.log',
 '/tmp/zfc-joint-equational-packet-root1/stderr.log':'data/intake169-joint-stderr.log',
}
for src,dst in explicit.items():
    add(src,dst,'Exact existing source/review/root evidence; no rerun and no historical wording change.')

roots = [
 ('/tmp/zfc-d584-reflection-review','return-branch'),
 ('/tmp/zfc-compare-d584512002/drop-review','context'),
 ('/tmp/zfc-d584-opening-review','detour-zero'),
 ('/tmp/zfc-joint-equational-proof-review','joint-review'),
 ('/tmp/zfc-joint-equational-packet/history','joint-builder-history'),
]
for root,prefix in roots:
    root=Path(root)
    for p in sorted(root.rglob('*')):
        if not p.is_file() or '__pycache__' in p.parts or str(p) in explicit:
            continue
        p.read_text()  # Restrict this evidence selection to losslessly retained text.
        leaf='intake169-'+prefix+'-'+str(p.relative_to(root)).replace('/','-')
        add(p,('code/' if p.suffix=='.py' else 'data/')+leaf,'Exact peer script/receipt/history, including reviewer-only corrections; not executed by this writer.')

run=Path('/tmp/zfc-joint-equational-packet-root1')
for p in sorted((run/'output').iterdir()):
    if p.name=='verification.json': continue
    add(p,'data/intake169-joint-'+p.name,'Exact fresh root output; complete encoding and equation payload.')
for p in sorted((run/'reference').iterdir()):
    if not p.is_file(): continue
    add(p,('code/' if p.suffix=='.py' else 'data/')+'intake169-joint-reference-'+p.name,'Exact copied executed dependency; original name restored for replay.')

proposal=Path('/tmp/zfc-intake169-placement-plan/placement-proposal.json')
placement=json.loads(proposal.read_text())
assert placement['counts']['members']==1387
assert placement['counts']['new_files']==440
planned={e['target_relative_to_host'] for e in entries}
root_provided={'data/intake169-placement.json','data/intake169-history-review.json',
 'data/intake169-original-placement-bindings.json','data/intake169-exhaustive-history.json.gz',
 'data/intake169-map-history.json.gz'}
links=[]
for p in sorted(HERE.glob('intake-169*.md')):
    for target in re.findall(r'\]\(([^)]+)\)',p.read_text()):
        target=target.split('#')[0]
        if not target or '://' in target:continue
        assert target in planned or target in root_provided or (REPO/HOST/target).exists(),(p,target)
        links.append(dict(file=p.name,target=target))
for e in entries:
    assert len('C:\\ProveIt\\'+e['target'].replace('/','\\'))<240,e['target']
manifest=dict(status='FROZEN_DRAFT_MAP_PENDING_ACTUAL_PLACEMENT_AND_ROOT_WRITE',batch=169,
    source_numbers=list(range(74,80)),entries=entries,count=len(entries),
    placement_proposal=dict(path=str(proposal),sha256=hashlib.sha256(proposal.read_bytes()).hexdigest()),
    placement_commit=None,recovery_record=None,root_provided_metadata=sorted(root_provided),
    separate_root_owned_snippets=['host-readme-addition.md','catalogue-snippets.md'],
    local_link_checks=links,supplied_execution=False,maintained_mutation=False,
    caveat='This is a reviewable draft copy map, not an executed installer or claim of six-suite replay.')
(HERE/'draft-map.json').write_text(json.dumps(manifest,indent=2)+'\n')
sources=[p for p in sorted(HERE.iterdir()) if p.is_file() and p.name not in ['freeze.json']]
(HERE/'freeze.json').write_text(json.dumps(dict(status='DRAFT_SOURCE_FREEZE',files=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in sources]),indent=2)+'\n')
print(json.dumps(dict(entries=len(entries),links=len(links),map_sha256=hashlib.sha256((HERE/'draft-map.json').read_bytes()).hexdigest(),freeze_sha256=hashlib.sha256((HERE/'freeze.json').read_bytes()).hexdigest())))
