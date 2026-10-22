"""Adopt exactly the reviewed nine-document successor and its metadata."""
from pathlib import Path
import hashlib,json
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');O=Path('/tmp/k215-phase15-root')
S=Path('/tmp/k215-phase15-docs')
P=R/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase15'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
assert sha(S/'copy-map.json')=='4884840cb12c95ef1724441f87b0fc8a91715878b8c88d15843c8111d8a13c57'
assert sha(S/'freeze.json')=='9b1bb1c6ff79afa56a933da2aa178465f06d75b5dfa17e4aaaadc2537e6b4a4c'
rows=read(S/'copy-map.json')['files'];assert len(rows)==9
assert read(O/'publication-copy-review.json')['owner_and_independent_receipts_identical']
for row in rows:
    assert sha(row['source'])==row['sha256']
    out=R/row['target']
    if row['before_sha256'] is None:assert not out.exists() and not out.is_symlink()
    else:assert sha(out)==row['before_sha256']
for row in rows:
    out=R/row['target'];out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(Path(row['source']).read_bytes());assert sha(out)==row['sha256']
for source,target in [(S/'copy-map.json','documentation-map.json'),(S/'finalization.json','documentation-finalization.json'),
                      (O/'publication-copy-review.json','publication-copy-review.json'),(O/'copy_publication.py','copy_publication.py'),
                      (O/'copy_documents.py','copy_documents.py')]:
    out=P/'integration'/target;assert not out.exists();out.write_bytes(source.read_bytes())
print('Copied9 exact documents and5 explicit metadata files')
