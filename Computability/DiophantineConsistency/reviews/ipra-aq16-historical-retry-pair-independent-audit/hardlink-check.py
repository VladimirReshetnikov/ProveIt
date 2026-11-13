#!/usr/bin/env python3
"""Check all project-output inode sets, including cross-name parent links."""
import hashlib,json,os,tempfile
from pathlib import Path
if not __debug__:raise RuntimeError('optimized Python is unsupported')
HERE=Path(__file__).resolve().parent;PARENT=Path('/tmp/ipra-aq29-fresh-project-pair');PREP=Path('/tmp/ipra-aq16-historical-paired-run-02/prepared')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
paths=[Path(__file__)]+[PARENT/x/'state.json' for x in ('author','peer')]+[PREP/x/'rebuild-state.json' for x in ('author','peer')]
before={str(p.resolve()):H(p) for p in paths}
identity=lambda p:(p.stat().st_dev,p.stat().st_ino)
parent_inodes=set()
for label in ('author','peer'):
    state=json.loads((PARENT/label/'state.json').read_text())
    for group in state['outputs'].values():
        for name,entry in group.items():
            if entry is not None:
                p=Path(name);assert p.is_file() and not p.is_symlink();parent_inodes.add(identity(p))
def assert_fresh(inodes,seen):
    for inode in inodes:
        if inode in parent_inodes or inode in seen:raise ValueError('project output inode is shared')
        seen.add(inode)
seen=set();counts={}
for label in ('author','peer'):
    lib=PREP/label/'lib';files=[p for p in lib.rglob('*') if p.is_file() or p.is_symlink()]
    assert all(not p.is_symlink() for p in files);inodes=[identity(p) for p in files]
    assert_fresh(inodes,seen);counts[label]=len(files)
assert counts['author']==counts['peer']==1262
# Synthetic controls verify both ancestor and cross-sibling inode rejection.
with tempfile.TemporaryDirectory(prefix='aq16-retry-inode-control-') as d:
    a=Path(d)/'a';b=Path(d)/'b';a.write_bytes(b'x');os.link(a,b)
    try:assert_fresh([identity(a),identity(b)],set())
    except ValueError:pass
    else:raise AssertionError('duplicate inode accepted')
parent_example=next(iter(parent_inodes))
try:assert_fresh([parent_example],set())
except ValueError:pass
else:raise AssertionError('parent inode accepted')
assert {str(p.resolve()):H(p) for p in paths}==before
result={'status':'PASS_AQ16_RETRY_PARENT_AND_SIBLING_INODE_ISOLATION','inputs_sha256':before,'parent_unique_inodes':len(parent_inodes),'child_files':counts,
        'scope':'Point-in-time inode isolation only; not byte hashing, Lean replay, or transient-load tracing.'}
out=HERE/'hardlink-receipt.json'
if out.exists():raise ValueError('refusing to overwrite receipt')
out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(result['status'],H(out))
