"""Read-only byte/mode/mtime inventory. Never imports or runs source code."""
from pathlib import Path
import hashlib
import json
import stat
import sys

ROOT = Path('/workspace/shared')
INPUTS = [
    ROOT / 'two-witness-tensor-compiler-20261004',
    ROOT / 'two-witness-tensor-compiler-20261004.zip',
    ROOT / 'independent-low-arity-audit-20261004',
    ROOT / 'independent-low-arity-audit-20261004.zip',
    ROOT / 'report69-low-arity-compilers-release-20261004',
    ROOT / 'report70-two-scale-radius-release-20261004',
]

def inventory():
    out = {}
    for root in INPUTS:
        paths = [root] + (sorted(root.rglob('*')) if root.is_dir() else [])
        for path in paths:
            s = path.lstat()
            item = {'mode': stat.S_IMODE(s.st_mode), 'mtime_ns': s.st_mtime_ns,
                    'size': s.st_size, 'kind': stat.S_IFMT(s.st_mode)}
            if path.is_symlink():
                item['target'] = str(path.readlink())
            elif path.is_file():
                item['sha256'] = hashlib.sha256(path.read_bytes()).hexdigest()
            out[str(path)] = item
    return out

if __name__ == '__main__':
    output = Path(sys.argv[1])
    assert output.parent.resolve() == Path(__file__).parent.resolve() / 'evidence'
    current = inventory()
    if len(sys.argv) == 3:
        prior = json.loads(Path(sys.argv[2]).read_text())
        assert current == prior, 'An input byte/mode/mtime inventory changed'
    with output.open('x') as stream:
        json.dump(current, stream, indent=2, sort_keys=True)
        stream.write('\n')
    print(f'Preservation inventory: {len(current)} entries; output {output.name}')
