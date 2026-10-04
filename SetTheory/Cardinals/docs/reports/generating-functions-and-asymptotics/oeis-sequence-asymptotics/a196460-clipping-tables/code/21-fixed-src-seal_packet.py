"""Seal only this newly authored packet, while read-only checking core inputs."""
from pathlib import Path
import hashlib
import json
import stat
import zipfile

root = Path(__file__).resolve().parent
assert root == Path('/workspace/shared/arity-table-asymptotics-20261004')
evidence = root / 'evidence'
source_roots = [Path('/workspace/shared') / p for p in [
    'two-witness-tensor-compiler-20261004',
    'two-witness-tensor-compiler-20261004.zip',
    'independent-low-arity-audit-20261004',
    'independent-low-arity-audit-20261004.zip']]

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def inventory():
    out = {}
    for base in source_roots:
        for path in [base] + (sorted(base.rglob('*')) if base.is_dir() else []):
            s = path.lstat()
            item = {'mode': stat.S_IMODE(s.st_mode), 'mtime_ns': s.st_mtime_ns,
                    'size': s.st_size, 'kind': stat.S_IFMT(s.st_mode)}
            if path.is_symlink():
                item['target'] = str(path.readlink())
            elif path.is_file():
                item['sha256'] = sha(path)
            out[str(path)] = item
    return out

current = inventory()
prior = json.loads((evidence / 'input-before.json').read_text())
prior = {p: v for p, v in prior.items() if any(
    p == str(q) or p.startswith(str(q) + '/') for q in source_roots)}
assert current == prior
with (evidence / 'core-final.json').open('x') as stream:
    json.dump(current, stream, indent=2, sort_keys=True)
    stream.write('\n')

payloads = sorted(p for p in root.rglob('*') if p.is_file())
manifest = root / 'MANIFEST.sha256'
assert manifest not in payloads
with manifest.open('x') as stream:
    for path in payloads:
        stream.write(sha(path) + '  ' + str(path.relative_to(root)) + '\n')
payloads.append(manifest)
for path in payloads:
    path.chmod(0o444)
for path in sorted((p for p in root.rglob('*') if p.is_dir()), reverse=True):
    path.chmod(0o555)
root.chmod(0o555)

archive = root.with_suffix('.zip')
with zipfile.ZipFile(archive, 'x', compression=zipfile.ZIP_DEFLATED) as z:
    for path in sorted(payloads):
        z.write(path, str(Path(root.name) / path.relative_to(root)))
archive.chmod(0o444)
with zipfile.ZipFile(archive) as z:
    assert len(z.namelist()) == len(payloads)
    for path in payloads:
        assert z.read(str(Path(root.name) / path.relative_to(root))) == path.read_bytes()
assert inventory() == prior
receipt = {'packet': root.name, 'payload_count': len(payloads)-1,
           'manifest_sha256': sha(manifest), 'archive_sha256': sha(archive),
           'proof_sha256': sha(root / 'PROOF.md'),
           'sources_sha256': sha(root / 'SOURCES.md'),
           'core_source_entries_preserved': len(current),
           'core_source_bytes_modes_mtimes_unchanged': True,
           'concurrent_release_changes_disclosed': True,
           'archive_member_bytes_equal_packet': True}
receipt_path = root.parent / (root.name + '-receipt.json')
with receipt_path.open('x') as stream:
    json.dump(receipt, stream, indent=2, sort_keys=True)
    stream.write('\n')
receipt_path.chmod(0o444)
print(json.dumps(receipt, indent=2, sort_keys=True))
