"""Seal only this new audit; recheck the full input object set read-only."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import stat
import zipfile

ROOT = Path(__file__).resolve().parent
BASE = Path('/workspace/shared')
assert ROOT == BASE/'independent-arity-asymptotics-audit-20261004'
NAMES = ('arity-table-asymptotics-20261004',
         'two-witness-tensor-compiler-20261004',
         'independent-low-arity-audit-20261004')
INPUTS = [BASE/n for n in NAMES]+[BASE/(n+'.zip') for n in NAMES]
INPUTS += [BASE/'arity-table-asymptotics-20261004-receipt.json']

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def inventory():
    out = {}
    for root in INPUTS:
        for path in [root]+(sorted(root.rglob('*')) if root.is_dir() else []):
            s = path.lstat()
            item = dict(kind=stat.S_IFMT(s.st_mode),mode=stat.S_IMODE(s.st_mode),
                        size=s.st_size,mtime_ns=s.st_mtime_ns)
            if stat.S_ISLNK(s.st_mode):
                item['target']=str(path.readlink())
            elif stat.S_ISREG(s.st_mode):
                item['sha256']=sha(path)
            else:
                assert stat.S_ISDIR(s.st_mode)
            out[str(path)]=item
    return out

def main():
    before=json.loads((ROOT/'evidence/input-before.json').read_text())
    after=json.loads((ROOT/'evidence/input-after.json').read_text())
    assert before == after == inventory()
    files=sorted(p for p in ROOT.rglob('*') if p.is_file())
    assert all(not p.is_symlink() for p in ROOT.rglob('*'))
    manifest=ROOT/'MANIFEST.sha256'
    assert manifest not in files
    with manifest.open('x') as f:
        for path in files:
            f.write(sha(path)+'  '+str(path.relative_to(ROOT))+'\n')
    files.append(manifest)
    for path in files:
        assert path.is_relative_to(ROOT)
        path.chmod(0o444)
    for path in sorted((p for p in ROOT.rglob('*') if p.is_dir()),reverse=True):
        path.chmod(0o555)
    ROOT.chmod(0o555)
    archive=ROOT.with_suffix('.zip')
    with zipfile.ZipFile(archive,'x',compression=zipfile.ZIP_DEFLATED) as z:
        for path in sorted(files):
            z.write(path,str(Path(ROOT.name)/path.relative_to(ROOT)))
    archive.chmod(0o444)
    with zipfile.ZipFile(archive) as z:
        expected={str(Path(ROOT.name)/p.relative_to(ROOT)) for p in files}
        assert len(z.namelist()) == len(expected)
        assert set(z.namelist()) == expected
        for path in files:
            member=str(Path(ROOT.name)/path.relative_to(ROOT))
            assert z.read(member) == path.read_bytes()
            assert ((z.getinfo(member).external_attr>>16)&0o777) == 0o444
    assert inventory() == before
    receipt=dict(packet=ROOT.name,sealed_utc=datetime.now(timezone.utc).isoformat(),
                 payload_count=len(files)-1,manifest_sha256=sha(manifest),
                 audit_sha256=sha(ROOT/'AUDIT.md'),archive_sha256=sha(archive),
                 input_objects_preserved=len(before),
                 input_bytes_modes_mtimes_object_sets_unchanged=True,
                 archive_member_bytes_and_modes_equal=True,
                 original_history_retained=True,
                 no_whole_interval_report69_report70_preservation_claim=True,
                 proof_verdict='PASS with the stated scope and preservation qualifications')
    receipt_path=ROOT.parent/(ROOT.name+'-receipt.json')
    with receipt_path.open('x') as f:
        json.dump(receipt,f,indent=2,sort_keys=True)
        f.write('\n')
    receipt_path.chmod(0o444)
    print(json.dumps(receipt,indent=2,sort_keys=True))

if __name__ == '__main__':
    main()
