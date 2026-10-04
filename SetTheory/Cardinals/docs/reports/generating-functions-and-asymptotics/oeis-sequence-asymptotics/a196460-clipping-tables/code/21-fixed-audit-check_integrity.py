"""Fresh read-only authentication and preservation checker for this audit.

Only stdlib, bytes, metadata and ZIP/JSON data are read. No input code runs.
Outputs are exclusive-create files in this new audit directory.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import stat
import sys
import zipfile

BASE = Path('/workspace/shared')
OUT = Path(__file__).resolve().parent
assert OUT == BASE / 'independent-arity-asymptotics-audit-20261004'
NAMES = ['arity-table-asymptotics-20261004',
         'two-witness-tensor-compiler-20261004',
         'independent-low-arity-audit-20261004']
ROOTS = [BASE / n for n in NAMES]
INPUTS = ROOTS + [BASE / (n + '.zip') for n in NAMES]
INPUTS += [BASE / 'arity-table-asymptotics-20261004-receipt.json']
PINS = {
 'arity-table-asymptotics-20261004/MANIFEST.sha256': '6ae30398c52b6fe1d07a91346791ed3355e7104c55b19a4103de257299293de1',
 'arity-table-asymptotics-20261004/PROOF.md': '638e524d058deb926919d15b7df2dafc17f7a44dc2688b33e06ee24f476b7c41',
 'arity-table-asymptotics-20261004.zip': '11d45c3cf884e722b72d1032e8879f75070a69ec844efe89a919858b8200d345',
 'two-witness-tensor-compiler-20261004/MANIFEST.sha256': 'b243e39e0fd9698f9d610f0f6d2b17485a98df8e20a9412c1c38c65877a42c82',
 'two-witness-tensor-compiler-20261004/ONE_WITNESS.md': '9135dd0e829adb3190e99ed1b62f8d419f9f7540cfd92a1acd1635726fa7172c',
 'two-witness-tensor-compiler-20261004.zip': '897a7bee8ab8f0758b8c3b035b7be0d06d9521a9769919266ab30057a6702c8c',
 'independent-low-arity-audit-20261004/MANIFEST.sha256': '6852625bc450563eeda5ad96956e3ac18da64b95ca446c654da14f3b978594b3',
 'independent-low-arity-audit-20261004/AUDIT.md': '6bf14006170df1e126fb98d8e06ee97cfb51786f9ce11bcc0a37370a896d5afe',
 'independent-low-arity-audit-20261004.zip': '3f8811f2217d292ca3d895712e8e7d17465ac51e328ed94eeee80fbc22cfe1a7',
}

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def snapshot():
    items = {}
    for root in INPUTS:
        paths = [root] + (sorted(root.rglob('*')) if root.is_dir() else [])
        for p in paths:
            s = p.lstat()
            entry = dict(kind=stat.S_IFMT(s.st_mode), mode=stat.S_IMODE(s.st_mode),
                         size=s.st_size, mtime_ns=s.st_mtime_ns)
            if stat.S_ISLNK(s.st_mode):
                entry['target'] = str(p.readlink())
            elif stat.S_ISREG(s.st_mode):
                entry['sha256'] = digest(p)
            else:
                assert stat.S_ISDIR(s.st_mode), 'Unexpected filesystem object'
            items[str(p)] = entry
    return items

def authenticate():
    for rel, expected in PINS.items():
        assert digest(BASE / rel) == expected, rel
    records = []
    for root in ROOTS:
        manifest = {}
        for line in (root / 'MANIFEST.sha256').read_text().splitlines():
            sha, rel = line.split('  ', 1)
            assert rel not in manifest
            p = root / rel
            assert p.resolve().is_relative_to(root.resolve())
            assert digest(p) == sha, str(p)
            manifest[rel] = sha
        actual = {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
        expected = set(manifest) | {'MANIFEST.sha256'}
        assert actual == expected, root.name
        with zipfile.ZipFile(root.with_suffix('.zip')) as z:
            entries = {str(Path(root.name) / p) for p in expected}
            assert len(z.namelist()) == len(entries)
            assert set(z.namelist()) == entries
            for rel in expected:
                member = str(Path(root.name) / rel)
                assert z.read(member) == (root / rel).read_bytes(), member
                assert (z.getinfo(member).external_attr >> 16) & 0o777 == stat.S_IMODE((root / rel).stat().st_mode)
        records.append(dict(packet=root.name, manifest_payloads=len(manifest),
                            exact_file_set=True, archive_files=len(expected),
                            archive_bytes_and_modes_equal=True))
    return records

def historical(current):
    source = ROOTS[0] / 'evidence'
    before = json.loads((source / 'input-before.json').read_text())
    after = json.loads((source / 'input-current.json').read_text())
    recorded = json.loads((source / 'input-changes.json').read_text())
    computed = {p: {'before': before.get(p), 'after': after.get(p)}
                for p in sorted(before.keys() | after.keys()) if before.get(p) != after.get(p)}
    assert computed == recorded
    core_final = json.loads((source / 'core-final.json').read_text())
    core_roots = INPUTS[1:3] + INPUTS[4:6]
    is_core = lambda p: any(p == str(q) or p.startswith(str(q) + '/') for q in core_roots)
    core_before = {p: v for p, v in before.items() if is_core(p)}
    core_after = {p: v for p, v in after.items() if is_core(p)}
    core_current = {p: v for p, v in current.items() if is_core(p)}
    assert core_before == core_after == core_final == core_current
    assert len(core_before) == 62
    counts = {}
    for p in computed:
        release = Path(p).relative_to(BASE).parts[0]
        assert release in ('report69-low-arity-compilers-release-20261004',
                           'report70-two-scale-radius-release-20261004')
        counts[release] = counts.get(release, 0) + 1
    return dict(before_entries=len(before), after_entries=len(after),
                exact_recorded_diff_verified=True, differences=len(computed),
                release_difference_counts=counts, core_entries=62,
                core_all_four_snapshots_equal=True,
                whole_release_interval_preservation_claimed=False)

def write_new(path, obj):
    with path.open('x') as f:
        json.dump(obj, f, indent=2, sort_keys=True)
        f.write('\n')

def main():
    phase = sys.argv[1]
    assert phase in ('before', 'after')
    evidence = OUT / 'evidence'
    evidence.mkdir(exist_ok=True)
    now = datetime.now(timezone.utc).isoformat()
    current = snapshot()
    records = authenticate()
    history = historical(current)
    if phase == 'after':
        prior = json.loads((evidence / 'input-before.json').read_text())
        assert current == prior, 'Audit interval input change'
    write_new(evidence / ('input-' + phase + '.json'), current)
    result = dict(phase=phase, captured_utc=now, entries=len(current),
                  authentication=records, historical=history,
                  fresh_interval_equal=(phase == 'after'))
    write_new(evidence / ('integrity-' + phase + '.json'), result)
    if phase == 'before':
        history_dir = OUT / 'original-history'
        history_dir.mkdir()
        for name in ('input-before.json', 'input-current.json', 'input-changes.json',
                     'core-final.json', 'preservation-result.json', 'preservation.log'):
            with (history_dir / name).open('xb') as f:
                f.write((ROOTS[0] / 'evidence' / name).read_bytes())
    print(json.dumps(result, indent=2, sort_keys=True))

if __name__ == '__main__':
    main()
