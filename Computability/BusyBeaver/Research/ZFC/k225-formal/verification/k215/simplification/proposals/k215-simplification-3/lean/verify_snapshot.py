#!/usr/bin/env python3
"""Reproduce source-only Lean K215 audits from the bundled pinned snapshot.

Run: python3 -B verify_snapshot.py
No network, Git checkout, Lean compiler, or third-party package is needed.
This checks literal data and source dependencies, not Lean theorem correctness.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import re
import sys

if not __debug__:
    raise SystemExit('ERROR: do not run with -O or -OO; assertions are required.')
ROOT = Path(__file__).resolve().parent
ZFC = ROOT / 'snapshot/Computability/BusyBeaver/Lean/BusyBeaver/ZFC'
PIN = 'b6fb232916d008383e7cf2990d68ddb30fded7db'

def read(name: str) -> str:
    return (ZFC / name).read_text(encoding='utf-8')

def source_certificate_audit() -> dict:
    path = ZFC / 'KSource215Data.lean'
    raw = path.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == '33027ee1a573e7d50ed42547c0ec3fea552e1ea3d0b301967817fde34b8af8ed', 'Pinned source changed'
    s = raw.decode('utf-8')
    assert s.count('def fwd0 : OTree :=') == s.count('def bwd0 : OTree :=') == 1
    f = s[s.index('def fwd0 :'):s.index('def bwd0 :')]
    b = s[s.index('def bwd0 :'):]
    entry = re.compile(r'\.leaf\s*\((\d+),\s*(\d+),\s*\((-?\d+)\s*:\s*Int\),\s*(\d+),\s*(\d+)\)')
    fes = [tuple(map(int, x)) for x in entry.findall(f)]
    bes = [tuple(map(int, x)) for x in entry.findall(b)]
    assert len(fes) == len(bes) == 2240
    assert f.count('.leaf') == len(fes) and b.count('.leaf') == len(bes), 'Unparsed certificate leaf'
    assert {x[2] for x in fes} == {0}
    assert bes == [(q, p, -z, u, v) for p, q, z, u, v in fes]
    assert all(p >= 1 and q >= 1 and 0 <= u < 2240 and 0 <= v < 2240 for p, q, z, u, v in fes)
    max_left = max(x[0].bit_length() - 1 for x in fes)
    max_right = max(x[1].bit_length() - 1 for x in fes)
    assert (max_left, max_right) == (45, 176)
    result = {
        'source_sha256': hashlib.sha256(raw).hexdigest(),
        'forward_entries': len(fes), 'backward_entries': len(bes),
        'offsets': sorted({x[2] for x in fes}), 'backward_exact_mirror': True,
        'max_forward_path_bits': max_left, 'max_target_path_bits': max_right,
        'backward_section_bytes': len(b.encode()), 'backward_section_lines': len(b.splitlines()),
    }
    assert result == json.loads((ROOT / 'source_certificate_audit.json').read_text())
    return result

def import_audit() -> dict:
    data = read('KSource215Data.lean')
    expected_blobs = {
        'KSites215Batch000.lean': 'f655f78081fd6cfd1fb6c04f997817cb116b6213',
        'KSites215Batch001.lean': '6a7932e94802b79f937d31703889dec295fcfdd1',
        'KSites215Batch002.lean': 'be8fb3aaacc9873ae596025a0fe7713703a5dbb7',
        'KSites215Batch003.lean': '15d5f79a89f1c895832d99f8579ccc1cc0b3c371',
        'KSites215Batch004.lean': 'fb6062738b494ef091a3098257a92a7d6407d60d',
        'KSites215Batch005.lean': '50a35aeb53702a7464c61090ed3df6400d8b93ac',
        'KSites215Batch006.lean': '8872dcdd3d890cf82393fc67e7f6251eab150738',
        'KSites215Batch007.lean': '47297cb99c1f093481ad3afee79167e42582ed7c',
        'KSites215Batch008.lean': 'ad41cc27e4b789cdf26c41b2505c55744687b105',
    }
    for name, sha in expected_blobs.items():
        raw = (ZFC / name).read_bytes()
        actual = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
        assert actual == sha, 'Pinned site batch changed: ' + name
    batches = sorted(ZFC.glob('KSites215Batch*.lean'))
    assert [p.name for p in batches] == [f'KSites215Batch{i:03}.lean' for i in range(9)]
    files = batches + [ZFC / 'KSites215.lean']
    refs = set()
    for p in files:
        s = p.read_text()
        refs.update(re.findall(r'KSource215\.([A-Za-z0-9_]+)', s))
        if p in batches:
            assert s.startswith('import BusyBeaver.ZFC.KSource215\n')
            new = s.replace('import BusyBeaver.ZFC.KSource215\n', 'import BusyBeaver.ZFC.KSource215Data\n')
            assert new.splitlines()[1:] == s.splitlines()[1:]
    assert refs == {'p215', 't215', 't215_eq'}
    for name in refs:
        assert re.search(r'^(?:def|theorem) ' + name + r'\b', data, re.M)
    patch = (ROOT / 'site_import_split.uncompiled.patch').read_text()
    assert patch.count('-import BusyBeaver.ZFC.KSource215\n') == 9
    assert patch.count('+import BusyBeaver.ZFC.KSource215Data\n') == 9
    assert patch.count('+import BusyBeaver.ZFC.KSource215\n') == 1
    for line in patch.splitlines():
        if line.startswith(('+++', '---')):
            continue
        if line.startswith(('+', '-')):
            assert line[1:].startswith('import '), 'Patch edits non-import source'
    result = {
        'status': 'STATIC_ONLY_NOT_COMPILED', 'batch_files': [p.name for p in batches],
        'modified_only_import_lines': True, 'facade_preserves_full_source_import': True,
        'referenced_source_symbols': sorted(refs), 'all_in_KSource215Data': True,
    }
    assert result == json.loads((ROOT / 'site_import_static_audit.json').read_text())
    return result

if __name__ == '__main__':
    print(json.dumps({'status': 'PASS_SOURCE_AUDITS_ONLY_NOT_LEAN', 'snapshot_commit': PIN,
        'source_certificate': source_certificate_audit(), 'site_imports': import_audit()}, indent=2))
