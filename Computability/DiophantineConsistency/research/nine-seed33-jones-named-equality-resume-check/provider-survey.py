#!/usr/bin/env python3
"""Point-survey audited recipe and named-formula providers and their union."""
import hashlib, json, os, subprocess, sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
P = Path(__file__).resolve().parent
D = P.parents[1]
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
audits = [
    ('nine-seed33-jones-vars-final-resume-terminal-independent',
     '2d391dbb65aabf55126a2128d978cd3b77f98675adc2804b1aa123c898c1a854',
     '0309c4e22c31310cc1a3e0f7f2098328102ed9b84d84e438519d8aee7081b39b'),
    ('nine-sharing-sign33-jones-named-formula-terminal-frontier-independent',
     '575fde2525dcefbeb6247d60d2384c5e46df126bafb41bc2399f2ff431ad702c',
     '2e733f665515dfc5af699e6258d4ccea164da125800e37642e23a832d5ebe24b'),
]
for folder, checker, result in audits:
    q = D / 'reviews' / folder
    assert H(q / 'check.py') == checker and H(q / 'result.json') == result
    p = subprocess.run([sys.executable, '-I', '-S', '-B', str(q / 'check.py')], capture_output=True, timeout=300)
    expected = 'PASS_TERMINAL_AUDIT' if folder.startswith('nine-seed33-') else 'PASS'
    assert p.returncode == 0 and not p.stderr and json.loads(p.stdout)['status'] == expected
states = [
    (D / 'research/nine-seed33-jones-vars-final-resume-check/attempt01/state.json',
     '40af7bbbf8c696b6c2442d5cfac89e41153b04d61216afeb04bc9e8cde07ba6b',
     Path('/tmp/nine-seed33-jones-vars-final-resume-check-20261110')),
    (D / 'research/nine-sharing-sign33-jones-named-formula-check/attempt01/state.json',
     'f9ed7a8e03b6458d4fef44370059d192a95bff3db6b2d12127dce16a17081964',
     Path('/tmp/nine-sharing-sign33-jones-named-formula-check-20261106')),
]
union = {}
for state_path, pin, root in states:
    assert H(state_path) == pin
    s = json.loads(state_path.read_text())
    assert s['status'] == 'PASS'
    for path, target in s['overlay_links'].items():
        q = Path(path)
        assert q.is_symlink() and str(q.resolve()) == target and q.is_file()
        rel = str(q.relative_to(root / 'lib'))
        value = {'realpath': target, 'sha256': H(q)}
        assert rel not in union or union[rel] == value
        union[rel] = value
    for row in s['rows']:
        name = row['module']
        q = root / 'lib/DiophantineConsistency' / (name + '.olean')
        assert q.is_file() and H(q) == row['object_sha256']
        rel = str(q.relative_to(root / 'lib'))
        value = {'realpath': str(q.resolve()), 'sha256': H(q)}
        assert rel not in union or union[rel] == value
        union[rel] = value
print(json.dumps({'status': 'PASS_POINT_IN_TIME_PROVIDER_SURVEY', 'union': union,
                  'scope': 'Audited producer objects and point-observed overlay union; no Lean or complete dynamic trace.'}, sort_keys=True))
