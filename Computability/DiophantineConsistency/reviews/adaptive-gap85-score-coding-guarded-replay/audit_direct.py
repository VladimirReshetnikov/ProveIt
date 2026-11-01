#!/usr/bin/env python3
"""Recheck Cantor guards and Lean's direct-import resolution for both peers."""
import hashlib
import json
import os
from pathlib import Path
import subprocess

D = Path(__file__).resolve().parent
R = D.parents[3]
REPAIR = R / 'Computability/DiophantineConsistency/reviews/adaptive-gap85-score-cantor-repair'
m = json.loads((REPAIR/'manifest.json').read_text())
c = json.loads((REPAIR/'comparison.json').read_text())
receipt = json.loads((D/'comparison.json').read_text())
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert c['status'] == receipt['status'] == 'MATCHED_PASS'
assert c['manifest_sha256'] == sha(REPAIR/'manifest.json')
for path, digest in m['guard'].items():
    assert Path(path).is_file() and sha(path) == digest, path
count = 0
for module, candidates in m['candidates'].items():
    for path, expected in candidates.items():
        count += 1
        if expected is None:
            assert not os.path.lexists(path), path
        else:
            assert Path(path).is_file() and str(Path(path).resolve()) == expected['resolved'], path
            assert sha(path) == expected['sha256'], path
assert count == c['candidate_paths'] == 500
roots = [Path(receipt['author']), Path(receipt['peer'])]
dep_results = []
for root in roots:
    state = json.loads((root/'state.json').read_text())
    assert state['status'] == 'PASS' and state['cantor_repair_manifest_sha256'] == sha(REPAIR/'manifest.json')
    assert state['cantor_repair_receipt_sha256'] == sha(REPAIR/'comparison.json')
    env = dict(os.environ, LEAN_PATH=':'.join([str(root/'lib'), *state['boundary']]))
    env.pop('LEAN_SRC_PATH', None)
    source = root/'src/DiophantineConsistency/AdaptiveGap85ScoreCoding.lean'
    proc = subprocess.run([m['lean'], '--deps', str(source)], env=env, capture_output=True, text=True, check=True)
    actual = {str(Path(line).resolve()) for line in proc.stdout.splitlines()}
    cantor = m['selected']['BusyBeaver.ZFC.ArithmeticCantor']
    init = m['selected']['Init']
    least = root/'lib/DiophantineConsistency/AdaptiveGap85BalanceLeast.olean'
    assert actual == {cantor['resolved'], init['resolved'], str(least.resolve())}, actual
    assert sha(cantor['resolved']) == cantor['sha256'] and sha(init['resolved']) == init['sha256']
    least_parent = Path(state['provider'])/'lib/DiophantineConsistency/AdaptiveGap85BalanceLeast.olean'
    assert str(least.resolve()) == str(least_parent.resolve())
    assert sha(least) == state['anchors'][str(least_parent)]
    dep_results.append({'run': str(root), 'stdout_sha256': hashlib.sha256(proc.stdout.encode()).hexdigest(),
                        'resolved': sorted(actual)})
report = {'status': 'PASS', 'candidate_paths': count, 'runs': dep_results,
          'cantor_manifest_sha256': sha(REPAIR/'manifest.json'),
          'cantor_comparison_sha256': sha(REPAIR/'comparison.json'),
          'score_comparison_sha256': sha(D/'comparison.json'), 'auditor_sha256': sha(__file__),
          'scope': 'Direct import and companion checks only; transitive and dynamic ancestry inherited.'}
(D/'direct-audit.json').write_text(json.dumps(report, sort_keys=True, indent=2)+'\n')
print('PASS direct imports for two runs and', count, 'Cantor candidate paths')
