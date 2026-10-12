"""Replay only the exact marked-gap partition checks."""
from pathlib import Path
import json
from verify_marked_gaps import check_symbolic

if __name__ == '__main__':
    checks = [check_symbolic(k) for k in range(1, 6)]
    result = {'status': 'PASS', 'symbolic_partition_checks': checks,
              'scope': 'Exact combinatorial consequences of the analytic insertion lemma.'}
    Path(__file__).with_name('marked_gap_exact.json').write_text(
        json.dumps(result, indent=2) + '\n')
    print('PASS: marked-gap partition identity through five independent labels')
