"""Offline reproduction of metrics, structural checks, fixtures and corpus census."""
from pathlib import Path
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent

def main():
    steps = []
    for name in ['measure.py', 'verify.py', 'audit/census.py']:
        result = subprocess.run([sys.executable, '-I', '-S', '-B', str(ROOT / name)],
                                cwd=ROOT, text=True, capture_output=True, timeout=180)
        steps.append({'script': name, 'exit_code': result.returncode})
        print(name + ': ' + ('PASS' if result.returncode == 0 else 'FAIL'))
        if result.returncode:
            print(result.stdout)
            print(result.stderr)
            raise SystemExit(result.returncode)
    metrics = json.loads((ROOT / 'evidence/metrics.json').read_text())
    verification = json.loads((ROOT / 'evidence/verification.json').read_text())
    census = json.loads((ROOT / 'audit/census_receipt.json').read_text())
    receipt = {
        'python': sys.version,
        'steps': steps,
        'regression_cases': verification['case_count'],
        'isolated_executions': verification['executions'],
        'unexpected_outcomes': len(verification['failures']),
        'size_rows': metrics['rows'],
        'corpus_distinct_modules': census['distinct_normalized_modules'],
        'corpus_parse_or_decode_errors': census['parse_or_decode_errors'],
        'corpus_git_blob_mismatches': census['git_blob_mismatches'],
        'candidate_corpus_matches': {k: v['matching_corpus_paths'] for k, v in census['candidate_novelty'].items()},
        'formalization_status': 'Written operational proof plus structural checks; inherited arithmetic bridge. No new Lean/Rocq proof.',
    }
    if verification['failures'] or census['parse_or_decode_errors'] or census['git_blob_mismatches']:
        raise SystemExit('A validation obligation failed.')
    (ROOT / 'evidence/reproduction.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print('All offline checks passed.')

if __name__ == '__main__':
    main()
