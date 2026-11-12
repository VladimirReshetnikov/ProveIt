"""Additional strict-syntax rejection cases, partly overlapping the main fixtures."""
from pathlib import Path
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'code'))
import checker

if __name__ == '__main__':
    rejected = []
    for path in sorted((ROOT / 'validation' / 'syntax_rejections').glob('*.json')):
        data = json.loads(path.read_text())
        try:
            checker.check(data)
        except Exception:
            rejected.append(path.name)
        else:
            raise AssertionError('invalid certificate accepted: ' + path.name)
    if not rejected:
        raise AssertionError('missing syntax fixtures')
    result = {'rejected': len(rejected), 'files': rejected,
              'scope': 'Additional parser, scope, canonical-form and inferred-export rejection cases. Some overlap the main 16 negative fixtures; do not add the counts as distinct attacks.'}
    (ROOT / 'evidence' / 'syntax_audit.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'rejected': len(rejected)}, indent=2))
