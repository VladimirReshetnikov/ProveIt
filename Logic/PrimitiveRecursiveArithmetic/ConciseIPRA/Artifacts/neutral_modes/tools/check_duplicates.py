"""Check exact normalized ASTs against the bundled, attributed corpus indexes.

The frozen index and current incoming supplement are documentary census data.
This script rechecks their use; it does not claim a fresh network census.
"""
from pathlib import Path
import ast
import hashlib
import json
from measure import normalized_tree

ROOT = Path(__file__).resolve().parent.parent

def main():
    prior = json.loads((ROOT / 'reference/corpus_ast_index.json').read_text())
    recent = json.loads((ROOT / 'reference/current_incoming_ast_index.json').read_text())
    known = {}
    for row in prior:
        known.setdefault(row['normalized_ast_sha256'], []).append(row['path'])
    for row in recent:
        known.setdefault(row['normalized_ast_sha256'], []).append('current_incoming/' + row['path'])
    results = []
    for path in sorted((ROOT / 'code').glob('checker_*.py')):
        digest = hashlib.sha256(ast.dump(normalized_tree(path), include_attributes=False).encode()).hexdigest()
        results.append({'path': str(path.relative_to(ROOT)), 'normalized_ast_sha256': digest,
                        'identical_existing_sources': known.get(digest, [])})
    report = {'frozen_index_count': len(prior), 'current_incoming_python_count': len(recent),
              'scope': 'Exact-code duplication only, using the frozen 3247-source index plus the 56 Python files in the four inspected incoming archives. Not a new full repository census or a claim of mathematical priority.',
              'candidates': results}
    (ROOT / 'evidence/duplicate_check.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))
    if any(r['identical_existing_sources'] for r in results):
        raise SystemExit('A candidate duplicates a recorded existing AST.')

if __name__ == '__main__':
    main()
