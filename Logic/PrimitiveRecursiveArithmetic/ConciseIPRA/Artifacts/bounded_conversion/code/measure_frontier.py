"""Re-measure exact, retained complete comparator modules without executing them."""
import ast
import hashlib
import io
import json
import platform
import tokenize
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
manifest = json.loads((ROOT / 'reference/frontier_manifest.json').read_text())
skip = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
        tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
results = []
for entry in manifest['files']:
    data = (ROOT / entry['path']).read_bytes()
    normalized = ast.unparse(ast.parse(data)) + '\n'
    actual = {
        'tokens': sum(t.type not in skip for t in
                      tokenize.generate_tokens(io.StringIO(normalized).readline)),
        'ast_nodes': len(list(ast.walk(ast.parse(normalized)))),
        'normalized_bytes': len(normalized.encode()),
        'sha256': hashlib.sha256(data).hexdigest(),
    }
    if any(actual[key] != entry[key] for key in actual):
        raise ValueError('Comparator mismatch: ' + entry['label'])
    results.append(dict(label=entry['label'], path=entry['path'],
                        contract=entry['contract'], **actual))
report = {'python': platform.python_version(), 'reference_python': '3.12.14',
          'all_expected_metrics_match': True, 'measurements': results}
(ROOT / 'evidence/frontier_metrics.json').write_text(json.dumps(report, indent=2) + '\n')
print('Verified', len(results), 'complete comparator source hashes and measurements.')
