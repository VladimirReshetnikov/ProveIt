"""Reproduce complete-module metrics and verify the frozen reference sources."""
import ast
import difflib
import hashlib
import json
from pathlib import Path
from verify_mirror import metrics

ROOT = Path(__file__).resolve().parents[1]

def main():
    provenance = json.loads((ROOT / 'evidence/checker_source_provenance.json').read_text())
    for record in provenance['files']:
        raw = (ROOT / record['file']).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
        if blob != record['git_blob_sha1'] or hashlib.sha256(raw).hexdigest() != record['sha256']:
            raise ValueError('Frozen source mismatch: ' + record['file'])
    output = ROOT / 'evidence/normalized'
    output.mkdir(exist_ok=True)
    values, sources = {}, {}
    for name in ['diagonal_six', 'mirror_six']:
        path = ROOT / 'code' / (name + '.py')
        tree = ast.parse(path.read_text())
        if isinstance(tree.body[0], ast.Expr) and isinstance(tree.body[0].value, ast.Constant) and isinstance(tree.body[0].value.value, str):
            tree.body.pop(0)
        sources[name] = ast.unparse(tree) + '\n'
        (output / (name + '.py')).write_text(sources[name])
        values[name] = metrics(path)
    difference = ''.join(difflib.unified_diff(sources['diagonal_six'].splitlines(True), sources['mirror_six'].splitlines(True), fromfile='diagonal_six.normalized.py', tofile='mirror_six.normalized.py'))
    (ROOT / 'evidence/guard_change.diff').write_text(difference)
    report = {'method': 'Remove the actual module docstring, ast.unparse, append one LF; count the whole module.',
              'programs': values,
              'reduction': {key: values['diagonal_six'][key] - values['mirror_six'][key] for key in ['normalized_bytes', 'tokens', 'ast_nodes']},
              'verified_reference_blobs': len(provenance['files'])}
    (ROOT / 'evidence/metrics.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))

if __name__ == '__main__':
    main()
