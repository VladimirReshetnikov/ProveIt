"""Independently reproduce pinned whole-input metrics and framing comparisons.

The frontier coordinates belong to different complete programs. The finite
executions below supplement the inherited framing proof; they are not a
formal soundness or bi-interpretability proof.
"""
import ast
import gzip
import hashlib
import io
import json
import platform
import subprocess
import sys
import tokenize
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'baseline' / 'whole_json_refinement'
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
        tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
PAIRS = {
    'global': ('code/checker_tokens248.py', 'reference/checker_tokens.py'),
    'local': ('code/checker_ast268.py', 'reference/checker_ast.py'),
}

def git_blob(raw):
    return hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()

def measure(path):
    raw = path.read_bytes()
    source = (ast.unparse(ast.parse(raw)) + '\n').encode()
    return {'path': str(path.relative_to(ROOT)),
            'tokens': sum(t.type not in SKIP for t in tokenize.generate_tokens(
                io.StringIO(source.decode()).readline)),
            'ast_nodes': len(list(ast.walk(ast.parse(source)))),
            'normalized_bytes': len(source),
            'gzip9_bytes': len(gzip.compress(source, compresslevel=9, mtime=0)),
            'sha256': hashlib.sha256(raw).hexdigest(),
            'git_blob_sha1': git_blob(raw)}

def execute(path, data, optimized):
    command = [sys.executable, '-I', '-S', '-B']
    if optimized:
        command.append('-O')
    try:
        result = subprocess.run(command + [str(path)], input=data,
                                capture_output=True, timeout=30)
        return result.returncode == 0 and result.stdout == b'ACCEPT\n'
    except subprocess.TimeoutExpired:
        return 'timeout'

def main():
    provenance = json.loads((ROOT / 'audit' / 'whole_json_sources.json').read_text())
    identities = []
    for source in provenance['sources']:
        raw = (BASE / source['path']).read_bytes()
        identities.append({'path': source['path'], 'expected_blob': source['sha'],
                           'actual_blob': git_blob(raw),
                           'passed': len(raw) == source['size'] and git_blob(raw) == source['sha']})
    paths = [BASE / 'code' / 'checker_tokens248.py',
             BASE / 'code' / 'checker_ast268.py',
             ROOT / 'baseline' / 'shared_leaf' / 'code' / 'checker_bytes.py',
             BASE / 'reference' / 'checker_tokens.py',
             BASE / 'reference' / 'checker_ast.py']
    measurements = [measure(path) for path in paths]
    cases = json.loads((BASE / 'fixtures' / 'cases.json').read_text())
    comparisons = []
    for case in cases:
        payload = (BASE / 'fixtures' / case['file']).read_bytes()
        trees = json.loads(payload)
        stream = ''.join(json.dumps(tree) + '\n' for tree in reversed(trees)).encode()
        profiles = tuple(PAIRS) if case['profile'] == 'both' else (case['profile'],)
        for profile in profiles:
            candidate, control = PAIRS[profile]
            for optimized in (False, True):
                new = execute(BASE / candidate, payload, optimized)
                old = execute(BASE / control, stream, optimized)
                comparisons.append({'fixture': case['file'], 'profile': profile,
                                    'optimized': optimized, 'expected': case['expected'],
                                    'whole_input_accepted': new, 'stream_accepted': old,
                                    'passed': new == old == case['expected']})
    report = {'repository': 'VladimirReshetnikov/ProveIt',
              'commit': provenance['commit'], 'python': platform.python_version(),
              'scope': 'Pinned-source identity, complete-module measurements, and finite framing checks.',
              'whole_input_envelope': {'tokens': 248, 'ast_nodes': 268, 'normalized_bytes': 469},
              'envelope_note': 'Different programs attain the three coordinates.',
              'measurements': measurements, 'fixture_count': len(cases),
              'paired_comparisons': len(comparisons), 'executions': 2 * len(comparisons),
              'source_identity_checks': identities,
              'failed_source_identities': [row for row in identities if not row['passed']],
              'failed_expectations': [row for row in comparisons if not row['passed']],
              'comparisons': comparisons}
    (ROOT / 'audit' / 'whole_json_receipt.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({key: value for key, value in report.items()
                      if key not in {'source_identity_checks', 'comparisons'}}, indent=2))
    if report['failed_source_identities'] or report['failed_expectations']:
        raise SystemExit(1)

if __name__ == '__main__':
    main()
