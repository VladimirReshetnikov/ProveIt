"""Remeasure complete modules and check the frozen neutral-marker regression set."""
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import platform
import subprocess
import sys
import tokenize
import zlib

from convert import audit_positive, zero_neutral

ROOT = Path(__file__).resolve().parent
PROFILES = ('bytes', 'ast', 'strict')


def measure(path):
    raw = path.read_bytes()
    normalized = (ast.unparse(ast.parse(raw)) + '\n').encode()
    ignored = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL,
               tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT,
               tokenize.ENDMARKER}
    compressed = gzip.compress(normalized, compresslevel=9, mtime=0)
    return {
        'file': str(path.relative_to(ROOT)),
        'significant_tokens': sum(token.type not in ignored for token in
            tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)),
        'ast_nodes': len(list(ast.walk(ast.parse(normalized)))),
        'normalized_bytes': len(normalized),
        'gzip9_normalized_bytes': len(compressed),
        'raw_bytes': len(raw),
        'sha256': hashlib.sha256(raw).hexdigest(),
    }, compressed


def run(path, data, optimized):
    args = [sys.executable] + (['-O'] if optimized else []) + [str(path)]
    try:
        result = subprocess.run(args, input=data, capture_output=True, timeout=20)
        return {'accepted': result.returncode == 0 and result.stdout == b'ACCEPT\n',
                'returncode': result.returncode, 'timeout': False}
    except subprocess.TimeoutExpired:
        return {'accepted': False, 'returncode': None, 'timeout': True}


def main():
    metrics = []
    for folder in ('reference', 'code'):
        for profile in PROFILES:
            path = ROOT / folder / f'checker_{profile}.py'
            row, compressed = measure(path)
            metrics.append(row)
            if folder == 'code':
                path.with_suffix('.py.gz').write_bytes(compressed)
    cases = json.loads((ROOT / 'tests/cases.json').read_text())
    receipts, audits = [], []
    for case in cases:
        old_path = ROOT / 'tests/old' / case['file']
        packet = json.loads(old_path.read_text())
        if case['expected_compact']:
            audits.append({'case': case['file'], **audit_positive(packet)})
        converted = zero_neutral(packet)
        new_data = (json.dumps(converted, separators=(',', ':')) + '\n').encode()
        (ROOT / 'tests/zero' / case['file']).write_bytes(new_data)
        for folder, data in (('reference', old_path.read_bytes()), ('code', new_data)):
            for profile in PROFILES:
                expected = case['expected_strict'] if profile == 'strict' else case['expected_compact']
                checker = ROOT / folder / f'checker_{profile}.py'
                for optimized in (False, True):
                    receipts.append({'checker': str(checker.relative_to(ROOT)),
                        'case': case['file'], 'optimized': optimized, 'expected': expected,
                        **run(checker, data, optimized)})
    # The old spelling is not a backwards-compatible input convention.
    # Check its deliberate rejection on the simplest unchanged I0 packet.
    old_data = (ROOT / 'tests/old/computation_zero_local.json').read_bytes()
    for profile in PROFILES:
        checker = ROOT / 'code' / f'checker_{profile}.py'
        for optimized in (False, True):
            receipts.append({'checker': str(checker.relative_to(ROOT)),
                'case': 'stale_neutral_spelling_control', 'optimized': optimized,
                'expected': False, **run(checker, old_data, optimized)})
    failures = [row for row in receipts if row['accepted'] != row['expected']]
    result = {
        'python': sys.version,
        'implementation': platform.python_implementation(),
        'zlib_version': zlib.ZLIB_VERSION,
        'zlib_runtime_version': zlib.ZLIB_RUNTIME_VERSION,
        'normalization': 'ast.unparse(ast.parse(source)) + newline; complete module',
        'gzip': 'gzip.compress(normalized, compresslevel=9, mtime=0)',
        'metrics': metrics,
    }
    validation = {
        'executions': len(receipts),
        'expected_acceptances': sum(row['expected'] for row in receipts),
        'expected_rejections': sum(not row['expected'] for row in receipts),
        'failures': failures,
        'timeouts': sum(row['timeout'] for row in receipts),
        'receipts': receipts,
        'positive_packet_audits': audits,
        'claim': 'Finite regression evidence; not a proof of universal checker soundness or iPRA bi-interpretability.',
    }
    (ROOT / 'evidence/measurements.json').write_text(json.dumps(result, indent=2) + '\n')
    (ROOT / 'evidence/validation.json').write_text(json.dumps(validation, indent=2) + '\n')
    print(json.dumps({'metrics': metrics, 'executions': len(receipts),
                      'failures': failures, 'timeouts': validation['timeouts']}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
