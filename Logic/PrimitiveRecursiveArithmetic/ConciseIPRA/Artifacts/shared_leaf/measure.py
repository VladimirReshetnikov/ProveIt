"""Recompute complete-module metrics; no measured checker imports this file."""
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import platform
import sys
import tokenize
import zlib

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.INDENT,
        tokenize.DEDENT, tokenize.NEWLINE, tokenize.NL, tokenize.COMMENT}


def measure(path):
    raw = path.read_bytes()
    normalized = (ast.unparse(ast.parse(raw)) + '\n').encode()
    tree = ast.parse(normalized)
    tokens = tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)
    packed = gzip.compress(normalized, compresslevel=9, mtime=0)
    return {
        'file': str(path.relative_to(ROOT)),
        'significant_tokens': sum(t.type not in SKIP for t in tokens),
        'ast_nodes': sum(1 for _ in ast.walk(tree)),
        'normalized_utf8_bytes': len(normalized),
        'normalized_gzip9_bytes': len(packed),
        'source_utf8_bytes': len(raw),
        'source_gzip9_bytes': len(gzip.compress(raw, compresslevel=9, mtime=0)),
        'source_sha256': hashlib.sha256(raw).hexdigest(),
        'normalized_sha256': hashlib.sha256(normalized).hexdigest(),
        'normalized_gzip9_sha256': hashlib.sha256(packed).hexdigest(),
    }


def main():
    names = ['checker_tokens.py', 'checker_ast.py', 'checker_bytes.py']
    candidates = [measure(ROOT / 'code' / name) for name in names]
    controls = [measure(ROOT / 'controls' / name) for name in names]
    for name in names:
        raw = (ROOT / 'code' / name).read_bytes()
        normalized = (ast.unparse(ast.parse(raw)) + '\n').encode()
        (ROOT / 'code' / (name + '.gz')).write_bytes(gzip.compress(normalized, compresslevel=9, mtime=0))
    columns = ['significant_tokens', 'ast_nodes', 'normalized_utf8_bytes']
    envelope = lambda rows: {key: min(row[key] for row in rows) for key in columns}
    report = {
        'python': sys.version,
        'implementation': platform.python_implementation(),
        'zlib_runtime_version': zlib.ZLIB_RUNTIME_VERSION,
        'normalization': 'ast.unparse(ast.parse(complete source)) plus one LF',
        'token_exclusions': sorted(tokenize.tok_name[x] for x in SKIP),
        'gzip': {'compresslevel': 9, 'mtime': 0},
        'repository': 'https://github.com/VladimirReshetnikov/ProveIt',
        'pinned_commit': '12197d86f63e9ec73b2d91399c4de2a8cb0077ee',
        'control_archive': 'Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/docs/incoming/ipra_computation_leaves_2026-11-12.zip',
        'control_members': ['ipra_computation_leaves/code/' + name for name in names],
        'controls': controls,
        'candidates': candidates,
        'control_family_envelope': envelope(controls),
        'candidate_family_envelope': envelope(candidates),
        'envelopes_are_attained_by_different_programs': True,
        'readable_expansion': measure(ROOT / 'code' / 'readable_checker.py'),
    }
    (ROOT / 'evidence' / 'metrics.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: report[k] for k in ['control_family_envelope', 'candidate_family_envelope']}, indent=2))


if __name__ == '__main__':
    main()
