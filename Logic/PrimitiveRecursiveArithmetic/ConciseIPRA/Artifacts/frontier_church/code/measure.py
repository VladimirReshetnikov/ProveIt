"""Remeasure the eight archived incumbent modules without executing them."""
from pathlib import Path
import ast
import gzip
import hashlib
import io
import json
import platform
import tokenize
import zlib

ROOT = Path(__file__).resolve().parents[1]
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
        tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
EXPECTED = {
    'compact_tokens239.py': [239, 261, 549, 332],
    'compact_ast256.py': [245, 256, 580, 342],
    'compact_shifted461.py': [267, 298, 461, 313],
    'whole_tokens244.py': [244, 269, 547, 338],
    'whole_ast261.py': [252, 261, 593, 356],
    'strict_tokens317.py': [317, 368, 634, 398],
    'strict_ast356.py': [325, 356, 646, 399],
    'strict_bytes597.py': [328, 372, 597, 392],
}


def normalized(raw):
    tree = ast.parse(raw)
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)) and node.body:
            first = node.body[0]
            if (isinstance(first, ast.Expr)
                    and isinstance(first.value, ast.Constant)
                    and type(first.value.value) is str):
                node.body.pop(0)
    return (ast.unparse(tree) + '\n').encode('utf-8')


def measure(name):
    path = ROOT / 'reference' / 'checkers' / name
    raw = path.read_bytes()
    source = normalized(raw)
    packed = gzip.compress(source, compresslevel=9, mtime=0)
    tokens = sum(t.type not in SKIP for t in tokenize.generate_tokens(
        io.StringIO(source.decode()).readline))
    nodes = sum(1 for _ in ast.walk(ast.parse(source)))
    values = [tokens, nodes, len(source), len(packed)]
    stored = path.with_suffix(path.suffix + '.gz').read_bytes()
    return {
        'file': str(path.relative_to(ROOT)),
        'raw_bytes': len(raw),
        'raw_sha256': hashlib.sha256(raw).hexdigest(),
        'normalized_sha256': hashlib.sha256(source).hexdigest(),
        'tokens': tokens,
        'ast_nodes': nodes,
        'normalized_bytes': len(source),
        'gzip9_bytes': len(packed),
        'expected': EXPECTED[name],
        'matches_expected': values == EXPECTED[name],
        'stored_gzip_decodes_to_normalized_source': gzip.decompress(stored) == source,
        'stored_gzip_is_reproduced_exactly': stored == packed,
    }


def result():
    profiles = [measure(name) for name in EXPECTED]
    return {
        'python': platform.python_version(),
        'zlib': zlib.ZLIB_RUNTIME_VERSION,
        'normalization': 'Remove genuine docstrings; ast.unparse plus one final LF',
        'gzip': 'level=9, mtime=0, no filename; compressed normalized source',
        'new_checker_record_claimed': False,
        'profiles': profiles,
        'all_match': all(p['matches_expected'] for p in profiles),
        'all_gzip_members_verified': all(
            p['stored_gzip_decodes_to_normalized_source'] for p in profiles),
    }


if __name__ == '__main__':
    print(json.dumps(result(), indent=2))
