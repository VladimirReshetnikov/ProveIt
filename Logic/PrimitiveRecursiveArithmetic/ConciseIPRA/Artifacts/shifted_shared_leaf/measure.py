"""Measure complete source modules with the repository's conventions."""
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import sys
import tokenize
import zlib

ROOT = Path(__file__).resolve().parent
IGNORED = {tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE, tokenize.INDENT,
           tokenize.DEDENT, tokenize.ENCODING, tokenize.ENDMARKER}


def measure(path):
    normalized = ast.unparse(ast.parse(path.read_text())) + '\n'
    raw = normalized.encode('utf-8')
    return {
        'tokens': sum(t.type not in IGNORED for t in
                      tokenize.generate_tokens(io.StringIO(normalized).readline)),
        'ast_nodes': len(list(ast.walk(ast.parse(normalized)))),
        'normalized_bytes': len(raw),
        'gzip9_normalized_bytes': len(gzip.compress(raw, compresslevel=9, mtime=0)),
        'normalized_sha256': hashlib.sha256(raw).hexdigest(),
    }


def main():
    names = ['code/checker.py', 'controls/shared_leaf469.py', 'controls/offset472.py',
             'code/readable_checker.py', 'controls/tokens241.py', 'controls/ast262.py']
    report = {'python': sys.version, 'zlib': zlib.ZLIB_VERSION,
              'profiles': {name: measure(ROOT / name) for name in names}}
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
