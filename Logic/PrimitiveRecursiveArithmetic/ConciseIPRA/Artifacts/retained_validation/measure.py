"""Measure complete modules using the repository's source convention."""
from pathlib import Path
import ast
import gzip
import hashlib
import io
import json
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
IGNORED = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
           tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def measure(path):
    tree = ast.parse(path.read_text())
    normalized = (ast.unparse(tree) + '\n').encode()
    return {
        'path': str(path.relative_to(ROOT)),
        'tokens': sum(t.type not in IGNORED for t in tokenize.generate_tokens(
            io.StringIO(normalized.decode()).readline)),
        'ast_nodes': sum(1 for _ in ast.walk(tree)),
        'normalized_bytes': len(normalized),
        'gzip9_normalized_bytes': len(gzip.compress(normalized, compresslevel=9, mtime=0)),
        'source_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
        'normalized_sha256': hashlib.sha256(normalized).hexdigest(),
    }


def main():
    paths = [ROOT/'code'/n for n in
             ('checker.py', 'checker_tokens.py', 'checker_nodes.py')]
    paths += [ROOT/'reference'/n for n in
              ('control_intrinsic.py', 'control_nodes.py', 'control_tokens.py')]
    result = {'python': sys.version, 'profiles': [measure(p) for p in paths],
              'significant_tokens_exclude_layout_and_comments': True,
              'normalized_source_has_one_final_newline': True,
              'whole_module_counted': True}
    (ROOT/'evidence/measurements.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
