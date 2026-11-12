"""Complete-module measurements under the repository convention."""
from pathlib import Path
import ast
import gzip
import hashlib
import io
import json
import platform
import tokenize

ROOT = Path(__file__).resolve().parent
FILES = ['checker.py', 'control_explicit_witness.py',
         'control_template_validation.py', 'checker_fuel.py',
         'control_explicit_witness_fuel.py',
         'reference/explicit_name.py', 'reference/inferred_opening.py']
OMIT = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
        tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def measure(path):
    raw = path.read_bytes()
    tree = ast.parse(raw)
    if (tree.body and isinstance(tree.body[0], ast.Expr)
            and isinstance(tree.body[0].value, ast.Constant)
            and isinstance(tree.body[0].value.value, str)):
        tree.body.pop(0)
    normalized = (ast.unparse(tree) + '\n').encode()
    return dict(file=str(path.relative_to(ROOT)), raw_bytes=len(raw),
                normalized_bytes=len(normalized),
                significant_tokens=sum(t.type not in OMIT for t in
                    tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)),
                ast_nodes=sum(1 for _ in ast.walk(tree)),
                gzip9=len(gzip.compress(normalized, 9, mtime=0)),
                sha256=hashlib.sha256(raw).hexdigest())


def main():
    result = {'python': platform.python_version(),
              'normalization': 'Remove module docstring; ast.unparse; one final LF.',
              'programs': [measure(ROOT / path) for path in FILES]}
    (ROOT / 'measurements.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
