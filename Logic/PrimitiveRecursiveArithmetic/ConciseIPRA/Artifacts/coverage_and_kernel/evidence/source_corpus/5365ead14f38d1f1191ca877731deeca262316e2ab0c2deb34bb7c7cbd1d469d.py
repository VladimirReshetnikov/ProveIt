"""Whole-module measurements. The shared Python/JSON runtime is excluded.
All theory-specific code in each selected checker is included. Gzip is FYI.
"""
import ast
import gzip
import hashlib
import io
import json
import platform
import tokenize
import zlib
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE,
        tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}


class Strip(ast.NodeTransformer):
    def clean(self, node):
        self.generic_visit(node)
        if (node.body and isinstance(node.body[0], ast.Expr)
                and isinstance(node.body[0].value, ast.Constant)
                and isinstance(node.body[0].value.value, str)):
            node.body = node.body[1:]
        return node
    visit_Module = visit_FunctionDef = visit_AsyncFunctionDef = visit_ClassDef = clean


def measure(path):
    raw = path.read_bytes()
    tree = ast.fix_missing_locations(Strip().visit(ast.parse(raw)))
    normalized = (ast.unparse(tree)+'\n').encode()
    return {'path': str(path.relative_to(ROOT)),
            'sha256': hashlib.sha256(raw).hexdigest(),
            'normalized_bytes': len(normalized),
            'tokens': sum(t.type not in SKIP for t in tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)),
            'ast_nodes': sum(1 for _ in ast.walk(tree)),
            'raw_bytes': len(raw),
            'gzip9_raw_bytes': len(gzip.compress(raw, compresslevel=9, mtime=0)),
            'gzip9_normalized_bytes': len(gzip.compress(normalized, compresslevel=9, mtime=0))}


def main():
    selected = [ROOT/'code'/name for name in
                ['local_argument.py', 'local_argument_bytes.py',
                 'local_loop_joint.py', 'local_loop_joint_separate.py']]
    selected += sorted((ROOT/'reference').glob('baseline_checker*.py'))
    rows = []
    for path in selected:
        rows.append(measure(path))
        path.with_suffix(path.suffix+'.gz').write_bytes(gzip.compress(path.read_bytes(), compresslevel=9, mtime=0))
    corpus = []
    errors = []
    for path in sorted((ROOT/'reference/source_corpus').glob('*.py')):
        if hashlib.sha256(path.read_bytes()).hexdigest() != path.stem:
            raise ValueError('Frozen source hash mismatch: '+path.name)
        try:
            corpus.append(measure(path))
        except SyntaxError as error:
            errors.append({'file': path.name, 'error': str(error)})
    result = {'python': platform.python_version(), 'zlib': zlib.ZLIB_RUNTIME_VERSION,
              'programs': rows, 'frozen_sources': len(corpus)+len(errors),
              'parseable_sources': len(corpus), 'parse_errors': errors,
              'convention': 'Full source; genuine docstrings removed; ast.unparse plus newline; significant tokens; all AST nodes. Gzip9 mtime0 is informational.'}
    (ROOT/'evidence/measurements.json').write_text(json.dumps(result, indent=2)+'\n')
    (ROOT/'evidence/frozen_source_remeasurement.json').write_text(json.dumps(corpus, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
