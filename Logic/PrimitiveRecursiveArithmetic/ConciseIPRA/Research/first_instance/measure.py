"""Reproduce whole-module checker sizes; gzip-9 is an informational metric."""
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import platform
import tokenize

ROOT = Path(__file__).resolve().parent


class RemoveDocumentation(ast.NodeTransformer):
    def visit_Expr(self, node):
        if isinstance(node.value, ast.Constant) and isinstance(node.value.value, str):
            return None
        return self.generic_visit(node)


def metrics(path):
    source = path.read_bytes()
    tree = ast.fix_missing_locations(RemoveDocumentation().visit(ast.parse(source)))
    normalized = (ast.unparse(tree) + '\n').encode('utf-8')
    ignored = {tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE, tokenize.INDENT,
               tokenize.DEDENT, tokenize.ENDMARKER, tokenize.ENCODING}
    tokens = sum(token.type not in ignored for token in tokenize.tokenize(io.BytesIO(normalized).readline))
    return normalized, {'path': str(path.relative_to(ROOT)), 'source_bytes': len(source),
                        'normalized_bytes': len(normalized), 'significant_tokens': tokens,
                        'ast_nodes': sum(1 for _ in ast.walk(tree)),
                        'source_gzip9_bytes': len(gzip.compress(source, compresslevel=9, mtime=0)),
                        'normalized_gzip9_bytes': len(gzip.compress(normalized, compresslevel=9, mtime=0)),
                        'source_sha256': hashlib.sha256(source).hexdigest(),
                        'normalized_sha256': hashlib.sha256(normalized).hexdigest()}


def main():
    destination = ROOT / 'evidence/normalized'
    destination.mkdir(parents=True, exist_ok=True)
    paths = [ROOT/'code/checker.py', ROOT/'code/control_old.py',
             ROOT/'reference/witness_discharge.py', ROOT/'reference/uniform_binding.py',
             ROOT/'reference/compact516.py', ROOT/'reference/native788.py']
    for name in ['checker_fuel.py', 'control_fuel.py']:
        if (ROOT/'code'/name).exists():
            paths.append(ROOT/'code'/name)
    rows = []
    for path in paths:
        normal, row = metrics(path)
        name = str(path.relative_to(ROOT)).replace('/', '__')
        (destination/name).write_bytes(normal)
        (destination/(name + '.gz')).write_bytes(gzip.compress(normal, compresslevel=9, mtime=0))
        rows.append(row)
    result = {'python': platform.python_version(),
              'normalization': 'Remove string-expression documentation; ast.unparse; append LF.',
              'gzip': 'compresslevel=9, mtime=0; not minimized', 'checkers': rows}
    (ROOT/'evidence/metrics.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
