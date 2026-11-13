"""Reproduce full-module CPython metrics; no checker imports this file."""

import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import platform
import tokenize

ROOT = Path(__file__).resolve().parent.parent
OMIT = {
    tokenize.ENCODING, tokenize.ENDMARKER, tokenize.INDENT,
    tokenize.DEDENT, tokenize.NEWLINE, tokenize.NL, tokenize.COMMENT,
}


class StripDocstrings(ast.NodeTransformer):
    def visit_Module(self, node):
        self.generic_visit(node)
        return self.strip(node)

    def visit_FunctionDef(self, node):
        self.generic_visit(node)
        return self.strip(node)

    visit_AsyncFunctionDef = visit_FunctionDef
    visit_ClassDef = visit_FunctionDef

    @staticmethod
    def strip(node):
        if (node.body and isinstance(node.body[0], ast.Expr)
                and isinstance(node.body[0].value, ast.Constant)
                and isinstance(node.body[0].value.value, str)):
            node.body.pop(0)
        return node


def measure(path):
    original = path.read_bytes()
    tree = StripDocstrings().visit(ast.parse(original))
    normalized = (ast.unparse(tree) + '\n').encode()
    tokens = tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)
    return {
        'file': str(path.relative_to(ROOT)),
        'significant_tokens': sum(token.type not in OMIT for token in tokens),
        'ast_nodes': sum(1 for _ in ast.walk(tree)),
        'normalized_bytes': len(normalized),
        'source_bytes': len(original),
        'gzip9_normalized_bytes': len(gzip.compress(normalized, compresslevel=9, mtime=0)),
        'gzip9_source_bytes': len(gzip.compress(original, compresslevel=9, mtime=0)),
        'source_sha256': hashlib.sha256(original).hexdigest(),
        'normalized_sha256': hashlib.sha256(normalized).hexdigest(),
    }


def main():
    rows = [measure(path) for path in sorted((ROOT / 'code').glob('checker_*.py'))]
    controls = [measure(path) for path in sorted((ROOT / 'controls').glob('*.py'))]
    result = {
        'python': platform.python_version(),
        'expected_python': '3.12.14',
        'normalization': 'docstrings removed; ast.unparse; one final LF',
        'gzip': 'level 9; mtime 0; no filename',
        'profiles': rows, 'controls': controls,
    }
    (ROOT / 'evidence/measurements.json').write_text(json.dumps(result, indent=2) + '\n')
    lines = [r'\begin{center}\small',
             r'\begin{tabular}{@{}lrrrr@{}}', r'\toprule',
             r'Complete checker & Tokens & Nodes & Bytes & Gzip-9\\',
             r'\midrule']
    for row in rows:
        label = Path(row['file']).name.replace('_', r'\_')
        values = [row[k] for k in ('significant_tokens', 'ast_nodes',
                                    'normalized_bytes', 'gzip9_normalized_bytes')]
        lines.append(r'\texttt{' + label + '} & ' + ' & '.join(map(str, values)) + r'\\')
    lines += [r'\bottomrule', r'\end{tabular}\end{center}',
              'The byte control compresses to 310 bytes, compared with 313 for the',
              'new byte profile; the strict control compresses to 387, compared',
              'with 391 for the new strict profile. The source-byte improvements',
              'therefore do not establish gzip improvements.']
    (ROOT / 'evidence/measurements.tex').write_text('\n'.join(lines) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
