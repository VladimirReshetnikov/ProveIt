"""Measure complete modules, including parsers and verdict drivers.

The producer and this measuring script are never imported by a checker.
Gzip is reported as information, not an optimization objective.
"""
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import platform
import tokenize
import zlib

ROOT = Path(__file__).resolve().parent


class WithoutDocstrings(ast.NodeTransformer):
    def generic_visit(self, node):
        super().generic_visit(node)
        if isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)) and node.body:
            first = node.body[0]
            if isinstance(first, ast.Expr) and isinstance(first.value, ast.Constant) \
                    and isinstance(first.value.value, str):
                node.body = node.body[1:]
        return node


def measure(path):
    raw = path.read_bytes()
    tree = WithoutDocstrings().visit(ast.parse(raw.decode('utf-8')))
    normalized = (ast.unparse(tree) + '\n').encode('utf-8')
    ignored = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL,
               tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT,
               tokenize.ENDMARKER}
    significant = sum(t.type not in ignored for t in
                      tokenize.generate_tokens(io.StringIO(normalized.decode()).readline))
    raw_gzip = gzip.compress(raw, compresslevel=9, mtime=0)
    normalized_gzip = gzip.compress(normalized, compresslevel=9, mtime=0)
    path.with_name(path.name + '.gz').write_bytes(raw_gzip)
    normalized_dir = ROOT / 'evidence' / 'normalized_sources'
    normalized_dir.mkdir(exist_ok=True)
    tag = path.parent.name + '_' + path.name
    (normalized_dir / tag).write_bytes(normalized)
    (normalized_dir / (tag + '.gz')).write_bytes(normalized_gzip)
    return {'file': str(path.relative_to(ROOT)), 'raw_bytes': len(raw),
            'normalized_bytes': len(normalized), 'tokens': significant,
            'ast_nodes': sum(1 for _ in ast.walk(tree)),
            'gzip9_raw_bytes': len(raw_gzip),
            'gzip9_normalized_bytes': len(normalized_gzip),
            'sha256_raw': hashlib.sha256(raw).hexdigest(),
            'sha256_normalized': hashlib.sha256(normalized).hexdigest()}


def main():
    selected = [
        ('reference/published_checker_bytes.py', 'Published byte leader'),
        ('reference/published_checker.py', 'Published explicit-list'),
        ('reference/published_checker_joint.py', 'Published token/AST leader'),
        ('code/control_compact.py', 'Matched inherited control'),
        ('code/control_explicit.py', 'Control, explicit-list'),
        ('code/checker_zero_compact.py', 'Uniform zero'),
        ('code/checker_zero_explicit.py', 'Uniform zero, explicit-list'),
        ('code/checker_constructed_compact.py', 'Constructed majors'),
        ('code/checker_constructed_explicit.py', 'Constructed, explicit-list'),
        ('code/checker_readable.py', 'Readable constructed checker'),
    ]
    rows = []
    for filename, label in selected:
        row = measure(ROOT / filename)
        row['label'] = label
        rows.append(row)
    payload = {'python': platform.python_version(), 'zlib': zlib.ZLIB_VERSION,
               'normalization': 'Remove genuine docstrings; ast.unparse plus newline.',
               'gzip': 'Level 9, mtime=0, no filename; complete gzip stream counted.',
               'profiles': rows}
    (ROOT / 'evidence' / 'metrics.json').write_text(json.dumps(payload, indent=2) + '\n')
    lines = [r'\begin{center}\small', r'\begin{tabular}{lrrrr}', r'\toprule',
             r'Complete program & Bytes & Tokens & AST & gzip-9\\', r'\midrule']
    for i, row in enumerate(rows):
        if i == 3:
            lines.append(r'\midrule')
        lines.append(f"{row['label']} & {row['normalized_bytes']} & {row['tokens']} & "
                     f"{row['ast_nodes']} & {row['gzip9_raw_bytes']}" + r'\\')
    lines += [r'\bottomrule', r'\end{tabular}', r'\end{center}',
              r'Bytes, tokens, and AST refer to the normalized complete module. '
              r'The gzip column counts the delivered raw source. The readable source '
              r'is 2,192 raw bytes; normalized gzip sizes are also recorded in '
              r'\file{evidence/metrics.json}. The published generic token/AST profile '
              r'has the malformed-string qualification described in the text.']
    (ROOT / 'evidence' / 'metrics_table.tex').write_text('\n'.join(lines) + '\n')
    print(json.dumps(payload, indent=2))


if __name__ == '__main__':
    main()
