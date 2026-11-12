"""Offline whole-source measurements, including deterministic gzip level nine.

This file is not imported by any theorem checker. Frozen sources are parsed,
never imported or executed. The gzip values are information, not an objective.
"""
from pathlib import Path
import ast
import gzip
import hashlib
import io
import json
import platform
import tokenize
import zlib

ROOT = Path(__file__).resolve().parent
IGNORED = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
           tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


class StripDocstrings(ast.NodeTransformer):
    def clean(self, node):
        self.generic_visit(node)
        if (node.body and isinstance(node.body[0], ast.Expr)
                and isinstance(node.body[0].value, ast.Constant)
                and isinstance(node.body[0].value.value, str)):
            node.body = node.body[1:]
        return node

    visit_Module = clean
    visit_FunctionDef = clean
    visit_AsyncFunctionDef = clean
    visit_ClassDef = clean


def measure(raw):
    tree = ast.fix_missing_locations(StripDocstrings().visit(ast.parse(raw.decode('utf8'))))
    normalized = (ast.unparse(tree) + '\n').encode('utf8')
    tokens = tokenize.generate_tokens(io.StringIO(normalized.decode('utf8')).readline)
    return {
        'raw_bytes': len(raw),
        'normalized_bytes': len(normalized),
        'normalized_tokens': sum(item.type not in IGNORED for item in tokens),
        'ast_nodes': sum(1 for unused in ast.walk(tree)),
        'raw_gzip9_bytes': len(gzip.compress(raw, compresslevel=9, mtime=0)),
        'normalized_gzip9_bytes': len(gzip.compress(normalized, compresslevel=9, mtime=0)),
        'sha256': hashlib.sha256(raw).hexdigest(),
        'raw_lines': len(raw.splitlines()),
        'normalized_lines': len(normalized.splitlines()),
    }


def main():
    corpus = {}
    for path in sorted((ROOT / 'sources/python').glob('*.py')):
        row = measure(path.read_bytes())
        if path.stem != row['sha256']:
            raise ValueError('Frozen source hash mismatch: ' + path.name)
        corpus[path.stem] = row
    index = json.loads((ROOT / 'sources/python_index.json').read_text())
    if {item['sha256'] for item in index} != set(corpus):
        raise ValueError('Source index is incomplete')
    classifications = json.loads((ROOT / 'evidence/boundary_classification.json').read_text())
    roles = {item['sha256']: item['classification'] for item in classifications}
    boundary = {sha for sha, row in corpus.items()
                if row['normalized_tokens'] < 278 or row['ast_nodes'] < 312
                or row['normalized_bytes'] < 673}
    if boundary != set(roles):
        raise ValueError('Boundary inventory changed; check Python normalization version')
    complete = [corpus[sha] for sha, role in roles.items()
                if role == 'complete_documented_checker']
    metrics = ('normalized_tokens', 'ast_nodes', 'normalized_bytes')
    old_floor = {name: min(row[name] for row in complete) for name in metrics}
    names = ['checker.py', 'checker_bytes.py', 'checker_tokens.py',
             'checker_ast.py', 'readable_checker.py']
    programs = []
    for name in names:
        path = ROOT / 'code' / name
        raw = path.read_bytes()
        programs.append({'file': 'code/' + name, **measure(raw)})
        path.with_suffix('.py.gz').write_bytes(gzip.compress(raw, compresslevel=9, mtime=0))
    controls = []
    for name in ['baseline_constructed.py', 'baseline_scalar.py', 'baseline_ast.py', 'baseline_bytes.py']:
        controls.append({'file': 'reference/' + name,
                         **measure((ROOT / 'reference' / name).read_bytes())})
    new_floor = {name: min(row[name] for row in programs) for name in metrics}
    result = {
        'python': platform.python_version(), 'zlib': zlib.ZLIB_VERSION,
        'gzip_method': 'gzip.compress(data, compresslevel=9, mtime=0)',
        'frozen_distinct_sources': len(corpus), 'source_occurrences': len(index),
        'classified_boundary_sources': len(roles),
        'old_coordinate_envelope': old_floor, 'new_coordinate_envelope': new_floor,
        'one_program_strictly_below_all_old_minima': any(
            all(row[name] < old_floor[name] for name in metrics) for row in programs),
        'programs': programs, 'controls': controls,
    }
    (ROOT / 'evidence/measurements.json').write_text(json.dumps(result, indent=2) + '\n')
    (ROOT / 'evidence/corpus_remeasured.json').write_text(json.dumps(corpus, indent=2) + '\n')
    labels = ['Constructed computation', 'Matched scalar control', 'Transient AST control', 'Zero-product control']
    lines = [r'\begin{center}\small', r'\begin{tabular}{lrrrr}', r'\toprule',
             r'Complete source & Tokens & AST & Bytes & Gzip-9\\', r'\midrule']
    for label, row in zip(labels, controls):
        lines.append(f"{label} & {row['normalized_tokens']} & {row['ast_nodes']} & {row['normalized_bytes']} & {row['raw_gzip9_bytes']}" + r'\\')
    def envelope_row(label, values):
        cells = [r'\textbf{' + str(values[name]) + '}' for name in metrics]
        return label + ' & ' + ' & '.join(cells) + r' & --\\'
    lines += [r'\midrule', envelope_row('Old coordinate envelope', old_floor), r'\midrule']
    labels = ['New primary, ordinary list test', 'New byte profile', 'New token profile', 'New AST profile', 'Readable explanatory program']
    for label, row in zip(labels, programs):
        lines.append(f"{label} & {row['normalized_tokens']} & {row['ast_nodes']} & {row['normalized_bytes']} & {row['raw_gzip9_bytes']}" + r'\\')
    lines += [r'\midrule', envelope_row('New coordinate envelope', new_floor), r'\bottomrule', r'\end{tabular}', r'\end{center}',
              'Bytes are normalized UTF-8 bytes. Gzip-9 compresses the actual source,',
              'including its comments and layout, and is an informational column.',
              'The explanatory program therefore has a larger raw gzip size.',
              'Both raw and normalized gzip sizes are recorded in the evidence.']
    (ROOT / 'evidence/metrics_table.tex').write_text('\n'.join(lines) + '\n')
    print(json.dumps({key: value for key, value in result.items() if key not in ('programs', 'controls')}, indent=2))


if __name__ == '__main__':
    main()
