"""Measure every complete current root checker, preserving the whole-program boundary."""
import ast
import csv
import hashlib
import io
import json
from pathlib import Path
import platform
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
FIELDS = ('source_tokens', 'normalized_tokens', 'ast_nodes', 'normalized_bytes', 'raw_bytes')
IGNORED = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE,
           tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}


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


def significant(text):
    return sum(t.type not in IGNORED
               for t in tokenize.generate_tokens(io.StringIO(text).readline))


def metrics(path):
    raw = Path(path).read_bytes()
    source = raw.decode('utf-8')
    parsed = ast.parse(source)
    docstrings = set()
    for node in ast.walk(parsed):
        if isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            if (node.body and isinstance(node.body[0], ast.Expr)
                    and isinstance(node.body[0].value, ast.Constant)
                    and isinstance(node.body[0].value.value, str)):
                value = node.body[0].value
                docstrings.add(((value.lineno, value.col_offset),
                                (value.end_lineno, value.end_col_offset)))
    source_tokens = sum(t.type not in IGNORED and (t.start, t.end) not in docstrings
                        for t in tokenize.generate_tokens(io.StringIO(source).readline))
    tree = ast.fix_missing_locations(StripDocstrings().visit(parsed))
    normalized = ast.unparse(tree) + '\n'
    result = {'source_tokens': source_tokens,
              'normalized_tokens': significant(normalized),
              'ast_nodes': sum(1 for _ in ast.walk(tree)),
              'normalized_bytes': len(normalized.encode('utf-8')),
              'raw_bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}
    tree.body = [n for n in tree.body if not isinstance(n, (ast.Import, ast.ImportFrom))
                 and not (isinstance(n, ast.If) and '__name__' in ast.unparse(n.test))]
    normalized = ast.unparse(tree) + '\n'
    result['core'] = {'normalized_tokens': significant(normalized),
                      'ast_nodes': sum(1 for _ in ast.walk(tree)),
                      'normalized_bytes': len(normalized.encode('utf-8'))}
    return result


def main():
    manifest = json.loads((ROOT / 'manifest.json').read_text())
    rows = []
    for entry in manifest['programs']:
        measured = metrics(ROOT / entry['local_file'])
        if measured['sha256'] != entry['sha256']:
            raise ValueError('Changed comparator: ' + entry['local_file'])
        rows.append({**entry, **measured})
    minimum = {k: min(r[k] for r in rows) for k in FIELDS}
    core_minimum = {k: min(r['core'][k] for r in rows)
                    for k in ('normalized_tokens', 'ast_nodes', 'normalized_bytes')}
    result = {'python': platform.python_version(), 'implementation': platform.python_implementation(),
              'commit': manifest['commit'], 'archive_count': len(manifest['archives']),
              'program_count': len(rows), 'coordinatewise_minimum': minimum,
              'core_coordinatewise_minimum': core_minimum,
              'minimum_attainers': {k: [r['label'] for r in rows if r[k] == minimum[k]] for k in FIELDS},
              'programs': rows}
    (ROOT / 'metrics.json').write_text(json.dumps(result, indent=2) + '\n')
    fields = ('label', 'interface', 'witness_policy', 'proof_layout', *FIELDS, 'sha256')
    with (ROOT / 'metrics.csv').open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fields, extrasaction='ignore')
        writer.writeheader()
        writer.writerows(rows)
    if len(sys.argv) > 1:
        candidates = [{'file': str(Path(p).resolve()), **metrics(Path(p))} for p in sys.argv[1:]]
        result['candidates'] = candidates
        result['candidate_improvements'] = [{k: r[k] < minimum[k] for k in FIELDS} for r in candidates]
    print(json.dumps({k: v for k, v in result.items() if k != 'programs'}, indent=2))


if __name__ == '__main__':
    main()
