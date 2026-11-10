"""Remeasure every Python member in the fourteen-archive pinned source snapshot.

This is an audit utility, not a proof checker. It measures every source first;
classification only determines which files may witness a complete-kernel
frontier. All below-frontier sources were inspected in this research iteration.
"""
import ast
import hashlib
import io
import json
from pathlib import Path
import platform
import sys
import tokenize

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

def measure(path):
    raw = Path(path).read_bytes()
    parsed = ast.parse(raw.decode())
    doc = ast.get_docstring(parsed)
    tree = ast.fix_missing_locations(StripDocstrings().visit(parsed))
    normal = ast.unparse(tree) + '\n'
    return {'sha256': hashlib.sha256(raw).hexdigest(),
            'normalized_tokens': sum(t.type not in IGNORED for t in
                                     tokenize.generate_tokens(io.StringIO(normal).readline)),
            'ast_nodes': sum(1 for _ in ast.walk(tree)),
            'normalized_bytes': len(normal.encode()),
            'raw_bytes': len(raw), 'description': doc}

LATEST = 'ipra_kernel_and_initializer_2026-11-10/ipra_kernel_and_initializer_2026-11-10'
COUNTDOWN = 'ipra_countdown_retraction_2026-11-09/ipra_countdown_retraction_2026-11-09'
LEADERS = [(LATEST + '/code/' + name + '.py', 'silent_stderr')
           for name in ('tokens', 'structure', 'bytes')]
LEADERS += [(COUNTDOWN + '/code/driver_controls/' + name + '.py', 'traceback_stderr')
            for name in ('tokens', 'structure', 'bytes')]
LEADERS += [(COUNTDOWN + '/code/qi/matched_choice.py', 'traceback_stderr')]
COORDINATES = ('normalized_tokens', 'ast_nodes', 'normalized_bytes')

def envelope(rows):
    minima = {key: min(row[key] for row in rows) for key in COORDINATES}
    return {'minimum': minima, 'attainers': {
        key: [row['path'] for row in rows if row[key] == minima[key]] for key in COORDINATES}}

def main():
    base = Path(sys.argv[1]).resolve()
    destination = Path(sys.argv[2]).resolve() if len(sys.argv) > 2 else Path('frontier_audit.json')
    rows = {}
    for path in sorted(base.rglob('*.py')):
        row = measure(path)
        digest = row['sha256']
        if digest not in rows:
            rows[digest] = {**row, 'paths': []}
        rows[digest]['paths'].append(str(path.relative_to(base)))
    leaders = [{'path': path, 'rejection_interface': interface, **measure(base/path)}
               for path, interface in LEADERS]
    silent = envelope([row for row in leaders if row['rejection_interface'] == 'silent_stderr'])
    broad = envelope(leaders)
    leader_hashes = {row['sha256'] for row in leaders}
    low = []
    for row in rows.values():
        if any(row[key] < silent['minimum'][key] for key in COORDINATES):
            inspection = dict(row)
            if row['sha256'] in leader_hashes:
                inspection['classification'] = 'complete_checker_with_traceback_rejection'
                inspection['reason'] = 'Reviewed complete Choice-DI source; alternate stderr contract.'
            else:
                inspection['classification'] = 'utility_or_finite_diagnostic_not_complete_checker'
                inspection['reason'] = row['description']
                tree = ast.parse((base / row['paths'][0]).read_text())
                inspection['imports'] = [ast.unparse(n) for n in tree.body
                                         if isinstance(n, (ast.Import, ast.ImportFrom))]
                inspection['top_level_functions'] = [n.name for n in tree.body
                                                     if isinstance(n, ast.FunctionDef)]
            low.append(inspection)
    result = {
        'repository': 'VladimirReshetnikov/ProveIt',
        'commit': '6c902762efcb1e78a5dd25db745310bab74f47a5',
        'scope': 'Direct Python members of fourteen top-level draft ZIPs, including retained reference sources; nested ZIPs are not recursively expanded.',
        'python': platform.python_version(),
        'archive_count': len(list(base.glob('*.zip'))),
        'python_occurrences': sum(len(row['paths']) for row in rows.values()),
        'unique_python_sources': len(rows),
        'metric': 'Whole module; remove genuine docstrings; ast.unparse + newline; no renaming, driver deletion or dead-code elimination.',
        'silent_stderr_frontier': silent,
        'traceback_allowed_frontier': broad,
        'leading_complete_sources': leaders,
        'below_silent_frontier_source_review': low,
        'all_python_sources': list(rows.values()),
        'limits': [
            'These are empirical source minima, hence upper bounds on the unknown least checker complexity, not universal lower bounds.',
            'Different programs attain the coordinates.',
            'Classification is source review, not a mechanical theorem deciding completeness.',
            'Every source with a smaller coordinate was inspected; larger source completeness need not be adjudicated to establish these minima.',
            'A driver traceback change is not a mathematical axiomatization improvement.',
            'CPython and its JSON/list/arithmetic/exception runtime are common uncharged ambient dependencies.'
        ]}
    destination.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ('archive_count', 'python_occurrences', 'unique_python_sources', 'silent_stderr_frontier', 'traceback_allowed_frontier')}, indent=2))

if __name__ == '__main__':
    main()
