"""Record all sub-envelope noncandidate files and the normalization exception."""
from pathlib import Path
import ast
import io
import json
import tokenize
from census import ROOT, RemoveDocstrings, SKIP


def input_sites(tree):
    sites = []
    for n in ast.walk(tree):
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Name):
            if n.func.id == 'input':
                sites.append(ast.unparse(n))
            if n.func.id == 'open' and n.args and isinstance(n.args[0], ast.Constant) and n.args[0].value == 0:
                sites.append(ast.unparse(n))
        if isinstance(n, ast.Attribute) and n.attr == 'stdin':
            sites.append(ast.unparse(n))
    return sorted(set(sites))


def main():
    c = json.loads((ROOT / 'census.json').read_text())
    low = [r for r in c['rows'] if not r.get('possible_complete_acceptance_module')
           and 'error' not in r and (r['normalized_bytes'] < 495
                or r['significant_tokens'] < 249 or r['ast_nodes'] < 271)]
    rows = []
    for r in low:
        source = (ROOT / 'blobs' / (r['git_blob_sha'] + '.py')).read_bytes()
        tree = ast.parse(source)
        row = {k: r[k] for k in ['canonical_path', 'git_blob_sha', 'sha256',
                'imports', 'normalized_bytes', 'significant_tokens', 'ast_nodes']}
        row['module_docstring'] = ast.get_docstring(tree)
        row['direct_standard_input_sites'] = input_sites(tree)
        row['literal_accept_marker'] = r['contains_accept_marker']
        row['top_level_functions'] = [n.name for n in tree.body
                if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))]
        row['calls'] = sorted(set(ast.unparse(n.func) for n in ast.walk(tree)
                if isinstance(n, ast.Call)))
        row['scope_of_exclusion'] = (
            'Not a standalone module implementing the surveyed stdin-JSON/ACCEPT contract: '
            'no direct standard-input operation and no literal ACCEPT marker. '
            'These files are report/code builders, metric utilities, manifest checkers, '
            'test/certificate utilities, or harnesses that invoke separately charged programs. '
            'This screening is not a theorem about alternative I/O conventions.')
        rows.append(row)
    exceptions = []
    for r in c['errors']:
        raw = (ROOT / 'blobs' / (r['git_blob_sha'] + '.py')).read_bytes()
        original = ast.parse(raw)
        transformed = RemoveDocstrings().visit(original)
        text = ast.unparse(transformed) + '\n'
        diag = {
            'git_blob_sha': r['git_blob_sha'], 'path': r['canonical_path'],
            'source_valid_python': True, 'canonical_normalization_error': r['error'],
            'explanation': 'Removing the sole docstring from class Rejection leaves an empty suite. The exact shared normalizer does not insert pass, so its emitted text cannot be reparsed. The source itself is a readable reference checker and is valid Python.',
            'canonical_unparse_bytes': len(text.encode()),
            'canonical_unparse_tokens': sum(t.type not in SKIP for t in
                tokenize.generate_tokens(io.StringIO(text).readline)),
            'transformed_ast_nodes_before_reparse': sum(1 for _ in ast.walk(transformed))}
        inserted = 0
        for n in ast.walk(transformed):
            if isinstance(n, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)) and not n.body:
                n.body = [ast.Pass()]
                inserted += 1
        repaired = ast.unparse(transformed) + '\n'
        diag['diagnostic_repair_only'] = {
            'inserted_pass_statements': inserted,
            'normalized_bytes': len(repaired.encode()),
            'significant_tokens': sum(t.type not in SKIP for t in
                tokenize.generate_tokens(io.StringIO(repaired).readline)),
            'ast_nodes': sum(1 for _ in ast.walk(ast.parse(repaired))),
            'used_in_reported_coordinate_minima': False}
        exceptions.append(diag)
    result = {'pin': c['pin'], 'research_unique_blobs_hash_verified': sum(
        bool(r.get('git_blob_verified')) for r in c['rows']),
        'canonical_metrics_available': c['retrieved_and_measured'],
        'sub_envelope_noncandidate_count': len(rows),
        'all_exclusions_lack_direct_stdin_and_literal_accept': all(
            not r['direct_standard_input_sites'] and not r['literal_accept_marker'] for r in rows),
        'normalization_exceptions': exceptions,
        'sub_envelope_noncandidates': rows}
    (ROOT / 'exclusions.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ['research_unique_blobs_hash_verified',
        'canonical_metrics_available', 'sub_envelope_noncandidate_count',
        'all_exclusions_lack_direct_stdin_and_literal_accept']}))


if __name__ == '__main__':
    main()
