"""Read-only measurement of the pinned Artifacts Python corpus.

Input JSON files contain exact GitHub blob data fetched through the GitHub app.
No repository program is imported or executed. Corpus membership and soundness
are separate questions; inspect the explicit exclusions in census_receipt.json.
"""
import ast
import base64
import gzip
import hashlib
import io
import json
from pathlib import Path
import sys
import tokenize

ROOT = Path(__file__).resolve().parent

class StripDocstrings(ast.NodeTransformer):
    def visit_Module(self, node):
        self.generic_visit(node)
        if (node.body and isinstance(node.body[0], ast.Expr)
                and isinstance(node.body[0].value, ast.Constant)
                and isinstance(node.body[0].value.value, str)):
            node.body = node.body[1:]
        return node
    visit_FunctionDef = visit_Module
    visit_AsyncFunctionDef = visit_Module
    visit_ClassDef = visit_Module

def measure(text):
    tree = StripDocstrings().visit(ast.parse(text))
    source = ast.unparse(tree) + '\n'
    excluded = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
                tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    tokens = sum(t.type not in excluded for t in tokenize.generate_tokens(io.StringIO(source).readline))
    return {
        'tokens': tokens,
        'ast_nodes': sum(1 for _ in ast.walk(tree)),
        'normalized_bytes': len(source.encode()),
        'normalized_sha256': hashlib.sha256(source.encode()).hexdigest(),
        'contains_ACCEPT': 'ACCEPT' in source,
        'contains_packing_or_exec': any(x in source for x in ('exec(', 'b85decode(', 'decompress(')),
    }

def main():
    bundle_path = ROOT / 'corpus_inputs.json.gz'
    if bundle_path.exists():
        bundle = json.loads(gzip.decompress(bundle_path.read_bytes()))
        trees = bundle['artifact_trees']
        sources = bundle['all_python_sources']
        compressed = bundle['gz_sources']
    else:
        trees = json.loads((ROOT / 'artifact_trees.json').read_text())
        sources = json.loads((ROOT / 'all_python_sources.json').read_text())
        compressed = json.loads((ROOT / 'gz_sources.json').read_text())
    all_rows, errors, git_failures = [], [], []
    for entries, is_gzip in ((sources, False), (compressed, True)):
        for sha, item in entries.items():
            raw = base64.b64decode(item['content']) if is_gzip else item['content'].encode()
            actual = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
            if actual != sha:
                git_failures.append(item['path'])
            try:
                text = gzip.decompress(raw).decode() if is_gzip else raw.decode()
                all_rows.append({'path': item['path'], 'git_blob_sha1': sha,
                                 'gzip_source': is_gzip, **measure(text)})
            except Exception as exc:
                errors.append({'path': item['path'], 'error': repr(exc)})
    (ROOT / 'corpus_measurements.json').write_text(json.dumps(all_rows, indent=2) + '\n')
    py_count = sum(x['path'].endswith('.py') for tree in trees.values() for x in tree['tree'])
    gz_count = sum(x['path'].endswith('.py.gz') for tree in trees.values() for x in tree['tree'])
    candidates = {}
    candidate_dir = Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT.parent / 'code'
    for name in ('checker_tokens239.py', 'checker_ast257.py'):
        measured = measure((candidate_dir / name).read_text())
        measured['matching_corpus_paths'] = [x['path'] for x in all_rows if x['normalized_sha256'] == measured['normalized_sha256']]
        candidates[name] = measured
    receipt = {
        'repository': 'VladimirReshetnikov/ProveIt',
        'commit': '95d3dd192e97a19bd4f8783c764331ec41126264',
        'scope': 'Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Artifacts',
        'python_version': sys.version,
        'package_trees': len(trees),
        'tree_entries': sum(len(t['tree']) for t in trees.values()),
        'python_file_occurrences': py_count,
        'gzip_python_occurrences': gz_count,
        'distinct_uncompressed_git_blobs': len(sources),
        'distinct_compressed_git_blobs': len(compressed),
        'distinct_normalized_modules': len({x['normalized_sha256'] for x in all_rows}),
        'parse_or_decode_errors': errors,
        'git_blob_mismatches': git_failures,
        'observed_compact_envelope': [240, 259, 462],
        'one_program_attains_all_coordinates': False,
        'normalization': 'Strip leading module/function/class docstrings; ast.unparse whole module plus one LF. Significant tokens exclude whitespace, comments, indentation, newline and end markers.',
        'qualified_controls': [
            'procedure_presentation/code/inherited_tokens240.py',
            'direct_packets/code/checkers/checker_ast_jsonl.py',
            'procedure_presentation/code/checker_compact462.py',
        ],
        'explicit_exclusions': [
            {'path': 'shifted_shared_leaf/negative/REJECTED_UNSOUND_shared_no_parity.py', 'reason': '460-byte deliberately unsound negative control; missing parity protection.'},
            {'path': 'shifted_shared_leaf/negative/direct_no_parity.py', 'reason': '464-byte deliberately unsound negative control.'},
            {'path': 'whole_json_refinement/negative/REJECTED_UNSOUND_no_parity.py', 'reason': '465-byte deliberately unsound negative control.'},
            {'path': 'direct_closure/code/build_strict_checkers.py', 'reason': 'Generator whose quoted checker payload is not executed as a proof-checking module.'},
            {'path': 'canonical_recursors/strict/build_family.py', 'reason': 'Generator whose quoted checker payload is not executed as a proof-checking module.'},
            {'path': 'shifted_shared_leaf/verify_negative.py', 'reason': 'Regression runner invoking other files; not a standalone proof checker.'},
            {'path': '502_scope_audit/illustrations/checker_packed.py', 'reason': 'Packed-source illustration; dependencies and decoded payload are charged separately, so raw launcher size is not comparable.'},
            {'path': '502_scope_audit/illustrations/incumbent_506_packed.py', 'reason': 'Packed-source illustration, same accounting exclusion.'},
        ],
        'candidate_novelty': candidates,
        'limits': ['Source measurement does not prove checker soundness.', 'The envelope is an observed attained record, not a mathematical lower bound.', 'Quoted generator templates and arbitrary dynamic program generation are not separately enumerated.', 'No new formal Lean/Rocq verification is implied.'],
    }
    (ROOT / 'census_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))

if __name__ == '__main__':
    main()
