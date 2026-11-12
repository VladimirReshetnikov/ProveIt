"""Read-only pinned-source census. Never imports or executes downloaded code."""
from pathlib import Path
import ast
import concurrent.futures
import hashlib
import io
import json
import platform
import tokenize
import urllib.error
import urllib.request

ROOT = Path(__file__).resolve().parent
WORK = ROOT.parents[1]
PIN = '42fba2a76aea6eb41a8c4acfe7761620f58956ee'
PREFIX = 'Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Research/'
BASE = 'https://raw.githubusercontent.com/VladimirReshetnikov/ProveIt/' + PIN + '/' + PREFIX
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
        tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
EXCLUDED_PARTS = {'source_corpus', 'reference', 'references', 'ref', 'refs',
                  'vendor', 'tests', 'test', 'controls', 'control', 'baseline',
                  'baselines', 'frozen', 'examples', 'certificates', 'fixtures',
                  'validation'}


class RemoveDocstrings(ast.NodeTransformer):
    def clean(self, node):
        self.generic_visit(node)
        if node.body and isinstance(node.body[0], ast.Expr):
            v = node.body[0].value
            if isinstance(v, ast.Constant) and isinstance(v.value, str):
                node.body = node.body[1:]
        return node
    visit_Module = clean
    visit_FunctionDef = clean
    visit_AsyncFunctionDef = clean
    visit_ClassDef = clean


def git_blob_hash(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def preferred(path):
    return not (set(Path(path).parts[:-1]) & EXCLUDED_PARTS)


def fetch_and_measure(item):
    sha, entries = item
    paths = sorted(e['path'] for e in entries)
    canonical = min(paths, key=lambda p: (not preferred(p), len(p), p))
    local = ROOT / 'blobs' / (sha + '.py')
    row = {'git_blob_sha': sha, 'repository_paths': paths,
           'canonical_path': canonical, 'source_url': BASE + canonical,
           'raw_size_expected': entries[0]['size'],
           'has_nonreference_occurrence': any(preferred(p) for p in paths)}
    try:
        if local.is_file():
            data = local.read_bytes()
        else:
            for attempt in range(3):
                try:
                    with urllib.request.urlopen(BASE + canonical, timeout=30) as response:
                        data = response.read()
                    break
                except (urllib.error.URLError, TimeoutError, OSError):
                    if attempt == 2:
                        raise
            local.write_bytes(data)
        actual = git_blob_hash(data)
        if actual != sha:
            raise ValueError('Git blob mismatch: ' + actual)
        row['git_blob_verified'] = True
        row['raw_bytes'] = len(data)
        row['sha256'] = hashlib.sha256(data).hexdigest()
        tree = ast.parse(data)
        tree = RemoveDocstrings().visit(tree)
        normalized = ast.unparse(tree) + '\n'
        ntree = ast.parse(normalized)
        row['significant_tokens'] = sum(t.type not in SKIP for t in
            tokenize.generate_tokens(io.StringIO(normalized).readline))
        row['ast_nodes'] = sum(1 for _ in ast.walk(ntree))
        row['normalized_bytes'] = len(normalized.encode())
        row['normalized_sha256'] = hashlib.sha256(normalized.encode()).hexdigest()
        row['imports'] = sorted(set(
            (n.module or '') if isinstance(n, ast.ImportFrom) else a.name
            for n in ast.walk(ntree) if isinstance(n, (ast.Import, ast.ImportFrom))
            for a in (n.names if isinstance(n, ast.Import) else [None])))
        row['contains_accept_marker'] = any(isinstance(n, ast.Constant)
            and isinstance(n.value, str) and n.value == 'ACCEPT'
            for n in ast.walk(ntree))
        row['contains_print_call'] = any(isinstance(n, ast.Call)
            and isinstance(n.func, ast.Name) and n.func.id == 'print'
            for n in ast.walk(ntree))
        row['contains_json_import'] = 'json' in row['imports']
        row['possible_complete_acceptance_module'] = (row['contains_accept_marker']
            and row['contains_json_import'] and row['contains_print_call'])
        (ROOT / 'normalized' / (sha + '.py')).write_text(normalized)
    except Exception as error:
        row['error'] = type(error).__name__ + ': ' + str(error)
    return row


def main():
    metadata = ROOT / 'research_metadata.json'
    if not metadata.is_file():
        metadata = WORK / 'baseline/tree_research.json'
    tree = json.loads(metadata.read_text())
    py = [e for e in tree['tree'] if e['type'] == 'blob' and e['path'].endswith('.py')]
    small = py
    bysha = {}
    for e in small:
        bysha.setdefault(e['sha'], []).append(e)
    for sub in ['blobs', 'normalized']:
        (ROOT / sub).mkdir(parents=True, exist_ok=True)
    rows = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=16) as pool:
        for row in pool.map(fetch_and_measure, sorted(bysha.items())):
            rows.append(row)
            if len(rows) % 250 == 0:
                print(json.dumps({'completed': len(rows), 'total': len(bysha)}), flush=True)
    candidates = [r for r in rows if r.get('possible_complete_acceptance_module')]
    candidates.sort(key=lambda r: (r['normalized_bytes'], r['significant_tokens'], r['ast_nodes']))
    result = {
        'repository': 'VladimirReshetnikov/ProveIt', 'pin': PIN,
        'scope': 'Every Python file in the complete pinned Research subtree, with no raw-size cutoff and including reference/control copies; deduplicated by Git blob SHA. Static AST analysis only; downloaded programs were not run.',
        'tree_sha': tree['sha'], 'tree_truncated': tree['truncated'],
        'python': platform.python_version(),
        'python_paths_total': len(py), 'python_unique_blobs_total': len(set(e['sha'] for e in py)),
        'selected_paths': len(small), 'selected_unique_blobs': len(bysha),
        'retrieved_and_measured': sum('error' not in r for r in rows),
        'errors': [r for r in rows if 'error' in r],
        'possible_complete_acceptance_modules': len(candidates),
        'candidate_coordinate_minima': {k: min(r[k] for r in candidates)
            for k in ['significant_tokens', 'ast_nodes', 'normalized_bytes']},
        'notes': ['Candidate classification is a static triage heuristic, not a semantic certification.',
                  'No raw-size cutoff is used; each Python blob is parsed after its Git identity is checked.',
                  'docs/incoming is outside this Research subtree and is audited separately.',
                  'Coordinate minima can be attained by different programs and are not a lower-bound theorem.'],
        'candidates': candidates, 'rows': rows}
    (ROOT / 'census.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ['selected_unique_blobs', 'retrieved_and_measured',
        'possible_complete_acceptance_modules', 'candidate_coordinate_minima']}))


if __name__ == '__main__':
    main()
