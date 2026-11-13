"""Measure the pinned project in a local checkout.

Usage: python3 census.py /path/to/ProveIt/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
Writes a fresh census and CSV in the current directory. Uses only the standard library.
"""
from pathlib import Path
import ast, csv, hashlib, io, json, platform, tokenize, argparse

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('project_directory', type=Path)
args = parser.parse_args()
ROOT = Path.cwd()
BASE = args.project_directory.resolve()
if not (BASE / 'Artifacts').is_dir():
    parser.error('Expected a ConciseIPRA directory containing Artifacts/')
SKIP = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}
rows = []
for path in sorted(BASE.rglob('*.py')):
    raw = path.read_bytes()
    row = {'path': str(path.relative_to(BASE)), 'raw_bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}
    try:
        tree = ast.parse(raw)
        normal = ast.unparse(tree) + '\n'
        row.update(tokens=sum(t.type not in SKIP for t in tokenize.generate_tokens(io.StringIO(normal).readline)), ast_nodes=len(list(ast.walk(ast.parse(normal)))), normalized_bytes=len(normal.encode()), normalized_sha256=hashlib.sha256(normal.encode()).hexdigest())
        row['has_json_reader'] = any(isinstance(n, ast.Import) and any(a.name == 'json' for a in n.names) or isinstance(n, ast.ImportFrom) and n.module == 'json' for n in ast.walk(tree))
        row['has_print'] = any(isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == 'print' for n in ast.walk(tree))
        row['input_mentions'] = any(isinstance(n, ast.Name) and n.id == 'input' for n in ast.walk(tree))
        row['sys_stdin_read'] = 'sys.stdin.read' in normal or '.read()' in normal
        row['source_is_normalized'] = raw == normal.encode()
    except Exception as e:
        row['error'] = type(e).__name__ + ': ' + str(e)
    rows.append(row)
summary = {'python': platform.python_version(), 'root': str(BASE), 'commit': '12197d86f63e9ec73b2d91399c4de2a8cb0077ee', 'python_files': len(rows), 'parse_failures': sum('error' in r for r in rows), 'rows': rows}
(ROOT/'all_python_census.json').write_text(json.dumps(summary, indent=2)+'\n')
valid = [r for r in rows if 'error' not in r]
small = [r for r in valid if r['tokens'] < 350 or r['ast_nodes'] < 400 or r['normalized_bytes'] < 700]
fields = ['path','tokens','ast_nodes','normalized_bytes','has_json_reader','has_print','input_mentions','sys_stdin_read','sha256']
with (ROOT/'small_python_census.csv').open('w', newline='') as f:
    w=csv.DictWriter(f,fieldnames=fields,extrasaction='ignore'); w.writeheader(); w.writerows(small)
seen=set()
for r in sorted(small,key=lambda r:(r['tokens'],r['ast_nodes'],r['normalized_bytes'])):
    if r['has_json_reader'] and r['has_print'] and r['normalized_sha256'] not in seen:
        print(r['tokens'],r['ast_nodes'],r['normalized_bytes'],r['path'])
        seen.add(r['normalized_sha256'])
print('FILES',len(rows),'PARSE_FAILURES',summary['parse_failures'],'UNIQUE_SMALL_READER_PRINT',len(seen))
