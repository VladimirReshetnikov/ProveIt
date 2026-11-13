from pathlib import Path
import ast, gzip, hashlib, io, json, sys, tokenize, zipfile

import argparse
parser = argparse.ArgumentParser(description='Statically census the pinned ConciseIPRA source tree and archives.')
parser.add_argument('--repository', type=Path, required=True)
parser.add_argument('--output', type=Path, default=Path('census-rerun'))
args = parser.parse_args()
ROOT = args.repository / 'Logic/PrimitiveRecursiveArithmetic/ConciseIPRA'
OUT = args.output
OUT.mkdir(parents=True, exist_ok=True)
if not ROOT.is_dir():
    parser.error('The repository does not contain the ConciseIPRA directory')
IGNORE = {tokenize.ENCODING, tokenize.NL, tokenize.NEWLINE, tokenize.INDENT,
          tokenize.DEDENT, tokenize.ENDMARKER, tokenize.COMMENT}
rows = []
errors = []

def record(path, payload):
    try:
        source = payload.decode('utf-8-sig')
        tree = ast.parse(source)
        normal = ast.unparse(tree) + '\n'
        data = normal.encode()
        imports = sorted({n.module for n in ast.walk(tree) if isinstance(n, ast.ImportFrom)} |
                         {a.name for n in ast.walk(tree) if isinstance(n, ast.Import) for a in n.names})
        calls = sorted({n.func.id for n in ast.walk(tree)
                        if isinstance(n, ast.Call) and isinstance(n.func, ast.Name)})
        row = {
            'path': path, 'tokens': sum(t.type not in IGNORE for t in tokenize.generate_tokens(io.StringIO(normal).readline)),
            'ast': sum(1 for _ in ast.walk(tree)), 'bytes': len(data),
            'gzip9': len(gzip.compress(data, compresslevel=9, mtime=0)),
            'sha256': hashlib.sha256(data).hexdigest(), 'imports': imports,
            'dangerous_calls': [v for v in calls if v in ('eval', 'exec', 'compile', '__import__')],
            'accept_string': any(isinstance(n, ast.Constant) and isinstance(n.value, str) and n.value == 'ACCEPT' for n in ast.walk(tree)),
            'reads_input': any(v in calls for v in ('input', 'open')) or 'stdin' in normal,
            'source': source,
        }
        row['candidate'] = (row['accept_string'] and row['reads_input'] and not row['dangerous_calls']
                            and set(imports) <= {'json', 'sys', 're', 'builtins'})
        row['framing'] = 'jsonl' if 'input()' in normal else 'json'
        rows.append(row)
    except Exception as e:
        errors.append({'path': path, 'error': repr(e)})

def archive(path, data, depth=0):
    try:
        with zipfile.ZipFile(io.BytesIO(data)) as z:
            for f in z.infolist():
                name = f.filename
                if f.is_dir():
                    continue
                if name.endswith('.py'):
                    record(path + '!' + name, z.read(f))
                elif name.endswith('.gz'):
                    record(path + '!' + name, gzip.decompress(z.read(f)))
                elif name.endswith('.zip') and depth < 4:
                    archive(path + '!' + name, z.read(f), depth + 1)
    except Exception as e:
        errors.append({'path':path, 'error':repr(e)})

for p in ROOT.rglob('*'):
    if not p.is_file():
        continue
    name = str(p)
    if name.endswith('.py'):
        record(name, p.read_bytes())
    elif name.endswith('.gz'):
        try:
            record(name, gzip.decompress(p.read_bytes()))
        except Exception as e:
            errors.append({'path':name,'error':repr(e)})
    elif name.endswith('.zip'):
        archive(name, p.read_bytes())

unique = {}
for row in rows:
    key = row['sha256']
    if key not in unique:
        unique[key] = dict(row, paths=[])
    unique[key]['paths'].append(row['path'])
items = list(unique.values())
for row in rows:
    row.pop('source', None)
(OUT/'census_all.json').write_text(json.dumps({'rows':rows, 'errors':errors}, indent=2))
(OUT/'unique_candidates.json').write_text(json.dumps([r for r in items if r['candidate']], indent=2))
print(json.dumps({'sources':len(rows), 'unique':len(items), 'candidates':sum(r['candidate'] for r in items),
                  'errors':errors[:10], 'python':sys.version},indent=2))
for metric in ('tokens','ast','bytes'):
    print(metric)
    for row in sorted((r for r in items if r['candidate']),key=lambda x:x[metric])[:15]:
        print(row['tokens'],row['ast'],row['bytes'],row['gzip9'],row['framing'],row['path'])
