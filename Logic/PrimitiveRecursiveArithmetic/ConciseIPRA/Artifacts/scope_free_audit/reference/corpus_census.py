import ast
import argparse
import gzip
import hashlib
import io
import json
from pathlib import Path
import tokenize
import zipfile

parser = argparse.ArgumentParser(description='Static census of a pinned ConciseIPRA checkout.')
parser.add_argument('project', type=Path)
parser.add_argument('--output', type=Path, default=Path('census_reproduced.json'))
args = parser.parse_args()
ROOT = args.project
OUT = args.output.parent
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
        tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}

class StripDocstrings(ast.NodeTransformer):
    def body(self, node):
        self.generic_visit(node)
        if node.body and isinstance(node.body[0], ast.Expr):
            v = node.body[0].value
            if isinstance(v, ast.Constant) and isinstance(v.value, str):
                node.body.pop(0)
        return node
    visit_Module = body
    visit_FunctionDef = body
    visit_AsyncFunctionDef = body
    visit_ClassDef = body

rows, errors, archives = [], [], []
seen_zip = set()

def visit(name, data, depth=0):
    if name.endswith('.zip') and depth < 8:
        digest = hashlib.sha256(data).hexdigest()
        archives.append({'path': name, 'sha256': digest, 'bytes': len(data)})
        if digest in seen_zip:
            return
        seen_zip.add(digest)
        try:
            with zipfile.ZipFile(io.BytesIO(data)) as z:
                for info in z.infolist():
                    if not info.is_dir():
                        visit(name+'!'+info.filename, z.read(info), depth+1)
        except Exception as e:
            errors.append({'path': name, 'error': repr(e)})
        return
    if name.endswith('.py.gz'):
        try:
            data = gzip.decompress(data)
        except Exception as e:
            errors.append({'path': name, 'error': repr(e)})
            return
    elif not name.endswith('.py'):
        return
    try:
        tree = StripDocstrings().visit(ast.parse(data))
        normalized = ast.unparse(tree)+'\n'
        print_accept = any(isinstance(n, ast.Call) and isinstance(n.func, ast.Name)
            and n.func.id=='print' and any(isinstance(a,ast.Constant) and a.value=='ACCEPT'
                for a in n.args) for n in ast.walk(tree))
        rows.append({'path': name, 'tokens': sum(t.type not in SKIP for t in
                tokenize.generate_tokens(io.StringIO(normalized).readline)),
            'ast_nodes': sum(1 for _ in ast.walk(tree)),
            'normalized_bytes': len(normalized.encode()),
            'raw_sha256': hashlib.sha256(data).hexdigest(),
            'normalized_sha256': hashlib.sha256(normalized.encode()).hexdigest(),
            'print_accept': print_accept})
    except Exception as e:
        errors.append({'path': name, 'error': repr(e)})

for p in sorted(ROOT.rglob('*')):
    if p.is_file() and p.name.endswith(('.py','.py.gz','.zip')):
        visit(str(p.relative_to(ROOT)), p.read_bytes())
result = {'root': str(ROOT), 'rows': rows, 'errors': errors, 'archives': archives,
          'note': 'Static source measurement only. ACCEPT screen is not soundness or completeness verification.'}
OUT.mkdir(parents=True, exist_ok=True)
args.output.write_text(json.dumps(result, indent=2)+'\n')
print('occurrences',len(rows),'distinct_raw',len({r['raw_sha256'] for r in rows}),
      'distinct_normalized',len({r['normalized_sha256'] for r in rows}),
      'archives',len(archives),'errors',len(errors))
for key in ('tokens','ast_nodes','normalized_bytes'):
    seen=set()
    print('\nSTATIC ACCEPT SCREEN BY',key)
    count=0
    for r in sorted((r for r in rows if r['print_accept']),key=lambda r:r[key]):
        if r['normalized_sha256'] in seen: continue
        seen.add(r['normalized_sha256'])
        print(r['tokens'],r['ast_nodes'],r['normalized_bytes'],r['path'])
        count+=1
        if count==20:break
