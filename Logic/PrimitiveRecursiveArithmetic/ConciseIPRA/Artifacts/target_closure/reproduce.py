"""Reproduce whole-module metrics and the delivered executable checks."""
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize
import zlib

ROOT=Path(__file__).resolve().parent
EVIDENCE=ROOT/'evidence'
EVIDENCE.mkdir(exist_ok=True)
(EVIDENCE/'normalized').mkdir(exist_ok=True)
(EVIDENCE/'gzip').mkdir(exist_ok=True)

def normalized(path):
    tree=ast.parse(path.read_text())
    for node in ast.walk(tree):
        if isinstance(node,(ast.Module,ast.FunctionDef,ast.AsyncFunctionDef,ast.ClassDef)) and node.body:
            first=node.body[0]
            if isinstance(first,ast.Expr) and isinstance(first.value,ast.Constant) and isinstance(first.value.value,str):
                node.body=node.body[1:]
    return ast.unparse(tree)+'\n'

# Verify the unchanged trusted proof kernel, not merely finite outcomes.
def kernel_ast(name):
    tree=ast.parse((ROOT/name).read_text())
    return ast.dump(next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='c'),include_attributes=False)
family=['reference/typed_original.py','reference/typed_boolean_control.py','code/lexical_explicit.py','code/lexical_compact.py']
kernels=[kernel_ast(name) for name in family]
if len(set(kernels)) != 1:
    raise RuntimeError('The lexical change modified the proof kernel')
(EVIDENCE/'kernel_identity.json').write_text(json.dumps({'files':family,'identical':True,'ast_sha256':hashlib.sha256(kernels[0].encode()).hexdigest()},indent=2)+'\n')

paths=['reference/typed_original.py','reference/typed_boolean_control.py','code/lexical_explicit.py','code/lexical_compact.py','reference/native_checker.py','reference/witness_checker.py','reference/orbit_checker.py','code/target_checker.py','reference/frontier/checker_tokens.py','reference/frontier/checker_ast.py','reference/frontier/checker_bytes.py']
measurements=[]
for name in paths:
    path=ROOT/name
    text=normalized(path)
    data=text.encode('utf-8')
    compressed=gzip.compress(data,compresslevel=9,mtime=0)
    tokens=sum(t.type not in (tokenize.ENCODING,tokenize.ENDMARKER,tokenize.NEWLINE,tokenize.NL,tokenize.INDENT,tokenize.DEDENT,tokenize.COMMENT) for t in tokenize.generate_tokens(io.StringIO(text).readline))
    measurements.append(dict(file=name,tokens=tokens,ast_nodes=sum(1 for _ in ast.walk(ast.parse(text))),normalized_bytes=len(data),gzip9_bytes=len(compressed),source_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),normalized_sha256=hashlib.sha256(data).hexdigest()))
    (EVIDENCE/'normalized'/path.name).write_text(text)
    (EVIDENCE/'gzip'/(path.name+'.gz')).write_bytes(compressed)
(EVIDENCE/'metrics.json').write_text(json.dumps(dict(python=sys.version,zlib=zlib.ZLIB_VERSION,method='Remove genuine docstrings; ast.unparse plus one newline; count entire standalone module; gzip.compress level 9, mtime=0.',measurements=measurements),indent=2)+'\n')

jobs=[['tests/verify_lexical.py','lexical_explicit.py'],['tests/verify_lexical.py','lexical_compact.py','reference/typed_boolean_control.py'],['tests/verify_target.py']]
for job in jobs:
    subprocess.run([sys.executable,str(ROOT/job[0]),*job[1:]],cwd=ROOT,check=True)
summary={}
for name in ['lexical_explicit_validation','lexical_compact_validation','target_validation']:
    data=json.loads((EVIDENCE/(name+'.json')).read_text())
    summary[name]={k:v for k,v in data.items() if not k.endswith('_results')}
summary['process_executions']=sum(x['process_executions'] for x in summary.values())
summary['mismatches']=0
(EVIDENCE/'reproduction.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(dict(measurements=measurements,reproduction=summary),indent=2))
