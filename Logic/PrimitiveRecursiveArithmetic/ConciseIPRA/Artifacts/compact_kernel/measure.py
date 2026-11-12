"""Measure complete modules by the unchanged corpus convention."""
import ast,gzip,hashlib,io,json,platform,tokenize,zlib
from pathlib import Path
ROOT=Path(__file__).resolve().parent
IGNORE={tokenize.ENCODING,tokenize.COMMENT,tokenize.NL,tokenize.NEWLINE,tokenize.INDENT,tokenize.DEDENT,tokenize.ENDMARKER}
class Strip(ast.NodeTransformer):
    def clean(self,node):
        self.generic_visit(node)
        if node.body and isinstance(node.body[0],ast.Expr) and isinstance(node.body[0].value,ast.Constant) and isinstance(node.body[0].value.value,str):
            node.body=node.body[1:]
        return node
    visit_Module=clean
    visit_FunctionDef=clean
    visit_AsyncFunctionDef=clean
    visit_ClassDef=clean

def metrics(path):
    raw=path.read_bytes()
    tree=ast.fix_missing_locations(Strip().visit(ast.parse(raw)))
    data=(ast.unparse(tree)+'\n').encode()
    return dict(file=str(path.relative_to(ROOT)),normalized_tokens=sum(t.type not in IGNORE for t in tokenize.generate_tokens(io.StringIO(data.decode()).readline)),ast_nodes=sum(1 for _ in ast.walk(tree)),normalized_bytes=len(data),raw_bytes=len(raw),gzip9_raw_bytes=len(gzip.compress(raw,compresslevel=9,mtime=0)),gzip9_normalized_bytes=len(gzip.compress(data,compresslevel=9,mtime=0)),sha256=hashlib.sha256(raw).hexdigest())

def collect():
    names=['code/checker.py','code/readable_checker.py','ancillary/checker_bytes.py','ancillary/checker_ast.py','ancillary/checker_ast_loop.py','reference/arity_original.py','reference/arity_bytes_original.py','reference/arity_ast_original.py','reference/uniform_original.py','reference/byte_frontier.py','reference/ast_frontier.py','reference/token_frontier.py']
    return dict(python=platform.python_version(),zlib=zlib.ZLIB_RUNTIME_VERSION,programs=[metrics(ROOT/n) for n in names],scope='Entire modules; shared Python/JSON runtime excluded under the inherited convention; gzip9 is FYI.')

if __name__=='__main__':
    data=collect()
    (ROOT/'evidence/measurements.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(data,indent=2))
