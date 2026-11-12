"""Reproduce complete-source sizes. Gzip level 9 is an FYI, not a target."""
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import platform
import subprocess
import tokenize
import zlib

ROOT=Path(__file__).resolve().parent
FILES=[
 ('Incumbent byte profile','reference/incumbent_bytes.py'),
 ('Incumbent AST profile','reference/minimum_ast.py'),
 ('Combined old-table control','reference/old_table_matched.py'),
 ('Affine before integer spelling','reference/affine_plus.py'),
 ('Selected affine checker','code/checker.py'),
 ('Plain old-table control','reference/old_table_plain.py'),
 ('Plain affine implementation','code/matched_checker.py'),
 ('Readable affine implementation','code/readable_checker.py'),
 ('Incidental token profile','code/incidental_tokens.py'),
 ('Incidental AST profile','code/incidental_ast.py'),
]

class StripDocstrings(ast.NodeTransformer):
    def visit_FunctionDef(self,node):return self.strip(self.generic_visit(node))
    def visit_AsyncFunctionDef(self,node):return self.strip(self.generic_visit(node))
    def visit_ClassDef(self,node):return self.strip(self.generic_visit(node))
    def visit_Module(self,node):return self.strip(self.generic_visit(node))
    @staticmethod
    def strip(node):
        if node.body and isinstance(node.body[0],ast.Expr) and isinstance(node.body[0].value,ast.Constant) and isinstance(node.body[0].value.value,str):
            node.body.pop(0)
        return node

def main():
    rows=[]
    for label,name in FILES:
        path=ROOT/name;source=path.read_bytes()
        tree=StripDocstrings().visit(ast.parse(source))
        normalized=(ast.unparse(tree)+'\n').encode()
        compressed=gzip.compress(source,compresslevel=9,mtime=0)
        (ROOT/(name+'.gz')).write_bytes(compressed)
        try:
            external = subprocess.run(['gzip', '-9', '-n', '-c', str(path)], check=True, capture_output=True).stdout
        except FileNotFoundError:
            external = None
        if external is not None and external != compressed:
            raise RuntimeError('Python/GNU gzip bytes differ for ' + name)
        ignored=(tokenize.ENDMARKER,tokenize.ENCODING,tokenize.NL,tokenize.NEWLINE,tokenize.INDENT,tokenize.DEDENT,tokenize.COMMENT)
        tokens=sum(t.type not in ignored for t in tokenize.generate_tokens(io.StringIO(normalized.decode()).readline))
        rows.append(dict(label=label,file=name,sha256=hashlib.sha256(source).hexdigest(),source_bytes=len(source),normalized_tokens=tokens,ast_nodes=sum(1 for _ in ast.walk(tree)),normalized_bytes=len(normalized),gzip9_source_bytes=len(compressed),gzip9_normalized_bytes=len(gzip.compress(normalized,compresslevel=9,mtime=0))))
    receipt=dict(python=platform.python_version(),implementation=platform.python_implementation(),zlib=zlib.ZLIB_VERSION,normalization='Strip comments and actual docstrings; ast.unparse plus one newline; whole standalone module',gzip='gzip.compress(source,compresslevel=9,mtime=0), equivalent size to gzip -n -9 -c in the reference environment',gzip_is_optimization_objective=False,profiles=rows)
    (ROOT/'evidence/implementation_metrics.json').write_text(json.dumps(receipt,indent=2)+'\n')
    selected=next(r for r in rows if r['file']=='code/checker.py')
    macros={'NewTokens':selected['normalized_tokens'],'NewAST':selected['ast_nodes'],'NewBytes':selected['normalized_bytes'],'NewGzip':selected['gzip9_source_bytes']}
    (ROOT/'evidence/metrics_macros.tex').write_text(''.join('\\newcommand{\\'+k+'}{'+str(v)+'}\n' for k,v in macros.items()))
    heading='\\begin{center}\\small\n\\begin{tabular}{lrrrr}\n\\toprule\nWhole standalone source & Tokens & AST & Bytes & Gzip 9\\\\\n\\midrule\n'
    lines=[]
    for r in rows:
        lines.append(f"{r['label']} &{r['normalized_tokens']}&{r['ast_nodes']}&{r['normalized_bytes']}&{r['gzip9_source_bytes']}\\\\\n")
    (ROOT/'evidence/controlled_comparison.tex').write_text(heading+''.join(lines)+'\\bottomrule\n\\end{tabular}\n\\end{center}\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
