"""Complete-checker source measurements with the repository convention."""
import ast
import gzip
import io
import json
import pathlib
import platform
import tokenize

ROOT=pathlib.Path(__file__).resolve().parent


def measure(path):
    tree=ast.parse(path.read_text())
    if (tree.body and isinstance(tree.body[0],ast.Expr)
        and isinstance(tree.body[0].value,ast.Constant)
        and isinstance(tree.body[0].value.value,str)):
        tree.body.pop(0)
    normalized=ast.unparse(tree)+'\n'
    significant=sum(t.type not in (tokenize.ENCODING,tokenize.ENDMARKER,tokenize.NEWLINE,
        tokenize.NL,tokenize.INDENT,tokenize.DEDENT,tokenize.COMMENT)
        for t in tokenize.generate_tokens(io.StringIO(normalized).readline))
    return {'normalized_bytes':len(normalized.encode()),'tokens':significant,
            'ast_nodes':len(list(ast.walk(ast.parse(normalized)))),
            'gzip9_bytes':len(gzip.compress(normalized.encode(),compresslevel=9,mtime=0))}


def run():
    names=['raw_control.py','matched_raw_control.py','raw_two_case.py',
           'normal_with_root.py','checker.py','reference/native_normal.py']
    if (ROOT/'zero_base.py').exists():names.append('zero_base.py')
    report={'python':platform.python_version(),'normalization':'Remove module docstring; ast.unparse(ast.parse(source)) plus one LF.',
            'results':{name:measure(ROOT/name) for name in names}}
    (ROOT/'metrics.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':run()
