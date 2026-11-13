"""Measure every delivered standalone checker and the pinned controls."""
from pathlib import Path
import ast, gzip, hashlib, io, json, sys, tokenize

ROOT=Path(__file__).resolve().parent
SKIP={tokenize.ENCODING,tokenize.ENDMARKER,tokenize.NEWLINE,tokenize.NL,
      tokenize.INDENT,tokenize.DEDENT,tokenize.COMMENT}

def measure(path):
    text=ast.unparse(ast.parse(path.read_text()))+'\n'
    return {'file':str(path.relative_to(ROOT)),
            'tokens':sum(t.type not in SKIP for t in tokenize.generate_tokens(io.StringIO(text).readline)),
            'ast_nodes':len(list(ast.walk(ast.parse(text)))),
            'normalized_bytes':len(text.encode()),
            'gzip9':len(gzip.compress(text.encode(),compresslevel=9,mtime=0)),
            'normalized_sha256':hashlib.sha256(text.encode()).hexdigest()}

if __name__=='__main__':
    paths=sorted((ROOT/'code').glob('checker*.py'))+sorted((ROOT/'reference/controls').glob('*.py'))
    print(json.dumps({'python':sys.version,'measurements':[measure(p) for p in paths]},indent=2))
