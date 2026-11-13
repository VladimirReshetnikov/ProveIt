"""Measure complete Python modules after ast.unparse plus one newline."""
from pathlib import Path
import ast,gzip,hashlib,io,json,sys,tokenize
HERE=Path(__file__).resolve().parent

def metrics(path):
    tree=ast.parse(path.read_text())
    source=(ast.unparse(tree)+'\n').encode()
    ignored={tokenize.ENCODING,tokenize.ENDMARKER,tokenize.NEWLINE,tokenize.NL,tokenize.INDENT,tokenize.DEDENT,tokenize.COMMENT}
    return {'tokens':sum(t.type not in ignored for t in tokenize.generate_tokens(io.StringIO(source.decode()).readline)), 'ast_nodes':len(list(ast.walk(tree))),'normalized_bytes':len(source),'gzip9':len(gzip.compress(source,compresslevel=9,mtime=0)),'normalized_sha256':hashlib.sha256(source).hexdigest()}

if __name__=='__main__':
    paths=[p for folder in ['code','controls'] for p in sorted((HERE/folder).glob('*.py'))]
    result={'python':sys.version,'modules':{str(p.relative_to(HERE)):metrics(p) for p in paths}}
    print(json.dumps(result,indent=2))
