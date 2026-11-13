"""External integration: six source regions to existing checker implementations.

Not a Lean parser, TeX interpreter, or PDF semantics. Recipe checking remains
fixed-byte/manual-transcription based; mutation rejection can occur at its pin.
"""
from pathlib import Path
from contextlib import redirect_stdout
from io import StringIO
import importlib.util, json, re, runpy

ROOT=Path('research/current14-envelope-checker-integration')
def load(name,path):
    spec=importlib.util.spec_from_file_location(name,str(path)); mod=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod); return mod

envelope=load('current14_envelope','research/current14-restricted-document-envelope/envelope.py')
math=load('current14_math','research/current14-restricted-tex-prefix-extractor/extract.py')
QUOTE=Path('research/current14-seed-readable-prefix-staged-check/src/DiophantineConsistency/Current14QuotedPrefixQuote.lean').read_text()
RECIPE=Path('research/current14-printed-port-recipe-semantic-check/check.py')

def arithmetic_lines(holes):
    fragment=holes['abbreviations'].rstrip()
    if not fragment.endswith('.'):raise math.ParseError('missing declaration period')
    lines,known=math.declarations(fragment[:-1])
    eq=holes['equation']
    if not eq.endswith('=0.'):raise math.ParseError('equation right side')
    parser=math.Parser(math.lex(eq[:-3]),known); tree=parser.expr()
    if parser.peek() is not None:raise math.ParseError('trailing equation tokens')
    return lines+[['result','=']+math.prefix(tree)]

def reconstruct(holes):
    fragments=envelope.FRAGMENTS; names=envelope.NAMES
    return ''.join(fragments[i]+holes[n] for i,n in enumerate(names))+fragments[-1]

def recipe_checker(assembled):
    """Give the existing pinned checker the assembled source as its equation.tex.

    Its pins and exact texfrag test remain enforced; this intentionally rejects
    any changed page and is not a parser for alternative recipes.
    """
    original_text,original_bytes=Path.read_text,Path.read_bytes
    def read_text(p,*args,**kwargs):
        return assembled if p==Path('equation.tex') else original_text(p,*args,**kwargs)
    def read_bytes(p,*args,**kwargs):
        return assembled.encode('utf-8') if p==Path('equation.tex') else original_bytes(p,*args,**kwargs)
    out=StringIO()
    try:
        Path.read_text,Path.read_bytes=read_text,read_bytes
        with redirect_stdout(out):runpy.run_path(str(RECIPE),run_name='__main__')
    finally:
        Path.read_text,Path.read_bytes=original_text,original_bytes
    return json.loads(out.getvalue())

def evaluate(document):
    """Feed extracted math holes directly, and reassembled holes to the recipe checker."""
    holes=envelope.extract(document)
    if holes is None:raise ValueError('envelope rejected')
    lines=arithmetic_lines(holes)
    if lines!=math.lean_quote(QUOTE):raise ValueError('arithmetic does not match staged quote')
    recipe=recipe_checker(reconstruct(holes))
    seed_digits=''.join(re.findall(r'(\d+)\\par',holes['decimal_seed']))
    if len(seed_digits)!=recipe['seed_decimal_digits']:raise ValueError('seed length mismatch')
    return {'holes':holes,'line_count':len(lines),'recipe':recipe}
