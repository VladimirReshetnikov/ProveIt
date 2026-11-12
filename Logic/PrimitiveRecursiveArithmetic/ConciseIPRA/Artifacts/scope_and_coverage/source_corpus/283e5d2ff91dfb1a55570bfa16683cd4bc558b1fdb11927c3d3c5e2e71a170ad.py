"""Whole-program measurements; gzip-9 is informational, not an objective."""
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import platform
import sys
import tokenize
import zlib

ROOT = Path(__file__).resolve().parent
IGNORED = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE,
           tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}

class StripDocstrings(ast.NodeTransformer):
    def clean(self, node):
        self.generic_visit(node)
        if (node.body and isinstance(node.body[0], ast.Expr)
                and isinstance(node.body[0].value, ast.Constant)
                and isinstance(node.body[0].value.value, str)):
            node.body = node.body[1:]
        return node
    visit_Module = clean
    visit_FunctionDef = clean
    visit_AsyncFunctionDef = clean
    visit_ClassDef = clean

def normalized(raw):
    tree = ast.fix_missing_locations(StripDocstrings().visit(ast.parse(raw.decode('utf-8'))))
    return tree, (ast.unparse(tree) + '\n').encode('utf-8')

def metrics(raw):
    tree, data = normalized(raw)
    return {
        'normalized_tokens': sum(t.type not in IGNORED for t in tokenize.generate_tokens(io.StringIO(data.decode()).readline)),
        'ast_nodes': sum(1 for _ in ast.walk(tree)),
        'normalized_bytes': len(data), 'raw_bytes': len(raw),
        'gzip9_raw_bytes': len(gzip.compress(raw, compresslevel=9, mtime=0)),
        'gzip9_normalized_bytes': len(gzip.compress(data, compresslevel=9, mtime=0)),
        'sha256': hashlib.sha256(raw).hexdigest(),
    }

def exit_status_control(raw):
    tree = ast.parse(raw.decode())
    matches = [n for n in tree.body if isinstance(n, ast.Try)]
    if len(matches) != 1:
        raise ValueError('Expected one top-level rejection wrapper')
    node = matches[0]
    if node.orelse or node.finalbody or len(node.handlers) != 1:
        raise ValueError('Unexpected rejection wrapper')
    handler = node.handlers[0]
    expected = ast.parse("print('REJECT')\nraise\n").body
    if handler.type is not None or ast.dump(ast.Module(handler.body, [])) != ast.dump(ast.Module(expected, [])):
        raise ValueError('Only a print-and-reraise handler may be removed')
    index = tree.body.index(node)
    tree.body[index:index+1] = node.body
    return (ast.unparse(tree) + '\n').encode()

PROGRAMS = [
    ('Current token leader', 'reference/baseline_tokens.py'),
    ('Current AST leader', 'reference/baseline_structure.py'),
    ('Current byte leader', 'reference/baseline_bytes.py'),
    ('Current flat computation', 'reference/baseline_flat.py'),
    ('Current predecessor joint', 'reference/baseline_joint.py'),
    ('New predecessor, two verdicts', 'reference/predecessor_two_verdicts.py'),
    ('Selected complete checker', 'code/checker.py'),
    ('Readable complete checker', 'code/readable_checker.py'),
    ('Ancillary byte profile', 'ancillary/checker_bytes.py'),
    ('Ancillary AST profile', 'ancillary/checker_ast.py'),
]

def collect(write=False):
    rows = [dict(label=label, file=name, **metrics((ROOT/name).read_bytes())) for label,name in PROGRAMS]
    matched=[]
    for label,name in PROGRAMS[:5]:
        data=exit_status_control((ROOT/name).read_bytes())
        relative='reference/matched/'+Path(name).name
        matched.append(dict(label=label+' (matched driver)', file=relative, **metrics(data)))
        if write:
            path=ROOT/relative;path.parent.mkdir(exist_ok=True);path.write_bytes(data)
        elif (ROOT/relative).read_bytes()!=data:
            raise ValueError('Changed matched control: '+relative)
    result={'python':platform.python_version(), 'implementation':platform.python_implementation(),
            'zlib_runtime':zlib.ZLIB_RUNTIME_VERSION,
            'gzip':'gzip.compress(raw,compresslevel=9,mtime=0); full header and trailer counted',
            'current_corpus_envelope':{'normalized_tokens':277,'ast_nodes':311,'normalized_bytes':672},
            'programs':rows, 'matched_driver_controls':matched}
    if write:
        (ROOT/'evidence/checker_metrics.json').write_text(json.dumps(result,indent=2)+'\n')
        selected=next(r for r in rows if r['file']=='code/checker.py')
        macros='\n'.join('\\newcommand{\\'+k+'}{'+str(selected[v])+'}' for k,v in [
            ('PrimaryTokens','normalized_tokens'),('PrimaryAST','ast_nodes'),('PrimaryBytes','normalized_bytes'),('PrimaryGzip','gzip9_raw_bytes')])+'\n'
        (ROOT/'evidence/metrics_macros.tex').write_text(macros)
        def table(items):
            lines=['\\begin{center}\\small','\\begin{tabular}{lrrrr}','\\toprule',
                   'Complete program & Tokens & AST & Bytes & Gzip-9\\\\','\\midrule']
            lines += [f"{r['label']} & {r['normalized_tokens']} & {r['ast_nodes']} & {r['normalized_bytes']} & {r['gzip9_raw_bytes']}\\\\" for r in items]
            lines+=['\\bottomrule','\\end{tabular}','\\end{center}']
            return '\n'.join(lines)
        (ROOT/'evidence/metrics_table.tex').write_text(table(rows)+'\n\nThe same rejection convention applied to the old programs gives:\n\n'+table(matched)+'\n')
        for name in ['code/checker.py','code/readable_checker.py','ancillary/checker_bytes.py','ancillary/checker_ast.py']:
            path=ROOT/name;path.with_suffix('.py.gz').write_bytes(gzip.compress(path.read_bytes(),compresslevel=9,mtime=0))
    return result

if __name__ == '__main__':
    print(json.dumps(collect('--write' in sys.argv),indent=2))
