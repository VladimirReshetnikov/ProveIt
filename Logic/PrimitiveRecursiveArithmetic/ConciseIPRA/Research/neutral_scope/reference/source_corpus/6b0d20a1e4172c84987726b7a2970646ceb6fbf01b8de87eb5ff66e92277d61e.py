"""Read-only audit of complete compact standalone kernels in the pinned corpus."""
import ast
import hashlib
import io
import json
import pathlib
import platform
import tokenize

ROOT = pathlib.Path(__file__).resolve().parents[1]
SKIP = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE,
        tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}

class Strip(ast.NodeTransformer):
    def visit_Module(self, node):
        return self.strip(node)
    def visit_FunctionDef(self, node):
        return self.strip(node)
    def visit_AsyncFunctionDef(self, node):
        return self.strip(node)
    def visit_ClassDef(self, node):
        return self.strip(node)
    def strip(self, node):
        self.generic_visit(node)
        if (node.body and isinstance(node.body[0], ast.Expr)
                and isinstance(node.body[0].value, ast.Constant)
                and isinstance(node.body[0].value.value, str)):
            node.body.pop(0)
        return node

def measure(path):
    raw = path.read_bytes()
    tree = ast.fix_missing_locations(Strip().visit(ast.parse(raw)))
    text = ast.unparse(tree) + '\n'
    return {'file': str(path.relative_to(ROOT)),
            'sha256': hashlib.sha256(raw).hexdigest(),
            'normalized_sha256': hashlib.sha256(text.encode()).hexdigest(),
            'normalized_tokens': sum(x.type not in SKIP for x in tokenize.generate_tokens(io.StringIO(text).readline)),
            'ast_nodes': sum(1 for _ in ast.walk(tree)),
            'normalized_bytes': len(text.encode())}

def main():
    programs=[]
    scanned=0
    for path in sorted((ROOT / 'baseline_texts').rglob('*.py')):
        scanned += 1
        source=path.read_text()
        if 'json.load(open(0))' not in source or 'ACCEPT' not in source or 'REJECT' not in source:
            continue
        programs.append(measure(path))
    keys=['normalized_tokens','ast_nodes','normalized_bytes']
    envelope={k:min(p[k] for p in programs) for k in keys}
    attainers={k:[p for p in programs if p[k]==envelope[k]] for k in keys}
    result={'python':platform.python_version(),'scanned_python_files':scanned,
            'scope':'Standalone compact modules with JSON stdin and ACCEPT/REJECT interface; full sources measured, not executed.',
            'programs_selected':len(programs),'distinct_normalized_sources':len(set(p['normalized_sha256'] for p in programs)),
            'envelope':envelope,'attainers':attainers,'programs':programs}
    output=ROOT/'logic_candidate'/'kernel_audit.json'
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in {'programs','attainers'}},indent=2))
    for key,values in attainers.items():
        print(key)
        seen=set()
        for p in values:
            if p['sha256'] not in seen:
                print(' ',p['file'],p['normalized_tokens'],p['ast_nodes'],p['normalized_bytes'])
                seen.add(p['sha256'])

if __name__=='__main__':
    main()
