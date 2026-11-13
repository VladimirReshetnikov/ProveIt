"""Offline reproduction of metrics, translations, and focused CLI checks."""
import ast
import concurrent.futures
import gzip
import hashlib
import io
import json
from pathlib import Path
import platform
import subprocess
import sys
import tokenize

from translate import odd, shared

ROOT = Path(__file__).resolve().parents[1]
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
        tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


class StripDocs(ast.NodeTransformer):
    def strip(self, node):
        self.generic_visit(node)
        if (node.body and isinstance(node.body[0], ast.Expr)
                and isinstance(node.body[0].value, ast.Constant)
                and isinstance(node.body[0].value.value, str)):
            node.body.pop(0)
            if not node.body and not isinstance(node, ast.Module):
                node.body.append(ast.Pass())
        return node
    visit_Module = visit_ClassDef = visit_FunctionDef = visit_AsyncFunctionDef = strip


def metric(path):
    raw = path.read_bytes()
    source = (ast.unparse(StripDocs().visit(ast.parse(raw))) + '\n').encode()
    return dict(path=str(path.relative_to(ROOT)),
                tokens=sum(t.type not in SKIP for t in tokenize.generate_tokens(io.StringIO(source.decode()).readline)),
                ast_nodes=len(list(ast.walk(ast.parse(source)))),
                normalized_bytes=len(source),
                gzip9_bytes=len(gzip.compress(source,compresslevel=9,mtime=0)),
                sha256=hashlib.sha256(raw).hexdigest())


def run(job):
    program, fixture, expected, optimized = job
    command = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT/program)]
    try:
        result = subprocess.run(command, input=(ROOT/fixture).read_bytes(),
                                stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=10)
        accepted = result.returncode == 0 and result.stdout == b'ACCEPT\n'
        return dict(program=program,fixture=fixture,optimized=optimized,
                    expected=expected,accepted=accepted,passed=accepted==expected,
                    returncode=result.returncode)
    except subprocess.TimeoutExpired:
        return dict(program=program,fixture=fixture,optimized=optimized,
                    expected=expected,accepted=False,passed=False,timeout=True)


def main():
    translations=[]
    for source in sorted((ROOT/'fixtures/source').glob('*.json')):
        data=json.loads(source.read_text())
        for profile,convert in [('odd',odd),('shared',shared)]:
            expected=json.loads((ROOT/'fixtures'/profile/source.name).read_text())
            actual=convert(data)
            if actual != expected:
                raise AssertionError('Translation mismatch: '+profile+'/'+source.name)
            translations.append(dict(source=source.name,profile=profile,packets=len(actual)-1))
    jobs=[]
    for program,profile in [('code/strict_tokens.py','odd'),('code/strict_ast.py','odd'),
                            ('code/strict_bytes.py','shared'),('code/readable_strict.py','shared')]:
        for fixture in sorted((ROOT/'fixtures'/profile).glob('*.json')):
            jobs.extend((program,str(fixture.relative_to(ROOT)),True,opt) for opt in (False,True))
        for fixture in sorted((ROOT/'fixtures/negative').glob('*.json')):
            jobs.extend((program,str(fixture.relative_to(ROOT)),False,opt) for opt in (False,True))
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        results=list(pool.map(run,jobs))
    metrics=[metric(ROOT/p) for p in ['code/strict_tokens.py','code/strict_ast.py',
             'code/strict_bytes.py','code/readable_strict.py','controls/prior_strict608.py',
             'controls/source_strict616.py','controls/source_strict_tokens.py','controls/source_strict_ast.py']]
    report=dict(python=platform.python_version(),metrics=metrics,translations=translations,
                process_runs=len(results),failures=[r for r in results if not r['passed']],results=results)
    (ROOT/'evidence/verification.json').write_text(json.dumps(report,indent=2)+'\n')
    (ROOT/'evidence/metrics.json').write_text(json.dumps(dict(python=platform.python_version(),programs=metrics),indent=2)+'\n')
    print(json.dumps(dict(translations=len(translations),process_runs=len(results),
                         failures=len(report['failures']),metrics=metrics),indent=2))
    if report['failures']:
        raise SystemExit(1)


if __name__=='__main__':
    main()
