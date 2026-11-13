"""Reproduce complete modules, exact source transformations and finite controls."""
from pathlib import Path
import ast
import concurrent.futures
import hashlib
import io
import json
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
        tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}

def normalized(source):
    return ast.unparse(ast.parse(source)) + '\n'

def outer_lambda(source):
    tree = ast.parse(source)
    node = tree.body[1]
    assert isinstance(node, ast.FunctionDef)
    assert isinstance(node.body[0], ast.Assign)
    assert isinstance(node.body[1], ast.Return)
    tree.body[1] = ast.Assign(
        targets=[ast.Name(id='c', ctx=ast.Store())],
        value=ast.Lambda(args=node.args, body=ast.BoolOp(op=ast.And(), values=[
            ast.NamedExpr(target=ast.Name(id='i', ctx=ast.Store()),
                          value=node.body[0].value), node.body[1].value])))
    ast.fix_missing_locations(tree)
    return ast.unparse(tree) + '\n'

def measure(name):
    raw = (ROOT / name).read_bytes()
    source = normalized(raw)
    compile(source, name, 'exec')
    return dict(file=name, tokens=sum(t.type not in SKIP for t in
                tokenize.generate_tokens(io.StringIO(source).readline)),
                ast_nodes=len(list(ast.walk(ast.parse(source)))),
                normalized_bytes=len(source.encode()),
                sha256=hashlib.sha256(raw).hexdigest())

def main():
    old = (ROOT / 'native_control.py').read_text()
    body = old[old.index('        c(g + '):old.index('\nq =')].strip()
    body = body.replace('c(g, m, k) or m * 3',
                        'c(g, m, k) and m * 3')
    expected = (old[:old.index('    if i(a) not in g:')]
                + '    return i(a) in g or g.append(0) or ['
                + body + ' for m, s, u, t in [q()]]\n'
                + old[old.index('\nq ='):])
    expected = normalized(expected)
    assert expected == (ROOT / 'native_append_function.py').read_text()
    assert outer_lambda(expected) == (ROOT / 'native_append_lambda.py').read_text()
    strict_old = (ROOT / 'strict646_control.py').read_text()
    assert outer_lambda(strict_old) == (ROOT / 'strict645_lambda.py').read_text()
    names = ['native_control.py', 'native_append_function.py',
             'native_append_lambda.py', 'strict646_control.py',
             'strict645_lambda.py']
    metrics = [measure(name) for name in names]
    expected_metrics = [(324,374,629),(330,379,623),(335,383,622),
                        (343,392,646),(348,396,645)]
    for row, expected in zip(metrics, expected_metrics):
        assert tuple(row[k] for k in ['tokens','ast_nodes','normalized_bytes']) == expected
    jobs = []
    for profile, groups, programs in [
        ('native',['fixtures'],names[:3]),
        ('strict',['proofs','boundary'],names[3:])]:
        for group in groups:
            base = ROOT / 'fixtures' / profile / group
            for case in json.loads((base / 'cases.json').read_text()):
                for program in programs:
                    for optimized in (False, True):
                        jobs.append((profile, base, case, program, optimized))

    def run(job):
        profile, base, case, program, optimized = job
        payload = (base / case['file']).read_bytes()
        command = [sys.executable, '-I', '-S', '-B']
        if optimized:
            command.append('-O')
        command.append(str(ROOT / program))
        result = subprocess.run(command, input=payload, capture_output=True,
                                timeout=20)
        actual = result.returncode == 0 and result.stdout == b'ACCEPT\n'
        return dict(profile=profile, fixture=str((base / case['file']).relative_to(ROOT)),
                    program=program, optimized=optimized, expected=case['expected'],
                    actual=actual, passed=actual == case['expected'],
                    fixture_sha256=hashlib.sha256(payload).hexdigest())

    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        results = list(pool.map(run, jobs))
    report = dict(python=sys.version, exact_transformations_checked=True,
                  metrics=metrics, process_executions=len(results),
                  failures=[r for r in results if not r['passed']], results=results)
    (ROOT / 'refinement_verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k != 'results'},indent=2))
    if report['failures']:
        raise SystemExit(1)

if __name__ == '__main__':
    main()
