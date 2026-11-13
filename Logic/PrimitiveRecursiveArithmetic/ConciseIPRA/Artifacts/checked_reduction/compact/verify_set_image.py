"""Independent finite checks of the singleton-set image refinement.

The checker imports no part of this verification script.
"""
import ast
import gzip
import hashlib
import io
import json
import platform
from pathlib import Path
import subprocess
import sys
import tokenize
import zipfile

HERE = Path(__file__).resolve().parent
REPO = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else None
BASE = HERE
CONTROL = HERE / 'control_ast256.py'
CANDIDATE = HERE / 'checker_ast255.py'
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
        tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}

def measure(source):
    tree = ast.parse(source)
    normalized = ast.unparse(tree) + '\n'
    return {'tokens': sum(t.type not in SKIP for t in tokenize.generate_tokens(io.StringIO(normalized).readline)),
            'ast_nodes': len(list(ast.walk(tree))),
            'normalized_bytes': len(normalized.encode()),
            'normalized_sha256': hashlib.sha256(normalized.encode()).hexdigest()}

def structural():
    tree = ast.parse(CONTROL.read_text())
    count = 0
    for node in ast.walk(tree):
        if (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                and node.func.id == 'i' and len(node.args) == 2
                and isinstance(node.args[0], ast.Name) and node.args[0].id == 'a'
                and isinstance(node.args[1], ast.List)
                and len(node.args[1].elts) == 1
                and isinstance(node.args[1].elts[0], ast.Name)
                and node.args[1].elts[0].id == 'k'):
            node.args[1] = ast.Set(elts=node.args[1].elts)
            count += 1
    same = ast.dump(tree, include_attributes=False) == ast.dump(ast.parse(CANDIDATE.read_text()), include_attributes=False)
    assert count == 1 and same
    return {'replaced_image_literals': count, 'all_other_ast_fields_identical': same}

def run(path, data, optimized):
    cmd = [sys.executable, '-I', '-S', '-B']
    if optimized:
        cmd.append('-O')
    cmd.append(str(path))
    p = subprocess.run(cmd, input=data, capture_output=True, timeout=10)
    return {'accepted': p.returncode == 0 and p.stdout == b'ACCEPT\n',
            'exit_code': p.returncode, 'stdout': p.stdout.decode(errors='replace'),
            'exception': p.stderr.decode(errors='replace').splitlines()[-1] if p.stderr else ''}

def trace(path, text):
    lines = iter(text.splitlines())
    reads = []
    outputs = []
    def input_line():
        x = next(lines)
        reads.append(x)
        return x
    env = {'input': input_line, 'print': lambda *xs: outputs.append(list(xs))}
    try:
        exec(compile(path.read_text(), str(path), 'exec'), env)
        outcome = 'return'
    except Exception as exc:
        outcome = type(exc).__name__
    return {'outcome': outcome, 'reads': reads, 'outputs': outputs, 'final_floor': env.get('k')}

def opener_checks():
    namespace = {}
    # Isolate exactly the unchanged decoder definition and its default initializer.
    t = ast.parse(CANDIDATE.read_text())
    f = next(n for n in t.body if isinstance(n, ast.FunctionDef) and n.name == 'i')
    exec(compile(ast.Module(body=[f], type_ignores=[]), '<decoder>', 'exec'), namespace)
    i = namespace['i']
    cases = 0
    raw = [-12, -3, -1, 0, 1, 2, 3, 4, 5, 7, 9, 100, [], [0], [100],
           [3, 7], [0, 3, 5], [[9], [1, 3], [0, 5, 9]], [[], [], [], []]]
    for floor in [0, -1, -3, -10]:
        namespace['k'] = floor
        assert i([floor], d=3) == i({floor}, d=3) == [floor]
        for a in raw:
            for depth in range(-2, 12):
                outcomes = []
                for image in ([floor], {floor}):
                    try:
                        outcomes.append(('value', i(a, image, depth)))
                    except Exception as exc:
                        outcomes.append(('exception', type(exc).__name__))
                assert outcomes[0] == outcomes[1], (floor, a, depth, outcomes)
                cases += 1
    return {'image_comparisons': cases, 'all_identical': True}

def strip_docs(tree):
    for n in ast.walk(tree):
        body = getattr(n, 'body', None)
        if isinstance(body, list) and body and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant) and isinstance(body[0].value.value, str):
            body.pop(0)
    return tree

def novelty():
    if REPO is None:
        return {'performed': False, 'reason': 'Pass a pinned ConciseIPRA checkout path to repeat the optional source census.'}
    wanted = measure(CANDIDATE.read_text())['normalized_sha256']
    count = 0
    failures = []
    duplicates = []
    set_images = []
    def inspect(name, data):
        nonlocal count
        try:
            if name.endswith('.gz'):
                data = gzip.decompress(data)
            tree = ast.parse(data.decode())
            count += 1
            norm = ast.unparse(strip_docs(tree)) + '\n'
            if hashlib.sha256(norm.encode()).hexdigest() == wanted:
                duplicates.append(name)
            # This syntactic screen also catches spaces and spelling changes.
            if any(isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == 'i'
                   and any(isinstance(a, ast.Set) and len(a.elts) == 1 for a in n.args)
                   for n in ast.walk(tree)):
                set_images.append(name)
        except Exception as exc:
            failures.append({'path': name, 'error': str(exc)})
    for p in sorted((REPO/'Artifacts').rglob('*')):
        if p.is_file() and (p.name.endswith('.py') or p.name.endswith('.py.gz')):
            inspect(str(p.relative_to(REPO)), p.read_bytes())
    for p in sorted((REPO/'docs/incoming').glob('*.zip')):
        with zipfile.ZipFile(p) as z:
            for name in z.namelist():
                if name.endswith(('.py', '.py.gz')):
                    inspect(str(p.relative_to(REPO))+'!'+name, z.read(name))
    return {'performed': True, 'parsed_source_occurrences': count, 'parse_failures': failures,
            'same_normalized_module': duplicates, 'singleton_set_call_images': set_images,
            'scope': 'Current Artifacts Python/gzip files and Python/gzip members of all five incoming ZIPs; nested historical ZIPs and strings containing generated sources not expanded.'}

def main():
    metrics = {'control': measure(CONTROL.read_text()), 'candidate': measure(CANDIDATE.read_text())}
    assert tuple(metrics['control'][k] for k in ('tokens','ast_nodes','normalized_bytes')) == (245,256,580)
    assert tuple(metrics['candidate'][k] for k in ('tokens','ast_nodes','normalized_bytes')) == (245,255,580)
    results = []
    traces = []
    positives = 0
    for fixture in sorted((BASE/'fixtures').glob('*.jsonl')):
        data = fixture.read_bytes()
        expected = fixture.name.startswith('global_') or fixture.name == 'direct_successor_zero_initializer.jsonl'
        positives += expected
        for optimized in [False, True]:
            before, after = run(CONTROL, data, optimized), run(CANDIDATE, data, optimized)
            assert before == after, (fixture, optimized, before, after)
            assert after['accepted'] == expected, (fixture, expected, after)
            results.append({'fixture': fixture.name, 'optimized': optimized, 'control': before, 'candidate': after})
        a, b = trace(CONTROL, data.decode()), trace(CANDIDATE, data.decode())
        assert a == b, (fixture, a, b)
        traces.append({'fixture': fixture.name, 'outcome': a['outcome'], 'lines_read': len(a['reads']), 'final_floor': a['final_floor'], 'identical': True})
    receipt = {'python': platform.python_version(), 'metrics': metrics,
               'structural': structural(), 'fixtures': len(traces), 'positive_fixtures': positives,
               'isolated_process_executions': len(results)*2, 'trace_comparisons': traces,
               'opener': opener_checks(), 'novelty': novelty(), 'results': results,
               'status': 'All checks passed; finite evidence supplements the separate universal proof.'}
    (HERE/'set_image_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:receipt[k] for k in ['python','metrics','structural','fixtures','positive_fixtures','isolated_process_executions','opener','novelty','status']},indent=2))

if __name__ == '__main__':
    main()
