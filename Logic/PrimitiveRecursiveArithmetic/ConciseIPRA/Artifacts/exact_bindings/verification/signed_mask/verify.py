"""Differential checks for canonical-mask integration; not trusted checker code."""
from pathlib import Path
import ast
import concurrent.futures
import hashlib
import io
import itertools
import json
import random
import subprocess
import sys
import tokenize

HERE = Path(__file__).resolve().parent
SCOPE = HERE / 'reference/source'
EXACT = HERE / 'reference/checker_exact.py'
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.INDENT, tokenize.DEDENT,
        tokenize.NEWLINE, tokenize.NL, tokenize.COMMENT}

def measure(path):
    src = path.read_text()
    norm = ast.unparse(ast.parse(src)) + '\n'
    return dict(tokens=sum(t.type not in SKIP for t in tokenize.generate_tokens(io.StringIO(norm).readline)),
                ast_nodes=len(list(ast.walk(ast.parse(norm)))), normalized_bytes=len(norm.encode()),
                sha256=hashlib.sha256(src.encode()).hexdigest())

exact_functions = [x for x in ast.parse(EXACT.read_text()).body
                   if isinstance(x, ast.FunctionDef) and x.name in ('term', 'formula')]
ns = {}
exec(compile(ast.Module(body=exact_functions, type_ignores=[]), '<upstream-predicate>', 'exec'), ns)
reference_formula = ns['formula']

def root_opener(path):
    tree = ast.parse(path.read_text())
    assign = next(x for x in tree.body if isinstance(x, ast.Assign)
                  and any(isinstance(t, ast.Name) and t.id == 'i' for t in x.targets))
    n = {'k': 0, 'v': 1, 'c': lambda *args: None}
    exec(compile(ast.Module(body=[assign], type_ignores=[]), '<candidate-opener>', 'exec'), n)
    return n

def result(fn, *args):
    try:
        return ('value', fn(*args))
    except Exception:
        return ('reject',)

def wrapper(original, output):
    tree = ast.parse(original.read_text())
    guard = ast.parse('def canonical_guard(a):\n    if not formula(a):\n        raise ValueError\n    return a\n').body[0]
    for x in tree.body:
        if isinstance(x, ast.Expr) and isinstance(x.value, ast.Call) and isinstance(x.value.func, ast.Name) and x.value.func.id == 'c':
            x.value.args[1] = ast.Call(func=ast.Name(id='canonical_guard', ctx=ast.Load()), args=[x.value.args[1]], keywords=[])
    tree.body = exact_functions + [guard] + tree.body
    output.write_text(ast.unparse(ast.fix_missing_locations(tree)) + '\n')

def main():
    profiles = [('exact_bytes.py', 'checker_bytes584.py'), ('exact_ast.py', 'checker_ast340.py')]
    generated = HERE / 'controls'
    generated.mkdir(exist_ok=True)
    for new, old in profiles:
        wrapper(SCOPE/'code'/old, generated/old)
    candidates = {name: root_opener(HERE/name) for name, _ in profiles}
    scalars = list(range(-3, 18)) + [31, 101]
    samples = scalars + [[]]
    samples += [[a] for a in scalars]
    samples += [[a,b] for a in scalars for b in scalars]
    samples += [[[a],[b]] for a in scalars for b in scalars]
    samples += [[a,b,c] for a,b,c in itertools.product(range(0,8), repeat=3)]
    rng = random.Random(20261113)
    def raw(depth):
        if not depth or rng.random() < .45:
            return rng.choice(scalars)
        return [raw(depth-1) for _ in range(rng.randrange(5))]
    samples += [raw(6) for _ in range(20000)]
    # Build many canonical terms, then force each ordinary and padding index.
    terms = [1, [1], [1,1,3], [[1],1,3], [1,[1],3]]
    for depth in range(1,8):
        for t in terms:
            for code in range(1, 4*depth+12):
                a = [[code], t]
                for _ in range(depth):
                    a = [a]
                samples.append(a)
    grammar_mismatches = []
    for a in samples:
        expected = bool(reference_formula(a))
        for name, n in candidates.items():
            got = result(n['i'], a)
            accepted = got[0] == 'value'
            if accepted != expected or accepted and got[1] != a:
                grammar_mismatches.append({'profile':name,'goal':a,'expected':expected,'result':got})
    old = root_opener(SCOPE/'code/checker_bytes584.py')
    new = root_opener(HERE/'exact_bytes.py')
    phase_mismatches = []
    for j in range(12000):
        old['k'] = new['k'] = rng.choice([-1,-2,-5,-17])
        a, t, d = raw(4), raw(3), rng.randrange(-3,12)
        x, y = result(old['i'],a,t,d), result(new['i'],a,t,d)
        if x != y:
            phase_mismatches.append({'a':a,'t':t,'d':d,'old':x,'new':y})
    jobs = []
    fixture_counts = {}
    extra_goals = [[[3],[1]], [[5],[1]], [[7],[1]], [[3,1,1],1],
                   [[1,3,1],1], [-1,1],
                   [[1,1,5],1], [[1,1,7],1]]
    for newname, oldname in profiles:
        cases = json.loads((SCOPE/'certificates'/(oldname[:-3]+'.json')).read_text())['cases']
        good = next(c['certificate'] for c in cases if c['expected'])
        cases += [{'name':'anti_padding_'+str(j),'certificate':good[:-1]+[a],'expected':False}
                  for j,a in enumerate(extra_goals)]
        fixture_counts[newname] = len(cases)
        for case in cases:
            for optimized in (False, True):
                for kind, path in [('candidate',HERE/newname),('matched_exact_wrapper',generated/oldname)]:
                    jobs.append((newname,kind,path,case,optimized))
    def run(job):
        name,kind,path,case,optimized = job
        p = subprocess.run([sys.executable,*(['-O'] if optimized else []),str(path)], input=json.dumps(case['certificate']), text=True, capture_output=True, timeout=15)
        actual = p.returncode == 0 and p.stdout == 'ACCEPT\n'
        return {'profile':name,'kind':kind,'case':case['name'],'optimized':optimized,
                'expected':case['expected'],'accepted':actual,'exit_code':p.returncode}
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        runs = list(pool.map(run,jobs))
    failures = [r for r in runs if r['expected'] != r['accepted']]
    receipt = {'python':sys.version,'metrics':{name:measure(HERE/name) for name,_ in profiles},
               'reference_exact_metrics':measure(EXACT),'grammar_cases':len(samples),
               'grammar_comparisons':len(samples)*len(candidates),'grammar_mismatches':grammar_mismatches,
               'proof_phase_opener_comparisons':12000,'proof_phase_mismatches':phase_mismatches,
               'fixture_counts':fixture_counts,'process_runs':len(runs),'failures':failures,'results':runs,
               'claim_boundary':'Finite differential evidence; universal equivalence is established by the written mask and phase invariants.'}
    (HERE/'verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k!='results'},indent=2))
    if failures or grammar_mismatches or phase_mismatches:
        raise SystemExit(1)

if __name__ == '__main__':
    main()
