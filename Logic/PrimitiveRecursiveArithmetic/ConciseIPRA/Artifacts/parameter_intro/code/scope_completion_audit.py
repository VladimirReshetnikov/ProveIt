"""Independent bounded check of the erased-parameter completion lemma.

This is a finite test of the implementation, not a proof of the lemma.
"""
import ast
import json
import random
from pathlib import Path

source = Path(__file__).resolve().parent / 'checker.py'
tree = ast.parse(source.read_text())
tree.body = [n for n in tree.body if isinstance(n, (ast.FunctionDef, ast.Import, ast.ImportFrom))]
ns = {}
exec(compile(tree, str(source), 'exec'), ns)
walk, sub, syntax = ns['walk'], ns['sub'], ns['syntax']

def norm(x):
    return walk(x, lambda i, d: i)

def complete(x, d=0):
    if type(x) is int:
        return 0 if x < -1 or x > d + 1 else x
    size = len(x)
    return [complete(a, d + 2 * (size != 2 and j == size - 1)) for j, a in enumerate(x)]

rng = random.Random(48629)

def term(k, d):
    if k <= 0 or rng.randrange(3) == 0:
        return rng.choice([-3, -2, -1, 0, *range(1, d + 4)])
    # Keep the experiment bounded: a zero-counter R can erase an arbitrary
    # out-of-scope body; an inert counter retains it. Avoid huge recurrences.
    c = rng.choice([0, -1, d + 1, d + 2])
    return [c, term(k - 1, d), term(k - 1, d + 2)]

def form(k, d=0):
    if k and rng.randrange(3) == 0:
        return [form(k - 1, d + 2)]
    return [term(k, d), term(k, d)]

def valid(a):
    try:
        syntax(a, -2, True)
        return True
    except (ValueError, RecursionError):
        return False

targets = [0, -1, [0, 0, 0], [0, -1, 0], [-1, 0, 1]]
checked = erased = 0
examples = []
for trial in range(5000):
    f = form(3)
    s, t = rng.choice(targets), rng.choice(targets)
    try:
        a, b = sub(f, s), sub(f, t)
        if not (valid(a) and valid(b)):
            continue
        repaired = norm(complete(f))
        assert walk(repaired, lambda i, d: ns['need'](-2 < i <= d) or i, 1, True) == repaired
        assert sub(repaired, s) == a
        assert sub(repaired, t) == b
        checked += 1
        if complete(f) != f:
            erased += 1
            if len(examples) < 3:
                examples.append({'raw': f, 'source': s, 'target': t, 'completed': repaired})
    except RecursionError:
        continue

print(json.dumps({'trials': 5000, 'two_valid_endpoints': checked,
                  'valid_with_erased_extra_parameters': erased,
                  'counterexamples': 0, 'examples': examples}, indent=2))
