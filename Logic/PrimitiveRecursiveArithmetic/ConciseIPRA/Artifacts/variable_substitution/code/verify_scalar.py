"""Checks variable-source substitution and the direct fresh-name Tr compiler."""
import copy
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def load(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / (name + '.py'))
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


V = load('scalar_latest')
T = load('scalar_transport')
NATIVE = load('native_goal_latest')
Z = ['z']
ONE = ['s', Z]
TWO = ['s', ONE]
H = ['=', Z, Z]


def var(i):
    return ['v', i]


def eq(s, t):
    return ['=', s, t]


def norm(t):
    return V.walk(t, lambda i, d: var(i))


def C(v, a, b):
    return norm(['i', v, a, V.shift(b)])


def parity(v):
    return norm(['i', v, Z, ['i', var(0), ONE, Z]])


def refl(t):
    return ['r', t]


def use(j, t=Z, proof=None):
    return ['u', j, t, refl(Z) if proof is None else proof]


def assumption(a):
    return (H, V.shift(a))


def weaken(p, amount=1, clauses=1, depth=0, local=0):
    """Rename free variables and add outer clauses; keep local binders fixed."""
    tag, *a = p
    shift = lambda x: V.shift(x, amount, depth)
    recur = lambda q: weaken(q, amount, clauses, depth, local)
    if tag == 'r':
        return ['r', shift(a[0])]
    if tag == 'u':
        j, t, q = a
        return ['u', j + (clauses if j >= local else 0), shift(t), recur(q)]
    if tag == 'x':
        return ['x', recur(a[0]), recur(a[1])]
    goal, data, branch = a
    return [tag, shift(goal), recur(data) if tag == 'e' else shift(data),
            weaken(branch, amount, clauses, depth + 1, local + 1)]


def cases(s, t, hs, r, k, p, q):
    """From s=t and hs=r derive C(k,s,hs)=C(k,t,r), without equality rules."""
    matrix = eq(C(var(0), V.shift(s), V.shift(hs)),
                C(var(0), V.shift(t), V.shift(r)))
    paired = ['d', V.shift(matrix, 1, 1)]
    introduced = ['i', paired, ONE, weaken(q)]
    goal = V.sub(matrix, k)
    return ['e', goal, introduced, use(0, V.shift(k), weaken(p))]


def transport(s, t, h, r, p, q):
    """Compile one crossed transport using only variable-source substitution."""
    hs = V.sub(h, s)
    inner_left = C(parity(var(0)), var(1), V.shift(h))
    inner_right = C(parity(var(0)), V.shift(t, 2), V.shift(r, 2))
    matrix = eq(C(var(0), Z, inner_left), C(var(0), Z, inner_right))
    paired = ['d', matrix]
    branch = cases(V.shift(s), V.shift(t), V.shift(hs), V.shift(r),
                   parity(['s', var(0)]), weaken(p), weaken(q))
    introduced = ['i', paired, s, branch]
    # The fresh name is variable zero in the elimination branch.
    result = ['x', use(0, TWO), use(0, ONE)]
    return ['e', eq(r, V.sub(h, t)), introduced, result]


def native_hint(p, g, n, kinds):
    """Map clausal proofs to native Q/D hints; kinds mark Q assumptions."""
    tag, *a = p
    if tag == 'r':
        return None
    if tag == 'u':
        j, t, q = a
        return ['qe', g[j][1], t, None, native_hint(q, g, n, kinds)] if kinds[j] else None
    if tag == 'x':
        major, minor = a
        equation = V.derive(major, g, n)
        instance = V.derive(minor, g, n)
        return ['vs', equation[2], instance[1],
                native_hint(major, g, n, kinds), native_hint(minor, g, n, kinds)]
    goal, data, branch = a
    if tag == 'e':
        b = V.derive(data, g, n)[1]
        extended = [(V.sub(b, Z), b)] + V.lift(g)
        return ['de', b, native_hint(data, g, n, kinds),
                native_hint(branch, extended, n + 1, [True] + kinds)]
    b = V.sub(goal[1], V.shift(data), index=1)
    h = b if b[0] == '=' and data == Z else V.shift(V.sub(b, Z))
    extended = [(H, V.shift(h))] + V.lift(g)
    return ['di', data, native_hint(branch, extended, n + 1, [False] + kinds)]


def native_accept(cert):
    try:
        NATIVE.check(copy.deepcopy(cert))
        return True
    except Exception:
        return False


def translate(p, g, n):
    """Translate a complete Tr proof inductively, before macro weakening."""
    tag, *a = p
    if tag == 'r':
        return p
    if tag == 'u':
        j, t, q = a
        return ['u', j, t, translate(q, g, n)]
    if tag == 'x':
        h, major, minor = a
        equation = T.derive(major, g, n)
        instance = T.derive(minor, g, n)
        return transport(equation[1], equation[2], h, instance[2],
                         translate(major, g, n), translate(minor, g, n))
    goal, data, branch = a
    if tag == 'e':
        b = T.derive(data, g, n)[1]
        extended = [(V.sub(b, Z), b)] + V.lift(g)
        return ['e', goal, translate(data, g, n), translate(branch, extended, n + 1)]
    b = V.sub(goal[1], V.shift(data), index=1)
    h = b if b[0] == '=' and data == Z else V.shift(V.sub(b, Z))
    extended = [(H, V.shift(h))] + V.lift(g)
    return ['i', goal, data, translate(branch, extended, n + 1)]


def rename_term(t, permutation, protected=0):
    return V.walk(t, lambda i, d: var(i) if i < d + protected
                  else var(d + protected + permutation[i - d - protected]))


def rename_proof(p, permutation, protected=0):
    tag, *a = p
    rename = lambda x: rename_term(x, permutation, protected)
    recur = lambda q: rename_proof(q, permutation, protected)
    if tag == 'r':
        return ['r', rename(a[0])]
    if tag == 'u':
        j, t, q = a
        return ['u', j, rename(t), recur(q)]
    if tag == 'x':
        return ['x', recur(a[0]), recur(a[1])]
    goal, data, branch = a
    return [tag, rename(goal), recur(data) if tag == 'e' else rename(data),
            rename_proof(branch, permutation, protected + 1)]


results = []


def record(name, value):
    results.append({'name': name, 'passed': bool(value)})
    if not value:
        raise AssertionError(name)


s, t, r = var(0), var(1), var(2)
templates = [var(0), Z, ['s', var(0)],
             ['i', var(0), Z, var(0)],
             ['i', var(3), var(1), var(1)],
             ['i', var(3), var(1), ['i', var(1), Z, var(1)]],
             ['i', var(3), ['i', var(0), var(1), var(0)],
              ['i', var(1), Z, var(2)]]]
examples = []
native_examples = []
for i, h in enumerate(templates):
    V.syntax(h, 5)
    hs = V.sub(h, s)
    context = [assumption(eq(s, t)), assumption(eq(hs, r))]
    p, q = use(0), use(1)
    compiled = transport(s, t, h, r, p, q)
    expected = eq(r, V.sub(h, t))
    actual = V.derive(compiled, copy.deepcopy(context), 4)
    control = T.derive(['x', h, p, q], copy.deepcopy(context), 4)
    record('direct_derived_transport_' + str(i), actual == expected == control)
    # This renaming moves all sources away from variable zero; they remain legal.
    enlarged = [assumption(H)] + V.lift(context)
    record('weakening_stability_' + str(i),
           V.derive(weaken(compiled), enlarged, 5) == V.shift(expected))
    examples.append({'variables': 4, 'context': context, 'expected': expected, 'proof': compiled})
    native_cert = {'variables': 4, 'context': [eq(s, t), eq(hs, r)],
                   'goal': expected, 'proof': native_hint(compiled, context, 4, [False, False])}
    record('native_goal_compiled_transport_' + str(i), native_accept(native_cert))
    native_examples.append(native_cert)

# The crucial structural regression: an already translated Tr premise has
# its own internal E/VS. Embedding it into another macro preserves that
# internal source as variable zero, even under several additional scopes.
nested_context = [assumption(eq(s, t))]
nested = use(0)
left, right = s, t
for h in [templates[4], ['i', var(0), var(2), ['s', var(0)]],
          ['i', var(4), var(0), ['i', var(1), var(0), var(1)]]]:
    nested = ['x', h, nested, refl(V.sub(h, left))]
    left, right = V.sub(h, left), V.sub(h, right)
nested_expected = eq(left, right)
nested_compiled = translate(nested, nested_context, 4)
record('three_nested_transport_macros',
       T.derive(nested, nested_context, 4) == nested_expected
       and V.derive(nested_compiled, nested_context, 4) == nested_expected)
two_extra = [assumption(H), assumption(H)] + V.lift(V.lift(nested_context))
record('nested_macro_two_scope_weakening',
       V.derive(weaken(nested_compiled, amount=2, clauses=2), two_extra, 6)
       == V.shift(nested_expected, 2))
permutation = [2, 0, 3, 1]
renamed_context = [(rename_term(a, permutation), rename_term(b, permutation, 1))
                   for a, b in nested_context]
record('nested_macro_initial_parameter_permutation',
       V.derive(rename_proof(nested_compiled, permutation), renamed_context, 4)
       == rename_term(nested_expected, permutation))
nested_native = {'variables': 4, 'context': [eq(s, t)], 'goal': nested_expected,
                 'proof': native_hint(nested_compiled, nested_context, 4, [False])}
record('native_three_nested_transport_macros', native_accept(nested_native))
native_examples.append(nested_native)


# A variable substitution can expose a recursor computation beneath a binder.
u = ['i', var(0), Z, ['i', var(1), Z, var(1)]]
ctx = [assumption(eq(var(0), ONE)), assumption(eq(u, var(1)))]
expected = eq(var(1), V.sub(u, ONE, 0, 0))
record('nested_normalizing_variable_substitution', V.derive(['x', use(0), use(1)], ctx, 2) == expected)

# The source guard must reject an arbitrary closed source, including zero.
try:
    V.derive(['x', refl(Z), refl(Z)], [], 0)
    rejected = False
except Exception:
    rejected = True
record('reject_closed_source', rejected)

# A literal variable other than the newest is deliberately not a primitive
# source in the selected checker. The arbitrary-variable companion accepts it.
ctx = [assumption(eq(var(1), ONE)), assumption(eq(var(1), var(0)))]
raw = ['x', use(0), use(1)]
try:
    V.derive(raw, ctx, 2)
    rejected = False
except Exception:
    rejected = True
record('reject_nonnewest_source', rejected)

native_negative = {
    'nonnewest_source': {'variables': 3, 'context': [eq(var(1), ONE), eq(var(0), var(2))],
                        'goal': eq(var(2), ONE), 'proof': ['vs', ONE, var(0), None, None]},
    'bad_scope': {'variables': 1, 'context': [eq(var(0), ONE)],
                  'goal': eq(Z, ONE), 'proof': ['vs', ONE, var(2), None, None]},
    'boolean_scope': {'variables': True, 'context': [], 'goal': H, 'proof': None},
    'malformed_hint': {'variables': 3, 'context': [eq(var(0), ONE), eq(var(0), var(2))],
                       'goal': eq(var(2), ONE), 'proof': ['vs', ONE, var(0), None]},
    'wrong_endpoint': {'variables': 3, 'context': [eq(var(0), ONE), eq(var(0), var(2))],
                       'goal': eq(var(2), TWO), 'proof': ['vs', ONE, var(0), None, None]},
    'sort_in_erased_redex': {'variables': 3, 'context': [eq(var(0), ONE)],
                            'goal': eq(var(2), ONE),
                            'proof': ['vs', ONE, ['i', Z, ONE, H], None, None]},
    'scope_in_erased_redex': {'variables': 3, 'context': [eq(var(0), ONE)],
                             'goal': eq(var(2), ONE),
                             'proof': ['vs', ONE, ['i', Z, ONE, var(99)], None, None]},
}
for name, cert in native_negative.items():
    record('native_reject_' + name, not native_accept(cert))

closed = [
    {'goal': H, 'proof': refl(Z)},
    {'goal': ['d', eq(var(0), var(0))],
     'proof': ['i', ['d', eq(var(0), var(0))], Z, refl(['s', var(0)])]},
]
stationary = ['d', eq(['i', var(0), Z, var(0)], Z)]
closed.append({'goal': stationary, 'proof': ['i', stationary, Z, use(0)]})
for source, h in [(ONE, ['i', var(0), Z, ['s', var(0)]]), (Z, Z)]:
    result = V.sub(h, source)
    closed.append({'goal': eq(result, result),
                   'proof': transport(source, source, h, result, refl(source), refl(result))})
for i, cert in enumerate(closed):
    record('closed_theorem_' + str(i), V.verify(cert))
    native_cert = {'variables': 0, 'context': [], 'goal': cert['goal'],
                   'proof': native_hint(cert['proof'], [], 0, [])}
    record('native_closed_theorem_' + str(i), native_accept(native_cert))
    native_examples.append(native_cert)

scalar_negative = {
    'closed_source': {'goal': H, 'proof': ['x', refl(Z), refl(Z)]},
    'false_goal': {'goal': eq(Z, ONE), 'proof': refl(Z)},
    'scope_escape': {'goal': eq(var(0), var(0)), 'proof': refl(var(0))},
    'witness_escape': {'goal': ['d', eq(var(0), var(0))],
                       'proof': ['i', ['d', eq(var(0), var(0))], var(0), refl(var(0))]},
    'boolean_variable': {'goal': eq(var(False), var(False)), 'proof': refl(var(False))},
    'extra_header': {'goal': H, 'proof': refl(Z), 'extra': 0},
    'unknown_rule': {'goal': H, 'proof': ['unknown', Z]},
    'scope_in_erased_redex': {'goal': H, 'proof': refl(['i', Z, Z, var(99)])},
    'sort_in_erased_redex': {'goal': H, 'proof': refl(['i', Z, Z, H])},
    'unreduced_counter': {'goal': H, 'proof': refl(['i', Z, Z, var(0)])},
    'bad_clause_index': {'goal': stationary,
                         'proof': ['i', stationary, Z, ['u', False, Z, refl(Z)]]},
    'bad_progress_step': {'goal': ['d', eq(var(0), Z)],
                          'proof': ['i', ['d', eq(var(0), Z)], Z, use(0)]},
}
for name, cert in scalar_negative.items():
    try:
        V.verify(cert)
        rejected = False
    except Exception:
        rejected = True
    record('scalar_reject_' + name, rejected)

cli_cases = []
for family, checker, examples, negatives in [
    ('native', 'native_goal_latest.py', native_examples, native_negative),
    ('scalar', 'scalar_latest.py', closed, scalar_negative),
]:
    directory = ROOT / 'certificates' / family
    directory.mkdir(parents=True, exist_ok=True)
    for i, cert in enumerate(examples):
        path = directory / ('accept_' + str(i).zfill(2) + '.json')
        path.write_text(json.dumps(cert, indent=2) + '\n')
        cli_cases.append({'path': str(path.relative_to(ROOT)), 'checker': checker, 'expected': True})
    for name, cert in negatives.items():
        path = directory / ('reject_' + name + '.json')
        path.write_text(json.dumps(cert, indent=2) + '\n')
        cli_cases.append({'path': str(path.relative_to(ROOT)), 'checker': checker, 'expected': False})
(ROOT / 'cli_cases.json').write_text(json.dumps(cli_cases, indent=2) + '\n')

(ROOT / 'scalar_verification.json').write_text(json.dumps({'checks': len(results),
    'passed': all(r['passed'] for r in results), 'results': results,
    'boundary': 'Finite implementation checks; the proof compiler implements the written derivation.'}, indent=2) + '\n')
(ROOT / 'scalar_transport_examples.json').write_text(json.dumps(examples, indent=2) + '\n')
(ROOT / 'native_latest_examples.json').write_text(json.dumps(native_examples, indent=2) + '\n')
print(json.dumps({'checks': len(results), 'passed': all(r['passed'] for r in results)}))
