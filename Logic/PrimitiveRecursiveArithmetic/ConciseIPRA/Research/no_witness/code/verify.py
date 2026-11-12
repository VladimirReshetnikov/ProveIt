"""Untrusted fixtures and translators; no checker imports this module."""
import ast
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

HERE = Path(__file__).resolve().parent

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

EIGHT = load('candidate_eight', HERE / 'checker_eight.py')
SEVEN = load('candidate_seven', HERE / 'checker_seven.py')
OLD_EIGHT = load('old_eight', HERE / 'control_eight.py')
OLD_SEVEN = load('old_seven', HERE / 'control_seven.py')
PINNED_DIR = HERE / 'reference'
PINNED_EIGHT = load('pinned_eight', PINNED_DIR / 'native_checker.py')
PINNED_SEVEN = load('pinned_seven', PINNED_DIR / 'diagonal_checker.py')
HELP = load('pinned_helpers', PINNED_DIR / 'translate.py')

# Arithmetic builders in the raw level / bound-index notation.
def S(t): return [0, t]
def I(c, a, h): return [c, a, h]
def E(s, t): return [s, t]
def Q(a): return ['q', a]
def D(a): return [a]
def HYP(j): return ['hyp', j]
def TR(h, p, q): return ['tr', h, p, q]

def refl(t):
    z = ['zero', t, 0]
    return TR(1, z, z)

def sym(p, g, n, checker=EIGHT):
    s, _ = checker.infer(p, g, n)
    return TR(s, p, p)

def trans(p, q, g, n, checker=EIGHT):
    return TR(1, q, sym(p, g, n, checker))

def congr(h, p, g, n, checker=EIGHT):
    s, _ = checker.infer(p, g, n)
    return TR(h, p, refl(checker.opening(h, s)))

def normalize(t, g, n, checker=EIGHT, fuel=300):
    """Produce t = its weak-head normal form, using actual raw rules."""
    if fuel <= 0:
        raise RuntimeError('normalization producer budget')
    if type(t) is int:
        return refl(t)
    if len(t) == 2:
        p = normalize(t[1], g, n, checker, fuel - 1)
        return congr([0, 1], p, g, n, checker)
    c, a, h = t
    cp = normalize(c, g, n, checker, fuel - 1)
    c1 = checker.infer(cp, g, n)[1]
    first = congr([1, a, h], cp, g, n, checker)
    if c1 == 0:
        step = ['zero', a, h]
    elif type(c1) is list and len(c1) == 2:
        step = ['succ', c1[1], a, h]
    else:
        return first
    end = checker.infer(step, g, n)[1]
    rest = normalize(end, g, n, checker, fuel - 1)
    return trans(first, trans(step, rest, g, n, checker), g, n, checker)

def computation_equation(a, b, g, n, checker=EIGHT):
    p, q = normalize(a, g, n, checker), normalize(b, g, n, checker)
    assert checker.infer(p, g, n)[1] == checker.infer(q, g, n)[1]
    return trans(p, sym(q, g, n, checker), g, n, checker)

# Shift only free bound indices, for building a term beneath new binders.
def lift_bound(a, count=1, d=0):
    if type(a) is int:
        return a + count if a > d else a
    if a[0] == 'q':
        return ['q', lift_bound(a[1], count, d + 1)]
    return [lift_bound(b, count, d + (2 if len(a) == 1 else int(len(a) == 3 and j == 2))) for j, b in enumerate(a)]

def C(c, a, b):
    # b does not depend on the iterator's new update variable.
    return I(c, a, lift_bound(b))

def naming(y):
    # x is 2, v is 1; y is shifted beneath the two D binders.
    yy = lift_bound(y, 2)
    return D(E(C(1, 0, C(yy, 0, S(2))), C(1, 0, yy)))

def intro_computational(matrix, g, n, checker=EIGHT):
    body = checker.opening(matrix, -n, 1)
    fresh = -n - 1
    diag = (len(matrix) == 2 and all(type(t) is list and len(t) == 3 and t[:2] == [1, 1] for t in matrix))
    eta = fresh if checker is SEVEN and diag else 0
    local = checker.opening(body, eta)
    target = checker.opening(body, S(fresh))
    p = computation_equation(*target, g + [local], n + 1, checker)
    result = ['di', matrix, p]
    assert checker.infer(result, g, n) == D(matrix)
    return result

def close_cases(matrix, premise, g, n, checker=EIGHT):
    # D's unused witness is inserted outside the existing closure variable.
    paired_matrix = lift_bound(matrix, 1, 1)
    d = ['di', paired_matrix, premise]
    result = ['de', Q(matrix), d, HYP(len(g))]
    assert checker.infer(result, g, n) == Q(matrix)
    return result

def naming_two(checker):
    base = intro_computational(naming(0)[0], [], 0, checker)
    matrix = naming(1)
    # Closure cases introduce z=-1, which is the forced witness of H(Sz).
    local = checker.opening(matrix, 0)
    successor_formula = checker.opening(matrix, S(-1))
    successor = intro_computational(successor_formula[0], [local], 1, checker)
    closure = close_cases(matrix, successor, [], 0, checker)
    proof = ['qe', S(S(0)), closure, base]
    goal = naming(S(S(0)))
    assert checker.infer(proof, [], 0) == goal
    return {'variables': 0, 'context': [], 'goal': goal, 'proof': proof}

# Translate raw syntax into the exact pinned repository's tagged syntax.
def tagged(a, n, d=0):
    if type(a) is int:
        if a == 0: return ['z']
        return ['v', a - 1 if a > 0 else d + n + a]
    if a[0] == 'q': return ['q', tagged(a[1], n, d + 1)]
    if len(a) == 1: return ['d', tagged(a[0], n, d + 2)]
    if len(a) == 2:
        # Caller determines equality versus successor; see term_tagged below.
        return ['=', term_tagged(a[0], n, d), term_tagged(a[1], n, d)]
    raise ValueError('formula expected')

def term_tagged(a, n, d=0):
    if type(a) is int:
        if a == 0: return ['z']
        return ['v', a - 1 if a > 0 else d + n + a]
    if len(a) == 2: return ['s', term_tagged(a[1], n, d)]
    return ['i', term_tagged(a[0], n, d), term_tagged(a[1], n, d), term_tagged(a[2], n, d + 1)]

def to_pinned(p, g, n, context_map, checker):
    tag = p[0]
    recurse = lambda q: to_pinned(q, g, n, context_map, checker)
    tt = lambda a, d=0: term_tagged(a, n, d)
    if tag == 'hyp': return ['hyp', context_map[p[1]]]
    if tag == 'zero': return ['zero', tt(p[1]), tt(p[2], 1)]
    if tag == 'succ': return ['succ', tt(p[1]), tt(p[2]), tt(p[3], 1)]
    if tag == 'tr':
        h, q, r = p[1:]
        s, t = checker.infer(q, g, n)
        _, u = checker.infer(r, g, n)
        forward = ['tr', tt(h, 1), HELP.shift(tt(u)), recurse(q), recurse(r)]
        return HELP.symm(forward, tt(checker.opening(h, t)))
    if tag == 'qe': return ['qe', tt(p[1]), recurse(p[2]), recurse(p[3])]
    new_map = [j + 1 for j in context_map] + [0]
    if tag == 'de':
        a, q, r = p[1:]
        B, = checker.infer(q, g, n)
        local = Q(checker.opening(B, -n - 1, 1))
        return ['de', tagged(a, n), recurse(q), to_pinned(r, g + [local], n + 1, new_map, checker)]
    if tag == 'di':
        B, q = p[1:]
        body = checker.opening(B, -n, 1)
        diag = len(B) == 2 and all(type(t) is list and len(t) == 3 and t[:2] == [1, 1] for t in B)
        eta = -n - 1 if checker is SEVEN and diag else 0
        local = checker.opening(body, eta)
        return ['di', tagged(B, n, 2), tt(-n), to_pinned(q, g + [local], n + 1, new_map, checker)]
    if tag == 'qi':
        B, q = p[1:]
        local = checker.opening(B, -n - 1)
        return ['qi', tagged(B, n, 1), to_pinned(q, g + [local], n + 1, new_map, checker)]
    raise ValueError(tag)

def restore_witness(p, n):
    tag = p[0]
    q = p[:]
    if tag == 'di': return ['di', p[1], -n, restore_witness(p[2], n + 1)]
    if tag == 'tr': q[2:] = [restore_witness(r, n) for r in p[2:]]
    if tag == 'qe': q[2:] = [restore_witness(r, n) for r in p[2:]]
    if tag == 'de': q[2] = restore_witness(p[2], n); q[3] = restore_witness(p[3], n + 1)
    if tag == 'qi': q[2] = restore_witness(p[2], n + 1)
    return q

def certificate(n, g, p, checker=EIGHT):
    return dict(variables=n, context=g, goal=checker.infer(p, g, n), proof=p)

def fixtures(checker):
    result = {}
    result['hypothesis'] = certificate(1, [E(-1, 0)], HYP(0), checker)
    result['zero_computation'] = certificate(1, [], ['zero', -1, 1], checker)
    result['successor_computation'] = certificate(1, [], ['succ', -1, 0, 1], checker)
    result['transport'] = certificate(1, [E(-1, 0)], congr(S(1), HYP(0), [E(-1, 0)], 1, checker), checker)
    result['reflexivity'] = certificate(2, [], refl(I(-1, -2, S(1))), checker)
    const = E(0, 0)
    result['case_introduction'] = certificate(0, [], ['di', const, HYP(0)], checker)
    result['binder_transport'] = certificate(1, [E(-1, 0)], congr(I(1, 0, S(1)), HYP(0), [E(-1, 0)], 1, checker), checker)
    result['naming_two'] = naming_two(checker)
    if checker is EIGHT:
        matrix = E(I(1, 0, 1), 0)
        local = E(I(-1, 0, 1), 0)
        step = ['succ', -1, 0, 1]
        branch = trans(step, HYP(0), [local], 1, checker)
        result['equation_induction'] = certificate(0, [], ['qi', matrix, branch], checker)
    else:
        # This checks diagonal progress dispatch with a computationally true row.
        # The separate arbitrary-equation induction lift is metatheory.
        matrix = E(I(1, 1, 1), I(1, 1, 1))
        result['diagonal_progress'] = certificate(0, [], intro_computational(matrix, [], 0, checker), checker)
    return result

def run():
    out = HERE / 'verified';out.mkdir(exist_ok=True)
    receipts = []
    for label, checker, control, pinned, filename in [
        ('eight', EIGHT, OLD_EIGHT, PINNED_EIGHT, 'checker_eight.py'),
        ('seven', SEVEN, OLD_SEVEN, PINNED_SEVEN, 'checker_seven.py')]:
        for name, doc in fixtures(checker).items():
            checker.check(doc)
            old = dict(doc, proof=restore_witness(doc['proof'], doc['variables']))
            control.check(old)
            translated = dict(variables=doc['variables'],context=[tagged(a,doc['variables']) for a in doc['context']],goal=tagged(doc['goal'],doc['variables']),proof=to_pinned(doc['proof'],doc['context'],doc['variables'],list(range(len(doc['context']))),checker))
            pinned.check(translated)
            path=out/(label+'_'+name+'.json');path.write_text(json.dumps(doc,separators=(',',':'))+'\n')
            (out/(label+'_'+name+'_pinned.json')).write_text(json.dumps(translated,separators=(',',':'))+'\n')
            for optimized in (False, True):
                proc=subprocess.run([sys.executable,*(['-O'] if optimized else []),str(HERE/filename)],input=json.dumps(doc),text=True,capture_output=True)
                assert proc.returncode==0 and proc.stdout=='ACCEPT\n',(label,name,proc.stderr)
            receipts.append(dict(calculus=label,fixture=name,source=True,matched_control=True,pinned_control=True,normal_and_optimized_cli=True))
    bad = []
    for label, checker, filename in [('eight', EIGHT, 'checker_eight.py'), ('seven', SEVEN, 'checker_seven.py')]:
        base = certificate(0, [], refl(0), checker)
        variants = {
            'boolean_scope': dict(base, variables=False),
            'negative_scope': dict(base, variables=-1),
            'boolean_goal_term': dict(base, goal=[False, False]),
            'bound_escape': dict(base, goal=[1, 1]),
            'eigen_escape': dict(base, goal=[-1, -1]),
            'extra_public_field': dict(base, extra=0),
            'bad_context': dict(base, context=False),
            'bad_proof': dict(base, proof=None),
            'boolean_term': dict(base, proof=['zero', False, 0]),
            'negative_hypothesis': dict(base, proof=['hyp', -1]),
            'boolean_hypothesis': dict(base, proof=['hyp', False]),
            'old_witness_payload': dict(base, goal=[[0, 0]], proof=['di', [0, 0], 0, ['hyp', 0]]),
            'qe_equation_major': dict(base, proof=['qe', 0, refl(0), refl(0)]),
            'de_equation_major': dict(base, proof=['de', [0, 0], refl(0), ['hyp', 0]]),
            'tr_closure_major': dict(base, context=[['q',[0,0]]], proof=['tr',1,['hyp',0],['hyp',0]]),
            'false_conclusion': dict(base, goal=[0,[0,0]]),
        }
        if label == 'seven':
            matrix = E(I(1, 0, 1), 0)
            step = ['succ', -1, 0, 1]
            local = E(I(-1, 0, 1), 0)
            branch = trans(step, HYP(0), [local], 1, EIGHT)
            variants['unguarded_progress_attack'] = dict(base, goal=D(matrix), proof=['di',matrix,branch])
        for name, doc in variants.items():
            try:
                checker.check(doc)
            except Exception:
                pass
            else:
                raise AssertionError((label, name, 'unexpected acceptance'))
            (out/(label+'_reject_'+name+'.json')).write_text(json.dumps(doc,separators=(',',':'))+'\n')
            for optimized in (False, True):
                proc = subprocess.run([sys.executable,*(['-O'] if optimized else []),str(HERE/filename)],input=json.dumps(doc),text=True,capture_output=True)
                assert proc.returncode != 0 or proc.stdout != 'ACCEPT\n', (label,name)
            bad.append(dict(calculus=label,fixture=name,rejected=True,normal_and_optimized_cli=True))
    metrics = []
    skip = {tokenize.ENCODING,tokenize.NL,tokenize.NEWLINE,tokenize.INDENT,tokenize.DEDENT,tokenize.ENDMARKER,tokenize.COMMENT}
    for filename in ['control_eight.py','checker_eight.py','control_seven.py','checker_seven.py']:
        source = (HERE/filename).read_text()
        tree = ast.parse(source)
        normalized = ast.unparse(tree)+'\n'
        assert normalized == source
        metrics.append(dict(file=filename,significant_tokens=sum(t.type not in skip for t in tokenize.generate_tokens(io.StringIO(normalized).readline)),ast_nodes=sum(1 for _ in ast.walk(tree)),normalized_bytes=len(normalized.encode())))
    summary = dict(positive_fixtures=len(receipts),positive_cli_checks=2*len(receipts),negative_fixtures=len(bad),negative_cli_checks=2*len(bad),matched_control_translations=len(receipts),pinned_control_translations=len(receipts),all_passed=True)
    (out/'verification.json').write_text(json.dumps(dict(summary=summary,positive=receipts,negative=bad,metrics=metrics),indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':run()
