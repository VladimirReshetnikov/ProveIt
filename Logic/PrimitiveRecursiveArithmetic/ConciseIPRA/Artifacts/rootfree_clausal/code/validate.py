"""Finite validation of the clausal uniform-evaluation composition.

This is a regression suite and certificate producer, not a formal proof.
The normal certificates are also translated to the separately implemented,
inherited tagged six-rule checker and checked there.
"""
import ast
import copy
import importlib.util
import io
import json
import pathlib
import random
import subprocess
import sys
import tokenize

ROOT = pathlib.Path(__file__).resolve().parent


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


new = load('uniform', ROOT / 'checker.py')
native = load('native', ROOT / 'reference/native_normal.py')


def S(t):
    return [0, t]


def I(n, a, h):
    return a if n == 0 else [n, a, h]


def numeral(n):
    a = 0
    for _ in range(n):
        a = S(a)
    return a


def R(a):
    return ['r', a]


def EV(p, q):
    return ['v', p, q]


def identity_root(p, q, s):
    return EV(p, EV(q, R(I(S(0), s, 1))))


def symmetry(p, s):
    return identity_root(R(s), p, s)


def transitivity(p, q, s, t):
    return identity_root(q, symmetry(p, s), t)


def congruence(h, p, s):
    frame = I(S(0), s, h)
    first = EV(R(s), R(frame))
    second = EV(p, R(frame))
    return identity_root(second, first, frame)


def native_term(t, scope, depth=0):
    if type(t) is int:
        return ['z'] if t == 0 else ['v', t-1 if t > 0 else depth+scope+t]
    if len(t) == 2:
        return ['s', native_term(t[1], scope, depth)]
    return ['i', native_term(t[0], scope, depth), native_term(t[1], scope, depth), native_term(t[2], scope, depth+1)]


def native_formula(f, scope, depth=0):
    if len(f) == 1:
        return ['d', native_formula(f[0], scope, depth+2)]
    return ['=', native_term(f[0], scope, depth), native_term(f[1], scope, depth)]


def to_native(p, context=(), kinds=(), scope=0):
    tag = p[0]
    if tag == 'r':
        return ['refl', native_term(p[1], scope)]
    if tag == 'v':
        return ['ev', to_native(p[1], context, kinds, scope), to_native(p[2], context, kinds, scope)]
    if tag == 'u':
        i, t, premise = p[1:]
        hyp = ['hyp', len(context)-1-i]
        if kinds[i] == 'ordinary':
            return hyp
        return ['qe', native_term(t, scope), hyp, to_native(premise, context, kinds, scope)]
    goal, data, branch = p[1:]
    fresh = -scope-1
    if tag == 'e':
        paired = new.derive(data, list(context), scope)
        body = new.opening(paired[0], fresh, 1)
        clause = (new.opening(body, 0), body)
        return ['de', native_formula(goal, scope), to_native(data, context, kinds, scope),
                to_native(branch, context+(clause,), kinds+('closure',), scope+1)]
    body = new.opening(goal[0], data, 1)
    eta = fresh if len(goal[0]) == 2 and data == 0 else 0
    clause = ([0, 0], new.opening(body, eta))
    return ['di', native_formula(goal[0], scope, 2), native_term(data, scope),
            to_native(branch, context+(clause,), kinds+('ordinary',), scope+1)]


def certificate(p):
    goal = new.derive(p, [], 0)
    return {'goal': goal, 'proof': p}


def positives():
    tests = {}
    def add(name, p):
        tests[name] = certificate(p)
    add('zero_reflexivity', R(0))
    add('successor_reflexivity', R(S(0)))
    add('one_successor_computation', EV(R(0), R(I(S(0), 0, S(1)))))
    b = I(S(0), 0, S(1))
    p = EV(R(0), R(b))
    add('symmetry', symmetry(p, b))
    add('transitivity', transitivity(p, symmetry(p, b), b, S(0)))
    add('root_composition', identity_root(p, R(b), b))
    h = I(S(0), 1, I(S(0), 2, S(3)))
    add('nested_multiple_occurrence_congruence', congruence(h, p, b))
    # The open induction step actually uses the local induction hypothesis.
    E = [I(1, 0, S(1)), 1]
    branch = EV(['u', 0, 0, R(0)], R(I(S(-1), 0, S(1))))
    induction = ['i', [E], 0, branch]
    add('used_equation_induction', induction)
    for n in (0, 1, 3):
        t = numeral(n)
        goal = [I(t, 0, S(1)), t]
        add('closure_specialization_'+str(n), ['e', goal, induction, ['u', 0, t, R(0)]])
    inner = [[2, 2]]
    # Outer D introduces a compound matrix; its constant ordinary clause is used.
    goal = [inner]
    add('nested_compound_case', ['i', goal, S(0), ['u', 0, 0, R(0)]])
    # Compound hypothesis obtained by D elimination, including an unused witness.
    nested = tests['nested_compound_case']['proof']
    # Obtain an ordinary true inner formula by direct introduction, to seed closure.
    base = ['i', inner, 0, R(0)]
    add('compound_closure_specialization', ['e', inner, nested, ['u', 0, 0, base]])
    # Binder opening creates a literal-zero counter, which must contract.
    # D_{x,y}(I(x,0;u.u)=0), witnessed by zero, has reflexive instances.
    normalization_goal = [[[2, 0, 1], 0]]
    add('witness_opening_zero_contraction', ['i', normalization_goal, 0, R(0)])
    # Nested term body, where the iterator update binds one more index.
    nested_goal = [[[S(0), 0, [2, 0, 1]], 0]]
    # At y=S(z), this reduces one iteration whose body has nonzero counter.
    # A standalone direct arithmetic instance exercises the same opening.
    a = I(S(0), 0, I(1, S(0), 1))
    add('body_substitution_zero_contraction', EV(R(0), R(a)))
    return tests


def negatives(good):
    tests = {}
    base = copy.deepcopy(good['zero_reflexivity'])
    def add(name, obj):
        tests[name] = obj
    add('boolean_goal_term', {'goal': [True, True], 'proof': R(True)})
    add('zero_counter_in_goal', {'goal': [[0, 0, 1], 0], 'proof': R(0)})
    add('zero_counter_in_refl', {'goal': [0, 0], 'proof': R([0, 0, 1])})
    add('free_variable_escape', {'goal': [-1, -1], 'proof': R(-1)})
    add('unbound_positive', {'goal': [1, 1], 'proof': R(1)})
    add('wrong_successor_tag', {'goal': [[1, 0], [1, 0]], 'proof': R([1, 0])})
    add('forged_root_eval', {'goal': [0, 0], 'proof': EV(R(0), R(0))})
    add('forged_predecessor_eval', {'goal': [S(0), 0], 'proof': EV(R(S(0)), R(I(S(0), 0, 1)))})
    add('wrong_final_goal', {'goal': [0, S(0)], 'proof': R(0)})
    add('extra_top_level_field', dict(base, extra=0))
    add('wrong_proof_arity', {'goal': [0, 0], 'proof': ['r', 0, 0]})
    add('unknown_rule', {'goal': [0, 0], 'proof': ['unknown']})
    add('empty_context_use', {'goal': [0, 0], 'proof': ['u', 0, 0, R(0)]})
    add('bool_context_index', {'goal': [[[0, 0]]], 'proof': ['i', [[[0, 0]]], 0, ['u', True, 0, R(0)]]})
    t = copy.deepcopy(good['used_equation_induction'])
    t['proof'][3][1][1] = -1
    add('negative_context_index', t)
    t = copy.deepcopy(good['used_equation_induction'])
    t['proof'][2] = -1
    add('escaping_di_witness', t)
    t = copy.deepcopy(good['closure_specialization_3'])
    t['proof'][3][3] = R(S(0))
    add('wrong_clause_antecedent', t)
    t = copy.deepcopy(good['closure_specialization_3'])
    t['proof'][1] = [-1, -1]
    t['goal'] = [-1, -1]
    add('de_eigenvariable_escape', t)
    # Under a compound matrix, the primitive branch receives its zero instance.
    # This mutant tries to use a fresh-variable progressive hypothesis instead.
    matrix = [[[3, 3], [0, 0], 1]]
    add('malformed_compound_matrix', {'goal': [matrix], 'proof': ['i', [matrix], 0, R(0)]})
    bad_counter = I(S(0), 0, 1)
    s = I(0, 0, S(1))
    b = I(bad_counter, 0, S(1))
    add('iterator_counter_is_not_successor', {'goal':[b,S(s)],'proof':EV(R(s),R(b))})
    b_at_successor = [[S(-1), S(-1)]]
    local_equality = ['u', 1, 0, R(-1)]
    lifted = congruence(S(1), local_equality, -1)
    progressive_branch = ['e',b_at_successor,['u',0,0,R(0)],['i',b_at_successor,0,lifted]]
    if new.derive(progressive_branch, [([0,0],[[-1,-1]])], 1) != b_at_successor:
        raise RuntimeError('invalid compound-progress adversary')
    add('compound_progress_is_not_primitive', {'goal':[[[3,3]]], 'proof':['i',[[[3,3]]],0,progressive_branch]})
    for malformed in (None, [], 0, False, {'goal': [0,0]}, {'proof':R(0)}):
        add('malformed_'+str(len(tests)), malformed)
    return tests


def opening_checks():
    """Compare free-level opening to the independent de Bruijn implementation."""
    rng=random.Random(20261111)
    def term(scope,depth,budget):
        atoms=[0]+list(range(-scope,0))+list(range(1,depth+1))
        if budget == 0 or rng.randrange(4)==0:
            return rng.choice(atoms)
        if rng.randrange(3)==0:
            return S(term(scope,depth,budget-1))
        return I(term(scope,depth,budget-1),term(scope,depth,budget-1),term(scope,depth+1,budget-1))
    def formula(scope,depth,budget):
        if budget and rng.randrange(3)==0:
            return [formula(scope,depth+2,budget-1)]
        return [term(scope,depth,budget),term(scope,depth,budget)]
    count=0
    for _ in range(2000):
        scope=rng.randrange(4)
        witness=term(scope,0,3)
        body=term(scope,1,3)
        a=native_term(new.opening(body,witness),scope)
        b=native.sub(native_term(body,scope,1),native_term(witness,scope))
        if a!=b:raise RuntimeError('term opening mismatch')
        matrix=formula(scope,1,3)
        a=native_formula(new.opening(matrix,witness),scope)
        b=native.sub(native_formula(matrix,scope,1),native_term(witness,scope))
        if a!=b:raise RuntimeError('formula opening mismatch')
        matrix=formula(scope,2,3)
        a=native_formula(new.opening(matrix,witness,1),scope,1)
        b=native.sub(['q',native_formula(matrix,scope,2)],native_term(witness,scope))[1]
        if a!=b:raise RuntimeError('outer witness opening mismatch')
        count+=3
    return count


def run():
    pos = positives()
    neg = negatives(pos)
    out = ROOT/'certificates'
    out.mkdir(exist_ok=True)
    results=[]
    for name, c in pos.items():
        new.verify(c)
        translated={'variables':0,'context':[],'goal':native_formula(c['goal'],0),'proof':to_native(c['proof'])}
        native.check(translated)
        (out/(name+'.json')).write_text(json.dumps(c,indent=2)+'\n')
        (out/(name+'.native.json')).write_text(json.dumps(translated,indent=2)+'\n')
    for name,c in neg.items():
        try:
            new.verify(c)
        except Exception:
            pass
        else:
            raise RuntimeError('unexpected accept '+name)
    for name,c in list(pos.items())+list(neg.items()):
        expected=name in pos
        for flag in ([],['-O']):
            run=subprocess.run([sys.executable,*flag,str(ROOT/'checker.py')],input=json.dumps(c),text=True,capture_output=True)
            ok=run.returncode==0 and run.stdout.strip()=='ACCEPT'
            if ok!=expected:
                raise RuntimeError((name,flag,run.returncode,run.stdout,run.stderr))
            results.append({'case':name,'optimized':bool(flag),'accepted':ok})
    report={'positive_certificates':len(pos),'negative_certificates':len(neg),'native_translations':len(pos),'independent_opening_checks':opening_checks(),'process_checks':len(results),'unexpected_outcomes':0,'details':results}
    (ROOT/'validation.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='details'},indent=2))


if __name__=='__main__':
    run()
