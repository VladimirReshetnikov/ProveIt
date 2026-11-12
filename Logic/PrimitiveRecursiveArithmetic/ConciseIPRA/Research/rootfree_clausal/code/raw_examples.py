"""Inherited substantive examples from ipra_raw_clausal/tests/verify.py.
Frozen at repository 831081033253cca2115196cf86bb99c77ed2aeae.
Only extracted into a return-value function; no expected conclusions changed.
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent / 'reference'))
import matched_control as old
from translate import old_refl, old_sym, old_trans, translate


def certificate(proof):
    return {'goal':old.derive(proof,[],0),'proof':proof}


def examples():
    examples = {}
    terms = [0, [0, 0], [0, [0, 0]], [0, 0, 1],
             [[0, 0], 0, [0, 1]], [0, [0, 0], [1, 0, 2]]]
    for i, t in enumerate(terms):
        examples[f'reflexivity_{i}'] = certificate(old_refl(t))
        examples[f'zero_computation_{i}'] = certificate(['z', t, [0, 1]])
    bodies = [0, 1, [0, 1], [1, 0, 2], [0, 1, [2, 1, [0, 2]]]]
    for i, h in enumerate(bodies):
        examples[f'successor_computation_{i}'] = certificate(['s', 0, 0, h])
        major = ['z', 0, h]
        s, t = old.derive(major, [], 0)
        minor = old_refl(old.opening(h, s))
        examples[f'template_congruence_{i}'] = certificate(['x', h, major, minor])
    major = old_sym(['z', 0, 1], [], 0)
    template = [1, 1, [2, 1, [0, 2]]]
    minor = old_refl(old.opening(template, 0))
    examples['zero_source_nested_template'] = certificate(['x', template, major, minor])

    # E(y) is I(y,0;u.u)=0. Its actual induction assumption is used.
    matrix = [[1, 0, 1], 0]
    paired = [matrix]
    context = [([0, 0], [[-1, 0, 1], 0])]
    hypothesis = ['u', 0, 0, old_refl(0)]
    computation = ['s', -1, 0, 1]
    step = old_trans(computation, hypothesis, context, 1)
    induction = ['i', paired, 0, step]
    examples['used_induction_hypothesis'] = certificate(induction)
    for i, t in enumerate(terms):
        target = [[t, 0, 1], 0]
        branch = ['u', 0, t, ['z', 0, 1]]
        examples[f'closure_specialization_{i}'] = certificate(['e', target, induction, branch])

    # The outer y remains bound beneath an inner D, hence index 3.
    nested_goal = [[[3, 3]]]
    inner_goal = [[[0, -1], [0, -1]]]
    inner = ['i', inner_goal, [0, 0], old_refl([0, -1])]
    examples['nested_compound_binders'] = certificate(['i', nested_goal, 0, inner])

    # A witness with an internally bound variable is inserted beneath I.
    witness = [[0, 0], 0, [0, 1]]
    goal = [[[1, 2, 3], 2]]
    examples['capture_avoiding_witness'] = certificate(
        ['i', goal, witness, ['s', -1, witness, witness]])

    return {name:translate(c) for name,c in examples.items()}
