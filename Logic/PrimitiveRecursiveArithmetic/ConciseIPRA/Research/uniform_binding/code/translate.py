"""Untrusted, checked proof recoding between the inherited forward checker
and the uniform-binder goal checker. Both recodings preserve the goal literally.

Usage: python3 code/translate.py forward|reverse INPUT.json OUTPUT.json
"""
import importlib.util
import json
from pathlib import Path
import sys


HERE = Path(__file__).resolve().parent.parent


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


old = load('inherited_counter', HERE / 'reference/counter_forward.py')
new = load('uniform_counter', HERE / 'code/checker.py')


def introduced(goal, witness, g, n):
    body = old.opening(goal[0], witness, 1)
    eta = -n - 1 if len(goal[0]) == 2 and witness == 0 else 0
    hypothesis = old.opening(body, eta)
    target = old.opening(body, [0, -n - 1, 0])
    return target, g + [([0, 0], hypothesis)]


def eliminated(matrix, g, n):
    body = old.opening(matrix, -n - 1, 1)
    return g + [(old.opening(body, 0), body)]


def forward_node(p, g, n):
    tag = p[0]
    if tag == 'r':
        return [p[1], p[1]], None
    if tag == 'v':
        eq1, proof1 = forward_node(p[1], g, n)
        eq2, proof2 = forward_node(p[2], g, n)
        s, t = eq1
        (counter, seed, body), r = eq2
        assert counter == [0, s, 0]
        value = old.opening(old.opening(body, old.rec(t, seed, body)), t)
        return [r, value], ['v', s, t, seed, body, proof1, proof2]
    if tag == 'u':
        _, index, witness, premise = p
        antecedent, body = g[index]
        premise_goal, premise_proof = forward_node(premise, g, n)
        assert premise_goal == antecedent
        return old.opening(body, witness), ['u', index, witness, premise_proof]
    if tag == 'e':
        _, goal, major, branch = p
        paired, major_proof = forward_node(major, g, n)
        context = eliminated(paired[0], g, n)
        branch_goal, branch_proof = forward_node(branch, context, n + 1)
        assert branch_goal == goal
        return goal, ['e', paired[0], major_proof, branch_proof]
    if tag == 'i':
        _, goal, witness, branch = p
        target, context = introduced(goal, witness, g, n)
        branch_goal, branch_proof = forward_node(branch, context, n + 1)
        assert branch_goal == target
        return goal, ['i', witness, branch_proof]
    raise ValueError('unknown inherited instruction')


def reverse_node(a, p, g, n):
    if len(a) == 2 and a[0] == a[1]:
        return ['r', a[0]]
    tag = p[0]
    if tag == 'v':
        _, s, t, seed, body, major, minor = p
        return ['v', reverse_node([s, t], major, g, n),
                reverse_node([[[0, s, 0], seed, body], a[0]], minor, g, n)]
    if tag == 'u':
        _, index, witness, premise = p
        antecedent, _ = g[index]
        return ['u', index, witness, reverse_node(antecedent, premise, g, n)]
    if tag == 'e':
        _, matrix, major, branch = p
        context = eliminated(matrix, g, n)
        return ['e', a, reverse_node([matrix], major, g, n),
                reverse_node(a, branch, context, n + 1)]
    if tag == 'i':
        _, witness, branch = p
        target, context = introduced(a, witness, g, n)
        return ['i', a, witness, reverse_node(target, branch, context, n + 1)]
    raise ValueError('unknown target instruction')


def forward(certificate):
    old.verify(certificate)
    goal, proof = forward_node(certificate['proof'], [], 0)
    assert goal == certificate['goal']
    result = {'goal': goal, 'proof': proof}
    new.check(result)
    return result


def reverse(certificate):
    new.check(certificate)
    result = {'goal': certificate['goal'],
              'proof': reverse_node(certificate['goal'], certificate['proof'], [], 0)}
    old.verify(result)
    return result


if __name__ == '__main__':
    direction, source, destination = sys.argv[1:]
    certificate = json.loads(Path(source).read_text())
    result = {'forward': forward, 'reverse': reverse}[direction](certificate)
    Path(destination).write_text(json.dumps(result, indent=2) + '\n')
