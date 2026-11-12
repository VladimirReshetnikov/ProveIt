"""Build a matched six-rule control with the new local-variable representation."""
from pathlib import Path

root = Path(__file__).resolve().parents[1]
source = (root / 'code/arity_checker.py').read_text()
source = source[source.index('import json'):]
source = source.replace("def formula(a, scope, depth=0):\n    return", "def formula(a, scope, depth=0):\n    if type(a) is list and len(a) == 2 and a[0] == 'Q':\n        return formula(a[1], scope, depth + 1)\n    return")
source = source.replace('    size = len(a)\n', "    if len(a) == 2 and a[0] == 'Q':\n        return ['Q', opening(a[1], value, depth + 1)]\n    size = len(a)\n")
start = source.index('def derive(')
end = source.index('\ndef verify(')
derive = '''def reverse(a):
    return [a[1], a[0]] if len(a) == 2 and a[0] != 'Q' else a


def derive(proof, context, scope):
    if type(proof) is not list or not proof or type(proof[0]) is not str:
        fail()
    tag = proof[0]
    if tag == 'h' and len(proof) == 2:
        index = proof[1]
        if type(index) is int and 0 <= index < len(context):
            return context[index]
        fail()
    if tag == 'r' and len(proof) == 4:
        n, a, h = proof[1:]
        if not (term(n, scope) and term(a, scope) and term(h, scope, 1)):
            fail()
        return [[successor(n), a, h], opening(h, rec(n, a, h))]
    if tag == 'x' and len(proof) == 4:
        template, major, minor = proof[1:]
        if (not formula(template, scope, 1) or len(template) != 2
                or template[0] == 'Q'):
            fail()
        equation = derive(major, context, scope)
        if len(equation) != 2 or equation[0] == 'Q' or equation[0] == 0:
            fail()
        if derive(minor, context, scope) != opening(template, equation[0]):
            fail()
        return reverse(opening(template, equation[1]))
    if tag == 'q' and len(proof) == 4:
        witness, major, base = proof[1:]
        if not term(witness, scope):
            fail()
        closure = derive(major, context, scope)
        if len(closure) != 2 or closure[0] != 'Q':
            fail()
        if derive(base, context, scope) != opening(closure[1], 0):
            fail()
        return reverse(opening(closure[1], witness))
    if tag in ('e', 'i') and len(proof) == 4:
        goal, data, branch = proof[1:]
        if not formula(goal, scope):
            fail()
        fresh = -scope - 1
        if tag == 'e':
            paired = derive(data, context, scope)
            if len(paired) != 1:
                fail()
            assumption = ['Q', opening(paired[0], fresh, 1)]
            target = goal
        else:
            if len(goal) != 1 or not term(data, scope):
                fail()
            body = opening(goal[0], data, 1)
            eta = fresh if len(goal[0]) == 2 and goal[0][0] != 'Q' and data == 0 else 0
            assumption = opening(body, eta)
            target = opening(body, successor(fresh))
        if derive(branch, context + [assumption], scope + 1) != target:
            fail()
        return goal
    fail()

'''
source = source[:start] + derive + source[end:]
(root / 'comparison').mkdir(exist_ok=True)
(root / 'comparison/arity_current_control.py').write_text(source)
