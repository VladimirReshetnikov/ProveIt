import json
import sys

def fail():
    raise ValueError('invalid certificate')

def rec(n, a, h):
    return [n, a, h]

def successor(a):
    return [a]

def term(t, n):
    if type(t) is int:
        return 0 <= t <= n
    if type(t) is not list:
        return False
    if len(t) == 1:
        return term(t[0], n)
    return len(t) == 3 and term(t[0], n) and term(t[1], n) and term(t[2], n + 1)

def formula(a, n):
    if type(a) is not list or not a:
        return False
    if a[0] == '=':
        return len(a) == 3 and term(a[1], n) and term(a[2], n)
    return len(a) == 2 and a[0] in ('Q', 'D') and formula(a[1], n + (1 if a[0] == 'Q' else 2))

def shift_term(t, amount=1, depth=0):
    if type(t) is int:
        return t + amount if t > depth else t
    if len(t) == 1:
        return [shift_term(t[0], amount, depth)]
    return rec(shift_term(t[0], amount, depth), shift_term(t[1], amount, depth), shift_term(t[2], amount, depth + 1))

def shift_formula(a, amount=1, depth=0):
    if a[0] == '=':
        return ['=', shift_term(a[1], amount, depth), shift_term(a[2], amount, depth)]
    return [a[0], shift_formula(a[1], amount, depth + (1 if a[0] == 'Q' else 2))]

def subst_term(t, images, depth=0):
    if type(t) is int:
        if t <= depth:
            return t
        index = t - depth
        return shift_term(images[index - 1], depth) if index <= len(images) else t - len(images)
    if len(t) == 1:
        return [subst_term(t[0], images, depth)]
    return rec(subst_term(t[0], images, depth), subst_term(t[1], images, depth), subst_term(t[2], images, depth + 1))

def subst_formula(a, images, depth=0):
    if a[0] == '=':
        return ['=', subst_term(a[1], images, depth), subst_term(a[2], images, depth)]
    return [a[0], subst_formula(a[1], images, depth + (1 if a[0] == 'Q' else 2))]

def reverse(a):
    return ['=', a[2], a[1]] if a[0] == '=' else a

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
        if not (term(n, scope) and term(a, scope) and term(h, scope + 1)):
            fail()
        return ['=', rec(successor(n), a, h), subst_term(h, [rec(n, a, h)])]
    if tag == 'z' and len(proof) == 3:
        a, h = proof[1:]
        if not (term(a, scope) and term(h, scope + 1)):
            fail()
        return ['=', rec(0, a, h), a]
    if tag == 'x' and len(proof) == 4:
        template, major, minor = proof[1:]
        if not formula(template, scope + 1) or template[0] != '=':
            fail()
        equation = derive(major, context, scope)
        if equation[0] != '=' or equation[1] == 0:
            fail()
        if derive(minor, context, scope) != subst_formula(template, [equation[1]]):
            fail()
        return reverse(subst_formula(template, [equation[2]]))
    if tag == 'q' and len(proof) == 4:
        witness, major, base = proof[1:]
        if not term(witness, scope):
            fail()
        closure = derive(major, context, scope)
        if closure[0] != 'Q':
            fail()
        if derive(base, context, scope) != subst_formula(closure[1], [0]):
            fail()
        return reverse(subst_formula(closure[1], [witness]))
    if tag == 'e' and len(proof) == 4:
        goal, major, branch = proof[1:]
        if not formula(goal, scope):
            fail()
        paired = derive(major, context, scope)
        if paired[0] != 'D':
            fail()
        extended = [shift_formula(a) for a in context] + [['Q', paired[1]]]
        if derive(branch, extended, scope + 1) != shift_formula(goal):
            fail()
        return goal
    if tag == 'i' and len(proof) == 4:
        goal, witness, branch = proof[1:]
        if not formula(goal, scope) or goal[0] != 'D' or (not term(witness, scope)):
            fail()
        body = shift_formula(goal[1], 1, 2)
        lifted_witness = shift_term(witness)
        eta = 1 if goal[1][0] == '=' and witness == 0 else 0
        hypothesis = subst_formula(body, [eta, lifted_witness])
        target = subst_formula(body, [successor(1), lifted_witness])
        extended = [shift_formula(a) for a in context] + [hypothesis]
        if derive(branch, extended, scope + 1) != target:
            fail()
        return goal
    fail()

def verify(data):
    if type(data) is not dict or set(data) != {'goal', 'proof'}:
        fail()
    if not formula(data['goal'], 0):
        fail()
    if derive(data['proof'], [], 0) != data['goal']:
        fail()
    return True
if __name__ == '__main__':
    try:
        verify(json.load(sys.stdin))
    except Exception:
        print('REJECT')
        sys.exit(1)
    print('ACCEPT')
