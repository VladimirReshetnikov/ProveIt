import json
import sys

def fail():
    raise ValueError('invalid certificate')

def rec(n, a, h):
    return [n, a, 0 if n == 0 else h]

def successor(a):
    return [0, a, 0]

def term(t, n):
    if type(t) is int:
        return 0 <= t <= n
    if type(t) is not list:
        return False
    return len(t) == 3 and term(t[0], n) and term(t[1], n) and term(t[2], n + 1) and (t[0] != 0 or t[2] == 0)

def formula(a, n):
    if type(a) is not list or not a:
        return False
    if a[0] == '=':
        return len(a) == 3 and term(a[1], n) and term(a[2], n)
    return len(a) == 2 and a[0] == 'D' and formula(a[1], n + 2)

def shift_term(t, amount=1, depth=0):
    if type(t) is int:
        return t + amount if t > depth else t
    return rec(shift_term(t[0], amount, depth), shift_term(t[1], amount, depth), shift_term(t[2], amount, depth + 1))

def shift_formula(a, amount=1, depth=0):
    if a[0] == '=':
        return ['=', shift_term(a[1], amount, depth), shift_term(a[2], amount, depth)]
    return ['D', shift_formula(a[1], amount, depth + 2)]

def subst_term(t, images, depth=0):
    if type(t) is int:
        if t <= depth:
            return t
        index = t - depth
        return shift_term(images[index - 1], depth) if index <= len(images) else t - len(images)
    return rec(subst_term(t[0], images, depth), subst_term(t[1], images, depth), subst_term(t[2], images, depth + 1))

def subst_formula(a, images, depth=0):
    if a[0] == '=':
        return ['=', subst_term(a[1], images, depth), subst_term(a[2], images, depth)]
    return ['D', subst_formula(a[1], images, depth + 2)]

def derive(proof, context, scope):
    if type(proof) is not list or not proof or type(proof[0]) is not str:
        fail()
    tag = proof[0]
    if tag == 'u' and len(proof) == 4:
        index, witness, premise = proof[1:]
        if type(index) is not int or not 0 <= index < len(context) or (not term(witness, scope)):
            fail()
        antecedent, body = context[index]
        if derive(premise, context, scope) != antecedent:
            fail()
        return subst_formula(body, [witness])
    if tag == 'r' and len(proof) == 4:
        n, a, h = proof[1:]
        if not (term(n, scope) and term(a, scope) and term(h, scope + 1)):
            fail()
        return ['=', rec(successor(n), a, h), subst_term(h, [rec(n, a, h)])]
    if tag == 'x' and len(proof) == 4:
        template, major, minor = proof[1:]
        if not term(template, scope + 1):
            fail()
        equation = derive(major, context, scope)
        instance = derive(minor, context, scope)
        if equation[0] != '=' or instance[0] != '=' or instance[1] != subst_term(template, [equation[1]]):
            fail()
        return ['=', instance[2], subst_term(template, [equation[2]])]
    if tag in ('e', 'i') and len(proof) == 4:
        goal, data, branch = proof[1:]
        if not formula(goal, scope):
            fail()
        extended = [(shift_formula(a), shift_formula(b, depth=1)) for a, b in context]
        if tag == 'e':
            paired = derive(data, context, scope)
            if paired[0] != 'D':
                fail()
            extended.append((subst_formula(paired[1], [0]), paired[1]))
            target = shift_formula(goal)
        else:
            if goal[0] != 'D' or not term(data, scope):
                fail()
            body = shift_formula(goal[1], 1, 2)
            witness = shift_term(data)
            eta = 1 if goal[1][0] == '=' and data == 0 else 0
            hypothesis = subst_formula(body, [eta, witness])
            extended.append((['=', [[0, 0, 0], 0, 0], 0], shift_formula(hypothesis)))
            target = subst_formula(body, [successor(1), witness])
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
