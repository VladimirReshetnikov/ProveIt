import json

def require(condition):
    if not condition:
        raise ValueError('Invalid certificate')

def term(tree, scope):
    if type(tree) is int:
        return tree == 0
    if type(tree) is not list or not tree:
        return False
    if tree[0] == 'v' and len(tree) == 2:
        return type(tree[1]) is int and 0 <= tree[1] < scope
    if tree[0] == 's' and len(tree) == 2:
        return term(tree[1], scope)
    return tree[0] == 'i' and len(tree) == 4 and term(tree[1], scope) and term(tree[2], scope) and term(tree[3], scope + 1)

def formula(tree, scope):
    if type(tree) is not list or not tree:
        return False
    if tree[0] == '=' and len(tree) == 3:
        return term(tree[1], scope) and term(tree[2], scope)
    return len(tree) == 2 and tree[0] in ('q', 'd') and formula(tree[1], scope + (1 if tree[0] == 'q' else 2))

def map_variables(tree, action, depth=0):
    if type(tree) is int:
        return tree
    tag, *args = tree
    if tag == 'v':
        return action(args[0], depth)
    if tag == 's':
        return [tag, map_variables(args[0], action, depth)]
    if tag == 'i':
        return [tag, map_variables(args[0], action, depth), map_variables(args[1], action, depth), map_variables(args[2], action, depth + 1)]
    if tag == '=':
        return [tag, map_variables(args[0], action, depth), map_variables(args[1], action, depth)]
    return [tag, map_variables(args[0], action, depth + (1 if tag == 'q' else 2))]

def lift(tree, amount=1, cutoff=0):
    return map_variables(tree, lambda index, depth: ['v', index + amount if index >= cutoff + depth else index])

def substitute(tree, index, value):

    def replace(variable, depth):
        if variable == index + depth:
            return lift(value, depth)
        return ['v', variable - (variable > index + depth)]
    return map_variables(tree, replace)

def instance(matrix, value):
    return substitute(matrix, 0, value)

def fresh_instance(matrix, value):
    return instance(lift(matrix, cutoff=1), value)

def derive(proof, context=(), scope=0):
    require(type(proof) is list and proof)
    rule, *args = proof
    if rule == 'hyp':
        index, = args
        require(type(index) is int and 0 <= index < len(context))
        return context[index]
    if rule == 'zero':
        seed, body = args
        require(term(seed, scope) and term(body, scope + 1))
        return ['=', ['i', 0, seed, body], seed]
    if rule == 'succ':
        counter, seed, body = args
        require(term(counter, scope) and term(seed, scope) and term(body, scope + 1))
        return ['=', ['i', ['s', counter], seed, body], instance(body, ['i', counter, seed, body])]
    if rule == 'tr':
        matrix, major, minor = args
        require(formula(matrix, scope + 1) and matrix[0] == '=')
        equality = derive(major, context, scope)
        require(equality[0] == '=')
        require(derive(minor, context, scope) == instance(matrix, equality[1]))
        return instance(matrix, equality[2])
    if rule == 'use':
        target, major, minor = args
        require(term(target, scope))
        closure = derive(major, context, scope)
        require(closure[0] == 'q')
        matrix = closure[1]
        require(derive(minor, context, scope) == instance(matrix, 0))
        return instance(matrix, target)
    if rule == 'elim':
        conclusion, major, continuation = args
        require(formula(conclusion, scope))
        paired = derive(major, context, scope)
        require(paired[0] == 'd')
        local = (['q', paired[1]],) + tuple((lift(item) for item in context))
        require(derive(continuation, local, scope + 1) == lift(conclusion))
        return conclusion
    if rule == 'intro':
        matrix, witness, premise = args
        require(formula(matrix, scope + 2) and term(witness, scope))
        body = substitute(matrix, 1, lift(witness))
        source = ['v', 0] if body[0] == '=' and witness == 0 else 0
        local = (fresh_instance(body, source),) + tuple((lift(item) for item in context))
        require(derive(premise, local, scope + 1) == fresh_instance(body, ['s', ['v', 0]]))
        return ['d', matrix]
    raise ValueError('Unknown inference rule')

def check(data):
    require(type(data) is dict and set(data) == {'goal', 'proof'})
    require(formula(data['goal'], 0))
    require(derive(data['proof']) == data['goal'])
if __name__ == '__main__':
    check(json.load(open(0)))
    print('ACCEPT')
