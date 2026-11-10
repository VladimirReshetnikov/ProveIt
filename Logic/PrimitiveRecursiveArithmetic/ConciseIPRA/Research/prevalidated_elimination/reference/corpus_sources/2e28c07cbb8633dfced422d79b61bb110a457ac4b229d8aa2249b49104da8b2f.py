# Matched scalar Choice-DI baseline: ordinary I0/IS and full formula transport.
import json


def require(condition):
    if not condition:
        raise ValueError('invalid proof')


def variable(value):
    return type(value) is str and value.isidentifier()


def free(expression):
    if type(expression) is str:
        return {expression}
    if type(expression) is int:
        return set()
    tag = expression[0]
    if tag == 'I':
        return free(expression[1]) | free(expression[2]) | (free(expression[4]) - {expression[3]})
    if tag == 'Q':
        return free(expression[2]) - {expression[1]}
    if tag == 'D':
        return free(expression[3]) - {expression[1], expression[2]}
    return set().union(*(free(child) for child in expression[1:]))


def names(expression):
    if type(expression) is str:
        return {expression}
    if type(expression) is int:
        return set()
    return set().union(*(names(child) for child in expression[1:]))


def substitute(expression, name, image):
    """Capture-free substitution with deterministic binder renaming."""
    if type(expression) is str:
        return image if expression == name else expression
    if type(expression) is int:
        return expression
    tag = expression[0]
    if tag in ('I', 'Q', 'D'):
        if tag == 'I':
            prefix = ['I', substitute(expression[1], name, image),
                      substitute(expression[2], name, image)]
            binders = [expression[3]]
            body = expression[4]
        elif tag == 'Q':
            prefix, binders, body = ['Q'], [expression[1]], expression[2]
        else:
            prefix, binders, body = ['D'], expression[1:3], expression[3]
        if name not in binders and name in free(body):
            occupied = names(body) | names(image) | set(binders) | {name}
            for index, binder in enumerate(binders):
                if binder in free(image):
                    number = 0
                    while '_b' + str(number) in occupied:
                        number += 1
                    fresh = '_b' + str(number)
                    occupied.add(fresh)
                    body = substitute(body, binder, fresh)
                    binders[index] = fresh
            body = substitute(body, name, image)
        return prefix + binders + [body]
    return [tag, *(substitute(child, name, image) for child in expression[1:])]


def key(expression, environment=()):
    """Alpha-invariant key with free variable names preserved."""
    if type(expression) is str:
        return ('bound', environment[::-1].index(expression)) if expression in environment else ('free', expression)
    if type(expression) is int:
        return expression
    tag = expression[0]
    if tag == 'I':
        return ('I', key(expression[1], environment), key(expression[2], environment),
                key(expression[4], (*environment, expression[3])))
    if tag == 'Q':
        return ('Q', key(expression[2], (*environment, expression[1])))
    if tag == 'D':
        return ('D', key(expression[3], (*environment, *expression[1:3])))
    return (tag, *(key(child, environment) for child in expression[1:]))


def same(left, right):
    return key(left) == key(right)


def term(value, scope):
    if type(value) is int:
        require(value == 0)
    elif type(value) is str:
        require(variable(value) and value in scope)
    else:
        require(type(value) is list and len(value) > 0)
        if value[0] == 'S':
            require(len(value) == 2)
            term(value[1], scope)
        else:
            require(value[0] == 'I' and len(value) == 5)
            _, counter, seed, binder, update = value
            require(variable(binder))
            term(counter, scope)
            term(seed, scope)
            term(update, scope | {binder})


def formula(value, scope):
    require(type(value) is list and len(value) > 0)
    if value[0] == '=':
        require(len(value) == 3)
        term(value[1], scope)
        term(value[2], scope)
    elif value[0] == 'Q':
        require(len(value) == 3)
        _, binder, body = value
        require(variable(binder))
        formula(body, scope | {binder})
    else:
        require(value[0] == 'D' and len(value) == 4)
        _, first, second, body = value
        require(variable(first) and variable(second) and first != second)
        formula(body, scope | {first, second})


def computation(value):
    require(type(value) is list and value[0] == 'I')
    _, counter, seed, binder, update = value
    if counter == 0:
        return seed
    require(type(counter) is list and counter[0] == 'S')
    predecessor = counter[1]
    argument = ['I', predecessor, seed, binder, update]
    return substitute(update, binder, argument)


def infer(proof, context=(), scope=frozenset()):
    require(type(proof) is list and len(proof) > 0)
    rule = proof[0]
    if rule == 'hyp':
        _, index = proof
        require(type(index) is int and 0 <= index < len(context))
        result = context[index]
    elif rule == 'comp':
        _, left = proof
        term(left, scope)
        result = ['=', left, computation(left)]
    elif rule == 'transport':
        _, source, minor, placeholder, template = proof
        require(variable(placeholder) and placeholder not in scope)
        formula(template, scope | {placeholder})
        equality = infer(source, context, scope)
        require(equality[0] == '=')
        previous = infer(minor, context, scope)
        require(same(previous, substitute(template, placeholder, equality[1])))
        result = substitute(template, placeholder, equality[2])
    elif rule == 'intro':
        _, result, witness, eigen, mode, child = proof
        formula(result, scope)
        term(witness, scope)
        require(result[0] == 'D' and mode in ('case', 'ind'))
        require(variable(eigen) and eigen not in scope | names(result) | names(witness)
                and all(eigen not in names(item) for item in context))
        _, first, second, body = result
        require(second not in free(witness))
        matrix = substitute(body, first, witness)
        require(mode == 'case' or matrix[0] == '=')
        local = substitute(matrix, second, 0 if mode == 'case' else eigen)
        target = substitute(matrix, second, ['S', eigen])
        require(same(infer(child, (*context, local), scope | {eigen}), target))
    elif rule == 'qelim':
        _, major, minor, target = proof
        closure = infer(major, context, scope)
        require(closure[0] == 'Q')
        _, binder, body = closure
        term(target, scope)
        require(same(infer(minor, context, scope), substitute(body, binder, 0)))
        result = substitute(body, binder, target)
    elif rule == 'delim':
        _, major, eigen, child = proof
        paired = infer(major, context, scope)
        require(paired[0] == 'D' and variable(eigen))
        require(eigen not in scope | names(paired)
                and all(eigen not in names(item) for item in context))
        _, first, second, body = paired
        local = ['Q', second, substitute(body, first, eigen)]
        result = infer(child, (*context, local), scope | {eigen})
        require(eigen not in free(result))
    else:
        raise ValueError('unknown inference')
    formula(result, scope)
    return result


def verify(packet):
    require(type(packet) is list and len(packet) == 2)
    goal, proof = packet
    formula(goal, frozenset())
    require(same(infer(proof), goal))
    return True


if __name__ == '__main__':
    try:
        verify(json.load(open(0)))
        print('ACCEPT')
    except Exception:
        print('REJECT')
        raise SystemExit(1)
