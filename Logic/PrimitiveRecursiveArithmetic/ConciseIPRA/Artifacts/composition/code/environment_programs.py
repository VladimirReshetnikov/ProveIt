"""Executable semantics for the variable-free environment presentation.

This is a semantic demonstrator, not a proof checker or a formal proof of
bi-interpretability. A word is a tuple of instructions. The empty word is
identity, and concatenation executes its left operand first.
"""

IDENTITY = ()
ZERO = ("zero",)
SUCCESSOR = ("succ",)
LEFT = ("left",)
RIGHT = ("right",)


def pair(a, b):
    if type(a) is not int or type(b) is not int or min(a, b) < 0:
        raise ValueError("pairing requires natural numbers")
    return (2 * b + 1) * (1 << a) - 1


def unpair(n):
    if type(n) is not int or n < 0:
        raise ValueError("unpairing requires a natural number")
    odd = n + 1
    exponent = 0
    while odd % 2 == 0:
        odd //= 2
        exponent += 1
    return exponent, (odd - 1) // 2


def fork(p, q):
    return (("fork", p, q),)


def iterator(h):
    return (("iterate", h),)


def triple(n, a, e=IDENTITY):
    return fork(n, fork(a, e))


def valid_word(word):
    if type(word) is not tuple:
        return False
    for instruction in word:
        if type(instruction) is str:
            if instruction not in {"zero", "succ", "left", "right"}:
                return False
        elif type(instruction) is tuple and instruction:
            if instruction[0] == "fork" and len(instruction) == 3:
                if not all(valid_word(p) for p in instruction[1:]):
                    return False
            elif instruction[0] == "iterate" and len(instruction) == 2:
                if not valid_word(instruction[1]):
                    return False
            else:
                return False
        else:
            return False
    return True


def run(word, value):
    """Evaluate one finite program at a natural number (may be expensive)."""
    for instruction in word:
        if instruction == "zero":
            value = 0
        elif instruction == "succ":
            value += 1
        elif instruction == "left":
            value = unpair(value)[0]
        elif instruction == "right":
            value = unpair(value)[1]
        elif instruction[0] == "fork":
            value = pair(run(instruction[1], value), run(instruction[2], value))
        elif instruction[0] == "iterate":
            count, payload = unpair(value)
            accumulator, environment = unpair(payload)
            for _ in range(count):
                accumulator = run(instruction[1], pair(accumulator, environment))
            value = accumulator
        else:
            raise ValueError("invalid instruction")
    return value


def equation(p, q):
    return ("eq", p, q)


def binder(prefix, body):
    return ("D", prefix, body)


def closure(prefix, body):
    return ("Q", prefix, body)


def reindex(formula, word):
    """Change the input environment at the root; never descend into a body."""
    kind, first, second = formula
    if kind == "eq":
        return equation(word + first, word + second)
    if kind in {"Q", "D"}:
        return (kind, word + first, second)
    raise ValueError("invalid formula")


def finite_reading(formula, environment, bound):
    """Finite-window semantics ONLY for testing the reindex identity.

    This is not truth in arithmetic and is not used to accept a theorem.
    Both quantified variables in each D range over range(bound).
    """
    kind, first, second = formula
    if kind == "eq":
        return run(first, environment) == run(second, environment)
    if kind == "Q":
        tail = run(first, environment)
        return (not finite_reading(second, pair(0, tail), bound)
                or all(finite_reading(second, pair(y, tail), bound)
                       for y in range(bound)))
    if kind == "D":
        tail = run(first, environment)
        return any(
            not finite_reading(second, pair(0, pair(x, tail)), bound)
            or all(finite_reading(second, pair(y, pair(x, tail)), bound)
                   for y in range(bound))
            for x in range(bound)
        )
    raise ValueError("invalid formula")


def variable(index):
    return RIGHT * index + LEFT


def compile_term(term):
    """Compile de Bruijn scalar iterator syntax into variable-free words.

    Source forms: ('var', j), ('zero',), ('succ', t), ('iter', n, a, h).
    Only h binds a variable. The target compiler introduces no names.
    """
    tag = term[0]
    if tag == "var":
        return variable(term[1])
    if tag == "zero":
        return ZERO
    if tag == "succ":
        return compile_term(term[1]) + SUCCESSOR
    if tag == "iter":
        n, a, h = map(compile_term, term[1:])
        return triple(n, a) + iterator(h)
    raise ValueError("invalid term")


def shift(term, amount=1, cutoff=0):
    if term[0] == "var":
        return ("var", term[1] + amount if term[1] >= cutoff else term[1])
    if term[0] == "zero":
        return term
    if term[0] == "succ":
        return ("succ", shift(term[1], amount, cutoff))
    return ("iter", shift(term[1], amount, cutoff),
            shift(term[2], amount, cutoff), shift(term[3], amount, cutoff + 1))


def substitute(term, replacement, depth=0):
    """Reference source substitution; absent from target reindex()."""
    if term[0] == "var":
        index = term[1]
        if index == depth:
            return shift(replacement, depth)
        return ("var", index - (index > depth))
    if term[0] == "zero":
        return term
    if term[0] == "succ":
        return ("succ", substitute(term[1], replacement, depth))
    return ("iter", substitute(term[1], replacement, depth),
            substitute(term[2], replacement, depth),
            substitute(term[3], replacement, depth + 1))
