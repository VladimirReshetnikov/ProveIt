"""Equality-free subset-seeded closure: reference syntax and certificate checker.

The implementation is not a verified TM compiler or an exported ZFC/PA proof.
Only the Python standard library is required. Resource exhaustion is not treated
as a logical rejection. All schema matrices have arbitrary finite complexity.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Any, Iterable

@dataclass(frozen=True)
class F:
    op: str
    args: tuple = ()

def natural(x: Any) -> int:
    if type(x) is not int or x < 0:
        raise ValueError('Expected a nonnegative integer, not a Boolean.')
    return x

def Bot() -> F: return F('bot')
def M(x: int, y: int) -> F: return F('mem', (natural(x), natural(y)))
def Eq(x: int, y: int) -> F: return F('eq', (natural(x), natural(y)))
def Hole(x: int, y: int) -> F: return F('hole', (x, y))
def Imp(a: F, b: F) -> F: return F('imp', (a, b))
def All(x: int, a: F) -> F: return F('all', (natural(x), a))
def Not(a: F) -> F: return Imp(a, Bot())
def And(a: F, b: F) -> F: return Not(Imp(a, Not(b)))
def Or(a: F, b: F) -> F: return Imp(Not(a), b)
def Iff(a: F, b: F) -> F: return And(Imp(a, b), Imp(b, a))
def Ex(x: int, a: F) -> F: return Not(All(x, Not(a)))
def For(xs: Iterable[int], a: F) -> F:
    for x in reversed(tuple(xs)): a = All(x, a)
    return a

def names(a: F) -> set[int]:
    if a.op in ('mem', 'eq', 'hole'): return set(a.args)
    if a.op == 'bot': return set()
    if a.op == 'all': return {a.args[0]} | names(a.args[1])
    if a.op == 'imp': return names(a.args[0]) | names(a.args[1])
    raise ValueError('Unknown formula constructor.')

def fv(a: F) -> set[int]:
    if a.op in ('mem', 'eq', 'hole'): return set(a.args)
    if a.op == 'bot': return set()
    if a.op == 'all': return fv(a.args[1]) - {a.args[0]}
    if a.op == 'imp': return fv(a.args[0]) | fv(a.args[1])
    raise ValueError('Unknown formula constructor.')

def subst(a: F, x: int, y: int) -> F:
    """Capture-avoiding substitution of variable y for free variable x."""
    natural(x); natural(y)
    if x == y or x not in fv(a): return a
    if a.op in ('mem', 'eq', 'hole'):
        return F(a.op, tuple(y if z == x else z for z in a.args))
    if a.op == 'imp': return Imp(subst(a.args[0], x, y), subst(a.args[1], x, y))
    if a.op == 'all':
        z, body = a.args
        if z == x: return a
        if z == y:
            fresh = max(names(a) | {x, y}) + 1
            body, z = subst(body, z, fresh), fresh
        return All(z, subst(body, x, y))
    return a

def alpha_key(a: F, env: tuple[int, ...] = ()) -> tuple:
    def var(x: int) -> tuple:
        for k, z in enumerate(reversed(env)):
            if x == z: return ('bound', k)
        return ('free', x)
    if a.op in ('mem', 'eq', 'hole'):
        return (a.op, *(var(x) for x in a.args))
    if a.op == 'bot': return ('bot',)
    if a.op == 'all': return ('all', alpha_key(a.args[1], env + (a.args[0],)))
    if a.op == 'imp': return ('imp', alpha_key(a.args[0], env), alpha_key(a.args[1], env))
    raise ValueError('Unknown formula constructor.')

def same(a: F, b: F) -> bool: return alpha_key(a) == alpha_key(b)

def Sub(x: int, y: int, z: int) -> F:
    if z in (x, y): raise ValueError('Subset binder must be fresh.')
    return All(z, Imp(M(z, x), M(z, y)))

def extensionality() -> F:
    return For((0, 1), Imp(All(2, Iff(M(2, 0), M(2, 1))), Eq(0, 1)))

def congruence() -> F:
    return For((0, 1), Imp(All(2, Iff(M(2, 0), M(2, 1))),
                          All(3, Iff(M(0, 3), M(1, 3)))))

def closure(matrix: F, seed: str = 'subset', mixed: bool = False,
            close_parameters: bool = True, curried: bool = False) -> F:
    """Fresh generation; slots 0/1 are input/output, other free names parameters.

    eq/hole nodes are permitted here only for measurement controls. The checker
    accepts matrices parsed in the equality-free executing grammar.
    """
    start = max(names(matrix) | {1}) + 1
    x, b, y, a, c, z = range(start, start + 6)
    rho = subst(subst(matrix, 0, x), 1, y)
    bound = Sub(y, b, z)
    if mixed: bound = Or(M(y, b), bound)
    local = All(x, Ex(b, All(y, Imp(rho, bound))))
    if seed == 'point': seed_formula = Eq(x, a)
    elif seed == 'subset': seed_formula = Sub(x, a, z)
    else: raise ValueError('Unknown seed.')
    active = Or(seed_formula, M(x, c))
    body = Imp(active, Imp(rho, M(y, c))) if curried else Imp(And(active, rho), M(y, c))
    closed = For((x, y), body)
    support = All(y, Imp(M(y, c), Ex(x, rho)))
    result = Imp(local, All(a, Ex(c, And(closed, support))))
    return For(sorted(fv(matrix) - {0, 1}), result) if close_parameters else result

def counts(a: F) -> dict[str, int]:
    result: dict[str, int] = {}
    todo = [a]
    while todo:
        f = todo.pop(); result[f.op] = result.get(f.op, 0) + 1
        if f.op == 'all': todo.append(f.args[1])
        if f.op == 'imp': todo.extend(f.args)
    return result

def parse_formula(a: Any) -> F:
    if type(a) is not list or not a: raise ValueError('A formula is a nonempty tagged list.')
    tag = natural(a[0])
    if tag == 0 and len(a) == 1: return Bot()
    if tag == 1 and len(a) == 3: return M(a[1], a[2])
    if tag == 2 and len(a) == 3: return Imp(parse_formula(a[1]), parse_formula(a[2]))
    if tag == 3 and len(a) == 3: return All(a[1], parse_formula(a[2]))
    raise ValueError('Invalid executing formula; equality and holes are not allowed.')

def dump_formula(a: F) -> list:
    if a.op == 'bot': return [0]
    if a.op == 'mem': return [1, *a.args]
    if a.op == 'imp': return [2, dump_formula(a.args[0]), dump_formula(a.args[1])]
    if a.op == 'all': return [3, a.args[0], dump_formula(a.args[1])]
    raise ValueError('Not an executing equality-free formula.')

@dataclass
class CheckResult:
    valid: bool
    refutation: bool
    lines: int
    error: str | None = None

def derive(proof: Any) -> list[F]:
    """Construct theorems, never accept an unchecked claimed conclusion."""
    if type(proof) is not list or not proof: raise ValueError('Empty or malformed certificate.')
    proved: list[F] = []
    def prior(i: Any) -> F:
        natural(i)
        if i >= len(proved): raise ValueError('References must point strictly backward.')
        return proved[i]
    for line, r in enumerate(proof):
        if type(r) is not list or not r: raise ValueError(f'Malformed record {line}.')
        tag = natural(r[0])
        if tag == 0 and len(r) == 3:
            a, b = map(parse_formula, r[1:]); conclusion = Imp(a, Imp(b, a))
        elif tag == 1 and len(r) == 4:
            a, b, c = map(parse_formula, r[1:])
            conclusion = Imp(Imp(a, Imp(b, c)), Imp(Imp(a, b), Imp(a, c)))
        elif tag == 2 and len(r) == 3:
            a, b = map(parse_formula, r[1:]); conclusion = Imp(Imp(Not(a), Not(b)), Imp(b, a))
        elif tag == 3 and len(r) == 4:
            x, y = natural(r[1]), natural(r[2]); a = parse_formula(r[3])
            conclusion = Imp(All(x, a), subst(a, x, y))
        elif tag == 4 and len(r) == 4:
            x = natural(r[1]); a, b = map(parse_formula, r[2:])
            if x in fv(a): raise ValueError('Q2 variable is free in the antecedent.')
            conclusion = Imp(All(x, Imp(a, b)), Imp(a, All(x, b)))
        elif tag == 5 and len(r) == 3:
            a, implication = prior(r[1]), prior(r[2])
            if implication.op != 'imp' or not same(a, implication.args[0]):
                raise ValueError('Modus ponens antecedent mismatch.')
            conclusion = implication.args[1]
        elif tag == 6 and len(r) == 3:
            conclusion = All(natural(r[1]), prior(r[2]))
        elif tag == 7 and len(r) == 1:
            conclusion = congruence()
        elif tag == 8 and len(r) == 2:
            conclusion = closure(parse_formula(r[1]))
        else: raise ValueError(f'Unknown rule or invalid arity at record {line}.')
        proved.append(conclusion)
    return proved

def check(proof: Any) -> CheckResult:
    try:
        formulas = derive(proof)
        return CheckResult(True, formulas[-1].op == 'bot', len(formulas))
    except (ValueError, TypeError) as exc:
        return CheckResult(False, False, 0, str(exc))

def evaluate(a: F, member: list[int], env: dict[int, int], relation: list[int] | None = None) -> bool:
    """Finite-model regression semantics. Bit j in member[i] means j is in i."""
    if a.op == 'bot': return False
    if a.op == 'mem': return bool(member[env[a.args[1]]] & (1 << env[a.args[0]]))
    if a.op == 'eq': return env[a.args[0]] == env[a.args[1]]
    if a.op == 'hole':
        if relation is None: raise ValueError('Missing matrix relation.')
        return bool(relation[env[a.args[0]]] & (1 << env[a.args[1]]))
    if a.op == 'imp': return not evaluate(a.args[0], member, env, relation) or evaluate(a.args[1], member, env, relation)
    if a.op == 'all':
        x, body = a.args
        return all(evaluate(body, member, env | {x: v}, relation) for v in range(len(member)))
    raise ValueError('Unknown formula constructor.')
