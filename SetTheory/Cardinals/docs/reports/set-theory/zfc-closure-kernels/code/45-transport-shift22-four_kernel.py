#!/usr/bin/env python3
"""Reference kernel for equality-free first-order logic with one contraction.

This is a mathematical reference implementation, not a Turing-machine compiler.
Bound variables use nonnegative de Bruijn indices. Free names are integers.
The only primitive renamings are up, down, swap (0 1), and contract (0 -> 1).
All operate only on free names. Proofs have no assumption-opening instruction.
The only AX instruction refers to a supplied finite list of *closed* axioms.

Tuple syntax:
  variable = ('b', index) | ('f', integer)
  formula  = ('bot',) | ('rel', var, var) | ('imp', formula, formula)
             | ('all', formula)
"""

from __future__ import annotations

from itertools import product
from typing import Callable, Iterable

Var = tuple
Formula = tuple
BOT: Formula = ('bot',)
RENAMINGS = frozenset(('up', 'down', 'swap', 'contract'))


def B(index: int) -> Var:
    return ('b', index)


def F(name: int) -> Var:
    return ('f', name)


def R(a: Var, b: Var) -> Formula:
    return ('rel', a, b)


def Imp(a: Formula, b: Formula) -> Formula:
    return ('imp', a, b)


def All(body: Formula) -> Formula:
    return ('all', body)


def Not(a: Formula) -> Formula:
    return Imp(a, BOT)


def And(a: Formula, b: Formula) -> Formula:
    return Not(Imp(a, Not(b)))


def Iff(a: Formula, b: Formula) -> Formula:
    return And(Imp(a, b), Imp(b, a))


def freeze(value):
    """Read JSON arrays as immutable syntax, preserving integer names."""
    if isinstance(value, list):
        return tuple(freeze(x) for x in value)
    return value


def integer(n) -> bool:
    return type(n) is int


def scoped(formula: Formula, depth: int = 0) -> bool:
    if not isinstance(formula, tuple) or not formula:
        return False
    tag = formula[0]
    if tag == 'bot':
        return len(formula) == 1
    if tag == 'rel' and len(formula) == 3:
        for var in formula[1:]:
            if not isinstance(var, tuple) or len(var) != 2:
                return False
            if not integer(var[1]):
                return False
            if var[0] == 'b':
                if not 0 <= var[1] < depth:
                    return False
            elif var[0] != 'f':
                return False
        return True
    if tag == 'imp' and len(formula) == 3:
        return scoped(formula[1], depth) and scoped(formula[2], depth)
    if tag == 'all' and len(formula) == 2:
        return scoped(formula[1], depth + 1)
    return False


def free_names(formula: Formula) -> set[int]:
    tag = formula[0]
    if tag == 'bot':
        return set()
    if tag == 'rel':
        return {v[1] for v in formula[1:] if v[0] == 'f'}
    if tag == 'imp':
        return free_names(formula[1]) | free_names(formula[2])
    return free_names(formula[1])


def edit(formula: Formula, fn: Callable[[Var, int], Var], depth=0) -> Formula:
    tag = formula[0]
    if tag == 'bot':
        return BOT
    if tag == 'rel':
        return R(fn(formula[1], depth), fn(formula[2], depth))
    if tag == 'imp':
        return Imp(edit(formula[1], fn, depth), edit(formula[2], fn, depth))
    return All(edit(formula[1], fn, depth + 1))


def rename(formula: Formula, fn: Callable[[int], int]) -> Formula:
    return edit(formula, lambda var, _: F(fn(var[1])) if var[0] == 'f' else var)


def name_step(op: str, name: int) -> int:
    if op == 'up':
        return name + 1
    if op == 'down':
        return name - 1
    if op == 'swap':
        return 1 - name if name in (0, 1) else name
    if op == 'contract':
        return 1 if name == 0 else name
    raise ValueError('unknown primitive free-name map')


def rename_step(op: str, formula: Formula) -> Formula:
    return rename(formula, lambda name: name_step(op, name))


def open_body(body: Formula, name: int) -> Formula:
    """Delete the displayed outer binder and replace its occurrences by F(name).

    Precondition scoped(body, 1) ensures there is no dangling index above depth.
    Internal binders retain their de Bruijn indices; all free fields are copied.
    """
    if not scoped(body, 1) or not integer(name):
        raise ValueError('malformed body/name')
    return edit(body, lambda var, d: F(name) if var == B(d) else var)


def close_name(formula: Formula, name: int) -> Formula:
    """Abstract one free name, making a body for a new outer binder."""
    if not scoped(formula) or not integer(name):
        raise ValueError('malformed formula/name')
    return edit(formula, lambda var, d: B(d) if var == F(name) else var)


def evaluate(formula: Formula, domain: tuple, relation: Callable,
             assignment: Callable[[int], object], stack=()) -> bool:
    def val(var):
        return stack[var[1]] if var[0] == 'b' else assignment(var[1])
    tag = formula[0]
    if tag == 'bot':
        return False
    if tag == 'rel':
        return bool(relation(val(formula[1]), val(formula[2])))
    if tag == 'imp':
        return (not evaluate(formula[1], domain, relation, assignment, stack)
                or evaluate(formula[2], domain, relation, assignment, stack))
    return all(evaluate(formula[1], domain, relation, assignment, (x,) + stack)
               for x in domain)


def check_certificate(certificate: dict, theory: Iterable[Formula] = ()) -> list:
    """Reconstruct every line; raises ValueError on every malformed certificate.

    A theory axiom must be closed. The input theory is the object theory whose
    consequence relation is being checked; it is not a list of accepted proofs.
    A consistency search must fix its theory/axiom emitter independently of
    candidates, and search only for reconstructed BOT.
    """
    if not isinstance(certificate, dict):
        raise ValueError('certificate must be an object')
    theory = tuple(freeze(a) for a in theory)
    if any(not scoped(a) or free_names(a) for a in theory):
        raise ValueError('theory axioms must be closed well-scoped formulas')
    instructions = certificate.get('instructions')
    if not isinstance(instructions, list):
        raise ValueError('missing instruction list')
    lines = []

    def prior(index):
        if not integer(index) or not 0 <= index < len(lines):
            raise ValueError('forward, negative or noninteger line reference')
        return lines[index]

    def formula_arg(ins, name, depth=0):
        formula = freeze(ins.get(name))
        if not scoped(formula, depth):
            raise ValueError('ill-scoped formula argument')
        return formula

    for ins in instructions:
        if not isinstance(ins, dict) or not isinstance(ins.get('op'), str):
            raise ValueError('malformed instruction')
        op = ins['op']
        if op in RENAMINGS:
            result = rename_step(op, prior(ins.get('line')))
        elif op == 'fresh_ui':
            body = formula_arg(ins, 'body', 1)
            fresh = ins.get('fresh')
            if not integer(fresh) or fresh in free_names(body):
                raise ValueError('fresh UI requires a name absent from the body')
            result = Imp(All(body), open_body(body, fresh))
        elif op == 'K':
            a, b = formula_arg(ins, 'a'), formula_arg(ins, 'b')
            result = Imp(a, Imp(b, a))
        elif op == 'S':
            a, b, c = (formula_arg(ins, k) for k in ('a', 'b', 'c'))
            result = Imp(Imp(a, Imp(b, c)), Imp(Imp(a, b), Imp(a, c)))
        elif op == 'Peirce':
            a, b = formula_arg(ins, 'a'), formula_arg(ins, 'b')
            result = Imp(Imp(Imp(a, b), a), a)
        elif op == 'exfalso':
            result = Imp(BOT, formula_arg(ins, 'a'))
        elif op == 'distribution':
            a, b = formula_arg(ins, 'a', 1), formula_arg(ins, 'b', 1)
            result = Imp(All(Imp(a, b)), Imp(All(a), All(b)))
        elif op == 'vacuity':
            a = formula_arg(ins, 'a')
            result = Imp(a, All(a))
        elif op == 'gen':
            a, name = prior(ins.get('line')), ins.get('name')
            if not integer(name):
                raise ValueError('bad generalization name')
            result = All(close_name(a, name))
        elif op == 'mp':
            implication = prior(ins.get('implication'))
            antecedent = prior(ins.get('antecedent'))
            if implication[0] != 'imp' or implication[1] != antecedent:
                raise ValueError('modus ponens does not match')
            result = implication[2]
        elif op == 'axiom':
            index = ins.get('index')
            if not integer(index) or not 0 <= index < len(theory):
                raise ValueError('unknown fixed theory axiom')
            result = theory[index]
        else:
            raise ValueError('unknown instruction')
        if not scoped(result):
            raise ValueError('internal scope invariant failed')
        if 'result' in ins and freeze(ins['result']) != result:
            raise ValueError('supplied line does not equal reconstructed line')
        lines.append(result)
    if 'conclusion' in certificate:
        if not lines or freeze(certificate['conclusion']) != lines[-1]:
            raise ValueError('incorrect final conclusion')
    return lines


def normal_word(word: Iterable[str]) -> list[str]:
    """Cancel adjacent inverse shifts/involutions and repeated contractions."""
    out = []
    inverse = {'up': 'down', 'down': 'up', 'swap': 'swap'}
    for op in word:
        if op not in RENAMINGS:
            raise ValueError('bad word')
        if out and inverse.get(op) == out[-1]:
            out.pop()
        elif out and op == out[-1] == 'contract':
            pass
        else:
            out.append(op)
    return out


def shifts(amount: int) -> list[str]:
    return ['up' if amount >= 0 else 'down'] * abs(amount)


def adjacent_swap_word(lower: int) -> list[str]:
    return shifts(-lower) + ['swap'] + shifts(lower)


def swap_word(a: int, b: int) -> list[str]:
    if a == b:
        return []
    a, b = sorted((a, b))
    positions = list(range(a, b)) + list(range(b - 2, a - 1, -1))
    return normal_word(op for position in positions for op in adjacent_swap_word(position))


def conjugator(source: int, target: int) -> list[tuple[int, int]]:
    """At most two transpositions, in execution order, sending 0 to source, 1 to target."""
    if source == target:
        raise ValueError('contraction requires distinct source and target')
    first = (0, source)
    one_image = 0 if source == 1 else 1
    pairs = [first, (one_image, target)]
    return [(a, b) for a, b in pairs if a != b]


def contract_name_word(source: int, target: int) -> list[str]:
    if source == target:
        return []
    q = conjugator(source, target)
    word = [op for pair in reversed(q) for op in swap_word(*pair)]
    word += ['contract']
    word += [op for pair in q for op in swap_word(*pair)]
    return normal_word(word)


def run_name_word(word: Iterable[str], name: int) -> int:
    for op in word:
        name = name_step(op, name)
    return name


def factor_on_support(mapping: dict[int, int]) -> list[str]:
    """Realize any finite partial map, using exactly |S|-|f(S)| contractions.

    Outside S the resulting transformation is intentionally unspecified. To
    realize a finite-support *total* map exactly, include all affected names
    and all their images in S, recording the intended identity values too.
    """
    if not all(integer(a) and integer(b) for a, b in mapping.items()):
        raise ValueError('map names must be integers')
    if not mapping:
        return []
    universe = sorted(set(mapping) | set(mapping.values()))
    fibers = {}
    for source, target in sorted(mapping.items()):
        fibers.setdefault(target, []).append(source)
    reps = {target: sources[0] for target, sources in fibers.items()}
    word = []
    for source, target in sorted(mapping.items()):
        representative = reps[target]
        if source != representative:
            word.extend(contract_name_word(source, representative))

    # Complete the partial bijection representative -> image to a permutation.
    permutation = {representative: target for target, representative in reps.items()}
    spare_sources = [x for x in universe if x not in permutation]
    spare_targets = [x for x in universe if x not in permutation.values()]
    permutation.update(zip(spare_sources, spare_targets))
    visited = set()
    for start in universe:
        if start in visited:
            continue
        cycle, x = [], start
        while x not in visited:
            visited.add(x)
            cycle.append(x)
            x = permutation[x]
        for target in cycle[1:]:
            word.extend(swap_word(cycle[0], target))
    return normal_word(word)


def make_ui_certificate(body: Formula, target: int) -> dict:
    if not scoped(body, 1) or not integer(target):
        raise ValueError('bad UI body/target')
    used = free_names(body)
    if target not in used:
        fresh = target
    else:
        fresh = 0
        while fresh in used:
            fresh += 1
    instructions = [{'op': 'fresh_ui', 'body': body, 'fresh': fresh}]
    for op in contract_name_word(fresh, target):
        instructions.append({'op': op, 'line': len(instructions) - 1})
    return {'instructions': instructions,
            'conclusion': Imp(All(body), open_body(body, target))}


def source19_body() -> Formula:
    """((R(x,y) <-> R(x,z)) <-> R(y,z)), with x bound, y=0, z=1."""
    return Iff(Iff(R(B(0), F(0)), R(B(0), F(1))), R(F(0), F(1)))


def source19_bad_semantics() -> list[dict]:
    rows = []
    for x, y, z in product((0, 1), repeat=3):
        original = (((x == y) == (x == z)) == (y == z))
        collided = ((False == (y == z)) == (y == z))
        rows.append({'x': x, 'y': y, 'z': z,
                     'body': original, 'identified_body': collided,
                     'ui_instance': (not original) or collided})
    return rows


if __name__ == '__main__':
    import json
    cert = make_ui_certificate(source19_body(), 0)
    checked = check_certificate(cert)
    print(json.dumps({'accepted': True, 'lines': len(checked),
                      'contractions': sum(i['op'] == 'contract' for i in cert['instructions']),
                      'certificate': cert}, indent=2))
