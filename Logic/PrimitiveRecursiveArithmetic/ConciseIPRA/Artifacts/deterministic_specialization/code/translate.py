"""Untrusted, constructive translation of complete unrestricted certificates.

The source is reference/unrestricted.py (oldest-first contexts).  The output
is checked independently by checker.py (newest-first contexts).  Persistent
premises are Python functions rebuilding a proof in each requested extended
context.  They are never trusted by the output checker.
"""
import importlib.util
import json
from pathlib import Path
import sys

import arith as a
import checker


def load_source():
    path = Path(__file__).resolve().parents[1] / 'reference' / 'unrestricted.py'
    spec = importlib.util.spec_from_file_location('unrestricted_source', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


source = load_source()


class Clause:
    """Identity distinguishes two occurrences with identical contents."""
    def __init__(self, antecedent, body):
        self.antecedent = antecedent
        self.body = body


def rename(tree, variables):
    if type(tree) is int:
        return variables[tree] if tree < 0 else tree
    if type(tree) is list:
        return [rename(item, variables) for item in tree]
    return tree


def rank(formula):
    return 0 if formula[0] == '=' else 1 + rank(formula[1])


def ordinary(clause, context):
    return a.assumption(context.index(clause))


def transport(template, s, t, equality, minor, context):
    """T_r: equality is persistent; minor is a proof only in this context.

    The D case consumes minor before entering any new scope.  No existing
    arbitrary proof tree is silently moved into a larger scope.
    """
    if template[0] == '=':
        equation = a.equation(a.opening(template, s), minor)
        return a.transport_equation(equality(context), equation, template)[2]

    target = a.opening(template, t)
    original = a.opening(template, s)
    witness = -len(context) - 1
    body = a.opening(original[1], witness, 1)
    closure = Clause(a.opening(body, 0), body)
    opened = [closure] + context
    fresh = -len(opened) - 1
    target_body = a.opening(target[1], witness, 1)
    assumed = Clause(a.Eq(0, 0), a.opening(target_body, 0))
    branch_context = [assumed] + opened

    # Removing x and y leaves exactly the outer template variable free.
    matrix_template = a.opening(template[1], witness, 1)
    base_template = a.opening(matrix_template, 0)
    successor_template = a.opening(matrix_template, a.S(fresh))

    def reverse(extended):
        return a.sym(equality(extended))

    def source_base(extended):
        return transport(base_template, t, s, reverse,
                         ordinary(assumed, extended), extended)

    source_successor = specialize(closure, a.S(fresh), source_base,
                                  branch_context)
    target_successor = transport(successor_template, s, t, equality,
                                 source_successor, branch_context)
    introduction = ['i', target, witness, target_successor]
    return ['e', target, minor, introduction]


def specialize(clause, term, premise, context):
    """U_r: premise(extended_context) supplies the antecedent persistently."""
    index = context.index(clause)
    permitted = a.ONE if index == 0 else -len(context)
    if term == permitted:
        return ['u', index, premise(context)]

    named, naming_proof = a.name(term, len(context))
    witness = -len(context) - 1
    name_base, name_body = a.naming_clause(witness, term)
    name_clause = Clause(name_base, name_body)
    extended = [name_clause] + context
    at_variable = ['u', extended.index(clause), premise(extended)]

    if rank(clause.body) == 0:
        # T_0 opens no scopes, so this immediate naming proof suffices.
        def equality(requested):
            if requested is not extended:
                raise ValueError('Atomic transport unexpectedly opened a scope')
            return a.newest_name_equality(witness, term)
    else:
        # Rebuild the atomic name equality if the naming clause has become
        # older.  This invokes U_0, never U_r at the present positive rank.
        def equality(requested):
            at_one = specialize(name_clause, a.ONE,
                                lambda _: a.refl(0)[2], requested)
            return a.extract_name(witness, term, at_one)

    transported = transport(clause.body, witness, term, equality,
                            at_variable, extended)
    goal = a.opening(clause.body, term)
    return ['e', goal, naming_proof, transported]


def compile_proof(proof, source_context, variables, references, context):
    """Structural recursion on the source proof produces persistent output.

    references maps source clause occurrences to identity-bearing target
    occurrences. variables maps old free levels to their current fresh names.
    An invocation under a later context is a regeneration, not weakening.
    """
    tag = proof[0]
    if tag == 'r':
        return ['r', rename(proof[1], variables)]
    if tag == 'x':
        return ['x', *(compile_proof(p, source_context, variables,
                                     references, context) for p in proof[1:])]
    if tag == 'u':
        _, index, term, subproof = proof

        def premise(extended):
            return compile_proof(subproof, source_context, variables,
                                 references, extended)

        return specialize(references[index], rename(term, variables),
                          premise, context)

    _, goal, data, branch = proof
    output_goal = rename(goal, variables)
    old_fresh = -len(source_context) - 1
    new_fresh = -len(context) - 1
    next_variables = dict(variables)
    next_variables[old_fresh] = new_fresh

    if tag == 'e':
        paired = source.derive(data, source_context, len(source_context))
        old_body = a.opening(paired[1], old_fresh, 1)
        old_clause = (a.opening(old_body, 0), old_body)
        new_body = a.opening(rename(paired, variables)[1], new_fresh, 1)
        new_clause = Clause(a.opening(new_body, 0), new_body)
        output_data = compile_proof(data, source_context, variables,
                                    references, context)
    elif tag == 'i':
        old_body = a.opening(goal[1], data, 1)
        old_eta = old_fresh if goal[1][0] == '=' and data == 0 else 0
        old_clause = (a.Eq(0, 0), a.opening(old_body, old_eta))
        output_data = rename(data, variables)
        new_body = a.opening(output_goal[1], output_data, 1)
        new_eta = new_fresh if goal[1][0] == '=' and data == 0 else 0
        new_clause = Clause(a.Eq(0, 0), a.opening(new_body, new_eta))
    else:
        raise ValueError('Invalid source instruction')

    output_branch = compile_proof(branch, source_context + [old_clause],
                                  next_variables, references + [new_clause],
                                  [new_clause] + context)
    return [tag, output_goal, output_data, output_branch]


def translate(certificate):
    source.verify(certificate)
    result = {'goal': certificate['goal'],
              'proof': compile_proof(certificate['proof'], [], {}, [], [])}
    checker.verify(result)
    return result


def expand_proof(proof, context):
    """Reverse inclusion: insert the deterministic target and reverse indices."""
    tag = proof[0]
    if tag == 'r':
        return proof
    if tag == 'x':
        return ['x', *(expand_proof(p, context) for p in proof[1:])]
    if tag == 'u':
        _, index, premise = proof
        target = a.ONE if index == 0 else -len(context)
        return ['u', len(context) - 1 - index, target,
                expand_proof(premise, context)]
    _, goal, data, branch = proof
    fresh = -len(context) - 1
    if tag == 'e':
        paired = checker.derive(data, context)
        body = a.opening(paired[1], fresh, 1)
        clause = (a.opening(body, 0), body)
        old_data = expand_proof(data, context)
    else:
        body = a.opening(goal[1], data, 1)
        eta = fresh if goal[1][0] == '=' and data == 0 else 0
        clause = (a.Eq(0, 0), a.opening(body, eta))
        old_data = data
    return [tag, goal, old_data, expand_proof(branch, [clause] + context)]


def expand(certificate):
    checker.verify(certificate)
    result = {'goal': certificate['goal'],
              'proof': expand_proof(certificate['proof'], [])}
    source.verify(result)
    return result


if __name__ == '__main__':
    certificate = json.load(sys.stdin)
    output = expand(certificate) if '--reverse' in sys.argv else translate(certificate)
    json.dump(output, sys.stdout, separators=(',', ':'))
    print()
