"""Untrusted structural compiler from the liberal control into checker.py.

The recursion is on source certificates.  Source antecedents and Close
premises are rebuilt in the exact new scope; finished target derivations
are never weakened.  Fixed helper constructions are built directly by
proof_tools and are not recursively fed into this compiler.
"""
import json
import sys

import checker as target
import control_liberal as source
import proof_tools as p


def translate(proof, source_context=p.INITIAL, target_context=p.INITIAL,
              numerical=None, clauses=None):
    if numerical is None:
        numerical = {i: i for i in range(1 - len(source_context), 0)}
    if clauses is None:
        clauses = list(range(len(source_context)))
    expected_source = source.prove(proof, source_context)
    if len(set(numerical.values())) != len(numerical):
        raise ValueError('the numerical embedding must be injective')
    if any(not 1 - len(target_context) <= j < 0 for j in numerical.values()):
        raise ValueError('the numerical embedding is out of scope')

    def rename(a):
        return target.walk(a, lambda i, d: numerical[i] if i < 0 else i)

    for j, (base, body) in enumerate(source_context):
        expected = (rename(base) if base else [], rename(body))
        if target_context[clauses[j]] != expected:
            raise ValueError('clause embedding mismatch')

    code, *args = proof
    if type(code) is int:
        term, antecedent = args

        def rebuild(local_target):
            return translate(antecedent, source_context, local_target,
                             numerical, clauses)

        result = p.use(target_context, clauses[code], rename(term),
                       rebuild if source_context[code][0] else None)
    elif code:
        witness, branch = args
        old_fresh = -len(source_context)
        old_body = source.sub(code, witness, 1)
        old_base = source.sub(old_body, 0)
        old_hyp = (source.sub(old_body, old_fresh)
                   if old_base == [0, 0] else old_base)
        local_source = source_context + [([], old_hyp)]

        def rebuild(local_target, step_goal):
            fresh = 1 - len(local_target)
            extended = dict(numerical)
            extended[old_fresh] = fresh
            result = translate(branch, local_source, local_target, extended,
                               clauses + [len(local_target) - 1])
            if target.prove(result, local_target) != step_goal:
                raise ValueError('translated successor branch mismatch')
            return result

        result = p.arbitrary_intro(rename(code), rename(witness), rebuild,
                                   target_context)
    else:
        major, branch = args
        old_body, = source.prove(major, source_context)
        old_fresh = -len(source_context)
        old_open = source.sub(old_body, old_fresh, 1)
        local_source = source_context + [(source.sub(old_open, 0), old_open)]
        new_major = translate(major, source_context, target_context,
                              numerical, clauses)
        new_body, = target.prove(new_major, target_context)
        fresh = -len(target_context)
        new_open = target.sub(new_body, fresh, 1)
        local_target = target_context + [(target.sub(new_open, 0), new_open)]
        extended = dict(numerical)
        extended[old_fresh] = fresh
        new_branch = translate(branch, local_source, local_target, extended,
                               clauses + [len(target_context)])
        result = [[], new_major, new_branch]
    if target.prove(result, target_context) != rename(expected_source):
        raise ValueError('translation changed the conclusion')
    return result


if __name__ == '__main__':
    goal, proof = json.load(sys.stdin)
    source.check([goal, proof])
    result = [goal, translate(proof)]
    target.check(result)
    json.dump(result, sys.stdout, separators=(',', ':'))
    sys.stdout.write('\n')
