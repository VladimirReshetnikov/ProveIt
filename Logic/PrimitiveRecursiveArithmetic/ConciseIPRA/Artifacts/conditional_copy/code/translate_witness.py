"""Untrusted general proof translation deleting supplied Intro witnesses.

Source: control_witness.py, with an explicit witness and the same
exact-truth selector and inferred Export. Target: checker.py.

The recursion is on the SOURCE certificate. Source branches are retranslated
under injective embeddings of numerical scopes, never weakened as already
built target proofs. This is the executable form of the completeness proof.
"""
import copy
import json
import sys

import checker as target
import control_witness as source
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

    code, *args = proof
    if type(code) is int:
        term, antecedent = args
        premise = (translate(antecedent, source_context, target_context,
                             numerical, clauses)
                   if source_context[code][0] else None)
        result = [clauses[code], rename(term), premise]
    elif code:
        witness, branch = args
        old_fresh = -len(source_context)
        old_body = source.sub(code, witness, 1)
        old_base = source.sub(old_body, 0)
        old_hyp = (source.sub(old_body, old_fresh)
                   if old_base == [0, 0] else old_base)
        local_source = source_context + [([], old_hyp)]

        def rebuild(local_target, step_goal):
            # local_target's last clause and parameter are precisely those
            # introduced for the q_y B(witness,y) branch in arbitrary_intro.
            fresh = 1 - len(local_target)
            extended = dict(numerical)
            extended[old_fresh] = fresh
            translated = translate(branch, local_source, local_target,
                                   extended, clauses + [len(local_target) - 1])
            if target.prove(translated, local_target) != step_goal:
                raise ValueError('translated successor branch mismatch')
            return translated

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
        new_branch = translate(branch, local_source, local_target,
                               extended, clauses + [len(target_context)])
        result = [[], new_major, new_branch]
    if target.prove(result, target_context) != rename(expected_source):
        raise ValueError('translation changed the conclusion')
    return result


def forget_determinism(proof, context=p.INITIAL):
    """The easy reverse inclusion, inserting the already selected witness."""
    code, *args = proof
    if type(code) is int:
        term, antecedent = args
        return [code, term, forget_determinism(antecedent, context)
                if context[code][0] else None]
    if code:
        branch, = args
        local, _ = p.intro_context([code], context)
        return [code, 1 - len(context), forget_determinism(branch, local)]
    major, branch = args
    matrix, = target.prove(major, context)
    body = target.sub(matrix, -len(context), 1)
    local = context + [(target.sub(body, 0), body)]
    return [[], forget_determinism(major, context),
            forget_determinism(branch, local)]


def check_round_trip(payload):
    goal, proof = payload
    target.check(payload)
    old = forget_determinism(proof)
    source.check([goal, old])
    new = translate(old)
    target.check([goal, new])
    return [goal, new]


if __name__ == '__main__':
    goal, proof = json.load(sys.stdin)
    source.check([goal, proof])
    output = [goal, translate(proof)]
    target.check(output)
    json.dump(output, sys.stdout, separators=(',', ':'))
    sys.stdout.write('\n')
