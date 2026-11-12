"""Targeted fallback-to-extraction substitution experiment for opening.

The outer passive parameter a is specialized to 0. A previously default
opening then selects the witness 1. The source smaller branch must receive
the combined substitution a->0, b->1; passive substitution alone is wrong.
This is one concrete experiment, not a generic substitution compiler.
"""
from pathlib import Path
import json

import macros_open as m
from inherited_reference_kernel import normal, map_syntax
from translate import selection

ROOT = Path(__file__).resolve().parent.parent


def substitute_proof(proof, assignments):
    def syntax(tree):
        return normal(map_syntax(tree, lambda i, d: assignments.get(i, i)))
    tag = proof[0]
    if tag == 'u':
        return ['u', proof[1], syntax(proof[2]),
                substitute_proof(proof[3], assignments) if proof[3] is not None else None]
    if tag == 'i':
        return ['i', syntax(proof[1]), substitute_proof(proof[2], assignments)]
    if tag == 'e':
        return ['e', syntax(proof[1]), substitute_proof(proof[2], assignments),
                substitute_proof(proof[3], assignments)]
    raise ValueError('unknown proof instruction')


def main():
    a = -1
    context = [([], [1, 1])]
    good_left = m.C(m.Y, 0, m.C(m.parity(m.Y), 0, m.X))
    good_right = m.C(m.Y, 0, m.C(m.parity(m.Y), 0, m.ONE))
    matrix = [m.C(a, good_left, 0), m.C(a, good_right, 0)]
    paired = m.D(matrix)
    major = m.introduce(paired, m.ONE,
                        lambda z, g, n, expected: m.refl(expected[0]), context, 1)
    def outer_branch(b, local, scope):
        # This row is C(a,b,0)=C(a,1,0), and is actually consumed below.
        row = m.use(1, m.ONE, m.refl(m.C(a, 0, 0)), local, scope)
        gate = m.D([m.C(m.Y, 0, row.goal[0]), m.C(m.Y, 0, row.goal[1])], m.W, m.Y)
        gated = m.introduce(gate, m.ONE,
                            lambda z, g, n, expected: m.weaken(row, scope, len(local)), local, scope)
        # The dummy gate is opened and then discarded. Its major still has
        # to prove the row, so replacing only a cannot bypass the mismatch.
        return m.eliminate(gated, lambda bb, gg, nn: m.refl(0), local, scope)
    source = m.eliminate(major, outer_branch, context, 1)
    m.candidate.prove(source.goal, source.proof, context, 1)
    old_body, old_base, old_target, old_extracted = selection(source.proof[1], 1)
    m.ensure(not old_extracted and old_target == -2, 'source did not use default mode')

    naive = substitute_proof(source.proof, {a: 0})
    new_body, new_base, new_target, new_extracted = selection(naive[1], 1)
    m.ensure(new_extracted and new_target == m.ONE, 'specialization did not select 1')
    try:
        m.candidate.prove(source.goal, naive, context, 1)
    except Exception:
        naive_rejected = True
    else:
        raise ValueError('passive-only substitution unexpectedly accepted')

    repaired = ['e', naive[1], naive[2], substitute_proof(source.proof[3], {a: 0, -2: m.ONE})]
    m.candidate.prove(source.goal, repaired, context, 1)
    record = {'scope': 1, 'context': context, 'goal': source.goal,
              'source_proof': source.proof, 'passive_only_proof': naive, 'repaired_proof': repaired,
              'source_verdict': 'ACCEPT', 'passive_only_verdict': 'REJECT', 'repaired_verdict': 'ACCEPT',
              'source_mode': 'default with fresh b=-2', 'specialized_mode': 'extracted witness 1',
              'repair': 'Apply a->0,b->1 simultaneously to the original smaller outer branch; keep a->0 alone on the outer major.',
              'limit': 'Concrete proof-level experiment, not a generic executable substitution theorem.'}
    (ROOT / 'validation/fallback_to_extraction.json').write_text(json.dumps(record, indent=2) + '\n')
    summary = {key: record[key] for key in ['source_verdict', 'passive_only_verdict', 'repaired_verdict',
                                           'source_mode', 'specialized_mode', 'repair', 'limit']}
    (ROOT / 'evidence/substitution_transition.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary))


if __name__ == '__main__':
    main()
