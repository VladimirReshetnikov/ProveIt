"""Exact strong state-quotient check and the spare-zero mutant's blank drift.

Neither result proves state minimality or a new consistency equivalence.
"""
import json
import independent_runtime as r


def main():
    table = r.table(r.BASE / 'candidate-routing245/zfc_routing245_old.tm')
    states = sorted({q for q, b in table})
    blocks = {q: 0 for q in states}
    counts = []
    while True:
        signatures = {}
        refined = {}
        for q in states:
            signature = tuple((w, d, blocks.get(n, -1)) for w, d, n in (table[q, 0], table[q, 1]))
            refined[q] = signatures.setdefault(signature, len(signatures))
        counts.append(len(signatures))
        if all((blocks[a] == blocks[b]) == (refined[a] == refined[b]) for a in states for b in states):
            break
        blocks = refined
    assert len(set(refined.values())) == 245
    mutant = r.table(r.OUT / 'candidates/candidate_appendzero244_old.tm')
    state, head, ones = 95, 0, set()
    for _ in range(77):
        write, move, target = mutant[state, int(head in ones)]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += move
        state = target
    assert state == 42 and head == 5 and all(x < head for x in ones)
    assert mutant[42, 0] == (1, 1, 42)
    # Induction: each next head cell is a previously blank cell to the right;
    # this exact row writes one, advances right, and remains in state 42.
    report = {
        'status': 'PASS',
        'strong_quotient_refinement_block_counts': counts,
        'strong_quotient_final_blocks': 245,
        'sparezero_blank_steps_to_rightward_drift': 77,
        'drift_state': state,
        'drift_head': head,
        'right_exterior_blank': True,
        'drift_row': list(mutant[42, 0]),
        'scope': 'Strong one-step quotient only; drift is this mutant\u2019s actual blank behavior, not a consistency-theoretic separation.'
    }
    (r.OUT / 'quotient-and-drift-reproduction.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
