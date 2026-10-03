"""Full accepted uncoded run for the fixed 01/10 serialized candidate."""
import argparse
from itertools import combinations, product
import hashlib
import json
from pathlib import Path
import sympy as sp
import native_dualrail_fifo67 as fifo


STATES = {'A': 0, 'B': 8, 'C': 4}
CODE = {0: (0, 1), 1: (1, 0)}
WEIGHTS = (8, 4, -88, -40)  # append0, append1, read0, read1
EDGES = [('A', 0, 0, 'A'), ('A', 1, 1, 'B'),
         ('B', 0, 1, 'A'), ('B', 1, 1, 'C'),
         ('C', 0, 1, 'A'), ('C', 1, 0, 'C')]
LABELS = tuple(product((0, 1), repeat=4))


def desired_paths():
    records = []
    rows = []
    for source, read, append, target in EDGES:
        paths = []
        for labels in product(LABELS, repeat=2):
            if tuple(sum(label[2:]) for label in labels) != CODE[read]:
                continue
            if tuple(sum(label[:2]) for label in labels) != CODE[append]:
                continue
            carry = STATES[source]
            carries = [carry]
            for label in labels:
                numerator = carry + 27 + sum(c * bit for c, bit in zip(WEIGHTS, label))
                if numerator % 3:
                    break
                carry = numerator // 3
                carries.append(carry)
            else:
                if carry == STATES[target]:
                    paths.append((labels, carries))
        assert len(paths) == 1
        labels, carries = paths[0]
        words = tuple(labels[0][i] + 3 * labels[1][i] for i in range(4))
        rows.append(words)
        records.append(dict(edge=[source, read, append, target],
                            labels=[list(label) for label in labels],
                            carries=carries, rail_words=list(words)))
    augmented = sp.Matrix([list(row) + [1] for row in rows])
    assert augmented.rank() == 5 and not augmented.nullspace()
    minor = next(indices for indices in combinations(range(6), 5)
                 if augmented[list(indices), :].det())
    for i, j in combinations(range(4), 2):
        assert any(row[i] != row[j] for row in rows)
        assert any(row[i] + row[j] != 4 for row in rows)
    return dict(uniquely_realized_desired_edges=records,
                augmented_rank=5, nonzero_minor_rows=list(minor),
                nonzero_minor_determinant=int(augmented[list(minor), :].det()),
                scope='No fixed affine block identity, in particular no rail equality or complement, preserves all six edges')


def accepted_uncoded_run():
    # Each row is (append0, append1, read0, read1), low-time first.
    labels = [(1, 1, 0, 0), (0, 0, 0, 1),
              (1, 1, 0, 0), (0, 0, 1, 0),
              (0, 0, 1, 1), (0, 0, 0, 0),
              (0, 0, 1, 1), (1, 0, 0, 0),
              (0, 0, 0, 0), (0, 0, 0, 0),
              (0, 0, 0, 0), (0, 0, 0, 1)]
    width = 81
    initial = 30
    carry = 0
    queue = initial
    carries = [carry]
    queues = [queue]
    for label in labels:
        assert queue % 3 == sum(label[2:])
        numerator = carry + 27 + sum(c * bit for c, bit in zip(WEIGHTS, label))
        assert numerator % 3 == 0
        carry = numerator // 3
        queue = queue // 3 + (width // 3) * sum(label[:2])
        assert 0 <= queue < width
        carries.append(carry)
        queues.append(queue)
    assert carry == queue == 0
    assert tuple(initial // 3 ** j % 3 for j in range(4)) == CODE[0] + CODE[0]
    assert labels[0][0] == 1
    reads = tuple(sum(label[2:]) for label in labels)
    appends = tuple(sum(label[:2]) for label in labels)
    read_blocks = [reads[j:j + 2] for j in range(0, len(labels), 2)]
    append_blocks = [appends[j:j + 2] for j in range(0, len(labels), 2)]
    assert append_blocks[0] == (2, 0)
    assert read_blocks[2] == read_blocks[3] == (2, 0)
    assert any(block not in CODE.values() for block in append_blocks)

    t = len(labels)
    q = 3 ** t
    H = (q - 1) // 2
    words = [sum(label[i] * 3 ** j for j, label in enumerate(labels)) for i in range(4)]
    fields = [H + word for word in words]
    index = sum(field * q ** i for i, field in enumerate(fields))
    values = dict(x=15, W=width, q=q, r=index, beta=width-initial, L=q//width,
                  **{f'F{i}': field for i, field in enumerate(fields)},
                  **{f'alpha{i}': q-field for i, field in enumerate(fields)})
    assert min(values.values()) > 0
    outer = [row for row in fifo.base.prior.OUTER if row[0] != 'even_r']
    env = fifo.selector.execute(outer + [('twice_H', '-', 'q', 1)] + fifo.EXTRA66, values)
    for i in range(4):
        assert env[f'bound{i}'] == q
    for left, right in [('r', 'packed'), ('read_sum', 'transport'),
                        ('width_bound', 'W'), ('q', 'length_product')]:
        assert env[left] == env[right]
    assert index % 2 == 0 and fifo.selector.valuation(index) == 4 * t

    # Double all carry data to obtain the general75 integer program numerals.
    doubled_weights = tuple(2 * c for c in WEIGHTS)
    offset = 54
    lam = (offset - sum(doubled_weights)) // 2
    assert lam == 143
    assert sum(c * field for c, field in zip(doubled_weights, fields)) + lam * (q - 1) == 0
    for j, label in enumerate(labels):
        assert 3 * (2 * carries[j + 1]) == 2 * carries[j] + offset + sum(
            c * bit for c, bit in zip(doubled_weights, label))
    D, A = sum(words[2:]), sum(words[:2])
    assert D == initial + width * A
    assert D + A < q and initial == 6 * 5
    return dict(width=width, width_exponent=4, initial=initial, time=t,
                labels=[list(label) for label in labels], carries=carries, queues=queues,
                read_blocks=[list(block) for block in read_blocks],
                append_blocks=[list(block) for block in append_blocks],
                positive_outer_values=values, rail_words=words,
                read_sum=D, append_sum=A,
                hypothetical_joint_bound_slack=q-D-A,
                hypothetical_I6x_input=5,
                fixed_general75_program=dict(weights=list(doubled_weights), h=offset,
                                             cs=0, cf=0, fixed_lambda=lam, fixed_delta=0),
                kernel_extension='Exact reviewed65 positive converse; auxiliary tuple proved parametrically, not materialized')


def verify():
    audit = fifo.source_check(True, False)
    general = fifo.conditional_carry_schedule(True, False, True)
    assert audit['operations'] == 65 and general['candidate_total'] == 75
    return dict(status='PASS_SERIALIZED_RULE110_UNCODED_ACCEPTED_FIFO',
                desired_transition_audit=desired_paths(), counterexample=accepted_uncoded_run(),
                audited_base_operations=65, audited_general_architecture=75,
                dependency_sha256=hashlib.sha256(Path(fifo.__file__).read_bytes().replace(b'\r\n', b'\n')).hexdigest(),
                scope='Fixed01/10 candidate only: existing FIFO and eventual zero acceptance do not force code typing; no universality obstruction',
                established_complete_universal_bound=76)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = verify()
    receipt = Path(__file__).with_suffix('.json')
    if args.write:
        receipt.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    else:
        assert json.loads(receipt.read_text()) == result, 'receipt mismatch'
    print(json.dumps({key: value for key, value in result.items() if key != 'dependency_sha256'}, indent=2))
