"""Exact obstruction to a direct three-state Rule110 carry embedding.

The finite search enumerates rail LABEL assignments, not coefficient values.
Every coefficient/state space is solved over Q, and each rejected assignment
has an exact linear-consequence certificate valid over R and hence over Z.
"""
import argparse
from itertools import permutations, product
import json
from pathlib import Path
import sympy as sp


# (old state, logical input bit, logical output bit, next state).
# A remembers that the preceding bit was0; B remembers01; C remembers11.
TRANSITIONS = ((0, 0, 0, 0), (0, 1, 1, 1),
               (1, 0, 1, 0), (1, 1, 1, 2),
               (2, 0, 1, 0), (2, 1, 0, 2))
RAILS = {0: ((0, 0),), 1: ((1, 0), (0, 1)), 2: ((1, 1),)}
VARIABLES = ('state_A', 'state_B', 'state_C',
             'read0_weight', 'read1_weight',
             'append0_weight', 'append1_weight', 'offset')


def edge_row(old, read, append, new):
    row = [0] * len(VARIABLES)
    row[new] += 3
    row[old] -= 1
    for index, bit in enumerate(read + append):
        row[3 + index] -= bit
    row[7] -= 1
    return row


def dot(left, right):
    return sum(a * b for a, b in zip(left, right))


def forced(row, nullspace):
    return all(dot(row, vector) == 0 for vector in nullspace)


def certificate(matrix, row):
    """Supply an exact row-space witness, independently of annihilation."""
    solution, parameters = matrix.T.gauss_jordan_solve(sp.Matrix(row))
    values = solution.subs({parameter: 0 for parameter in parameters})
    assert matrix.T * values == sp.Matrix(row)
    return [str(value) for value in values]


def audit_encoding(encoding):
    choices = [tuple(product(RAILS[encoding[bit]], RAILS[encoding[out]]))
               for old, bit, out, new in TRANSITIONS]
    records = []
    collisions = bad_edges = only_uncoded = 0
    for index, assignment in enumerate(product(*choices)):
        rows = [edge_row(old, read, append, new)
                for (old, bit, out, new), (read, append)
                in zip(TRANSITIONS, assignment)]
        # Translation of all state codes is absorbed by the arbitrary offset.
        rows.append([1, 0, 0, 0, 0, 0, 0, 0])
        matrix = sp.Matrix(rows)
        basis = matrix.nullspace()
        record = dict(assignment_index=index,
                      selected_rails=[[list(read), list(append)]
                                      for read, append in assignment],
                      rank=matrix.rank())
        collision = None
        for left, right in ((0, 1), (0, 2), (1, 2)):
            row = [int(i == left) - int(i == right) for i in range(8)]
            if forced(row, basis):
                collision = (left, right, row)
                break
        if collision is not None:
            left, right, row = collision
            record.update(outcome='forced_state_collision',
                          states=[left, right],
                          consequence=row, row_combination=certificate(matrix, row))
            collisions += 1
        else:
            wrong = []
            for old, bit, output_trit, new in product(range(3), range(2), range(3), range(3)):
                if any((old, bit, new) == (source, read_bit, target)
                       and output_trit == encoding[out_bit]
                       for source, read_bit, out_bit, target in TRANSITIONS):
                    continue
                for read, append in product(RAILS[encoding[bit]], RAILS[output_trit]):
                    row = edge_row(old, read, append, new)
                    if forced(row, basis):
                        wrong.append((output_trit not in encoding,
                                      old, bit, output_trit, new, read, append, row))
            # Prefer a coded but incorrect output when one is forced.
            wrong.sort()
            assert wrong, (encoding, index, assignment)
            uncoded, old, bit, output_trit, new, read, append, row = wrong[0]
            only_uncoded += uncoded
            record.update(outcome='forced_unwanted_internal_edge',
                          old_state=old, input_bit=bit, output_trit=output_trit,
                          next_state=new, read_rails=list(read), append_rails=list(append),
                          only_uncoded_output_witness=uncoded,
                          consequence=row, row_combination=certificate(matrix, row))
            bad_edges += 1
        records.append(record)
    return dict(symbol_encoding=list(encoding), assignments=len(records),
                forced_state_collisions=collisions,
                nondegenerate_assignment_spaces=bad_edges,
                forced_bad_coded_output_edges=bad_edges - only_uncoded,
                assignments_with_only_uncoded_output_witness=only_uncoded,
                exact_embeddings=0, records=records)


def illustrative_subgraph():
    values = (0, 1, 2, 4, 6, -1, -2, 0)
    selected = []
    for old, bit, out, new in TRANSITIONS:
        matches = [(read, append) for read, append in product(RAILS[bit], RAILS[out])
                   if dot(edge_row(old, read, append, new), values) == 0]
        assert matches
        selected.append(dict(transition=[old, bit, out, new],
                             read_rails=list(matches[0][0]), append_rails=list(matches[0][1])))
    bad = edge_row(0, (0, 1), (0, 0), 2)
    assert dot(bad, values) == 0
    return dict(state_codes=list(values[:3]), weights=list(values[3:7]), offset=values[7],
                desired_subgraph=selected,
                unwanted_edge=dict(old_state=0, input_bit=1, output_trit=0, next_state=2,
                                   read_rails=[0, 1], append_rails=[0, 0]))


def verify():
    audits = [audit_encoding(encoding) for encoding in permutations(range(3), 2)]
    assignments = sum(row['assignments'] for row in audits)
    viable = sum(row['nondegenerate_assignment_spaces'] for row in audits)
    uncoded = sum(row['assignments_with_only_uncoded_output_witness'] for row in audits)
    assert assignments == 322 and viable == 96 and uncoded == 8
    return dict(status='PASS_NO_EXACT_DIRECT_THREE_STATE_RULE110_EMBEDDING',
                variables=list(VARIABLES), logical_transitions=[list(row) for row in TRANSITIONS],
                assignment_count=assignments, nondegenerate_assignment_spaces=viable,
                exact_embeddings=0, encoding_audits=audits,
                illustrative_subgraph=illustrative_subgraph(),
                scope=('One carry value per minimal Rule110 transducer state; one scalar trit per binary symbol; '
                       'all six fixed injective symbol codes; arbitrary real and hence integer weights/offset. '
                       'Unwanted edges include an uncoded output trit. No serialization, accepting-language, '
                       'or general universality obstruction is asserted.'),
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
    summary = {key: value for key, value in result.items() if key != 'encoding_audits'}
    summary['encoding_counts'] = [{key: value for key, value in row.items() if key != 'records'}
                                  for row in result['encoding_audits']]
    print(json.dumps(summary, indent=2))
