"""Replay exceptional-factor rank witnesses without choosing elimination pivots.

The explicit Frobenius complex is shared and reconstructed from the source;
rank reduction is independent of the producer and follows only checked XORs.
"""
from .cube import build_complex, check_chain, expand_leaf
from .verify import require


def integer_list(value, expected, message):
    require(isinstance(value, list) and all(type(v) is int for v in value)
            and value == expected, message)


def replay_rank(columns, rows, steps, check):
    require(isinstance(steps, list) and len(steps) == len(columns), 'wrong column trace count')
    basis, pivots = {}, set()
    for index, (original, step) in enumerate(zip(columns, steps)):
        check()
        require(isinstance(step, dict) and set(step) == {'xor', 'pivot'}, 'invalid rank step')
        require(isinstance(step['xor'], list), 'invalid XOR trace')
        vector = original
        used = set()
        for previous in step['xor']:
            check()
            require(type(previous) is int and previous in basis and previous not in used,
                    'XOR must refer to a distinct preceding basis column')
            used.add(previous)
            vector ^= basis[previous]
        pivot = step['pivot']
        require(type(pivot) is int and -1 <= pivot < rows, 'invalid pivot row')
        if pivot == -1:
            require(vector == 0, 'dependent column did not reduce to zero')
        else:
            require(vector.bit_length() - 1 == pivot and pivot not in pivots,
                    'residual is not a new triangular basis vector')
            basis[index] = vector
            pivots.add(pivot)
    # Distinct leading rows prove independence. Each input column is an XOR of
    # an earlier basis subset and its residual, proving equality of the spans.
    return len(basis)


def verify(data, summary, certificate, *, max_crossings, check, reserve):
    c = certificate
    require(isinstance(c, dict) and c.get('version') == 'exceptional-cube-f2-v1', 'invalid cube version')
    word = expand_leaf(data, summary['length'], max_crossings, check)
    require(type(c.get('strands')) is int and c['strands'] == data['strands'], 'wrong cube strands')
    integer_list(c.get('word'), word, 'cube word differs from source projection')
    dimensions, matrices = build_complex(data['strands'], word, check=check, reserve=reserve)
    check_chain(matrices, check)
    integer_list(c.get('dimensions'), dimensions, 'wrong cube dimensions')
    traces = c.get('elimination')
    require(isinstance(traces, list) and len(traces) == len(matrices), 'wrong differential count')
    ranks = [replay_rank(columns, dimensions[h+1], traces[h], check)
             for h, columns in enumerate(matrices)]
    integer_list(c.get('differential_ranks'), ranks, 'wrong differential ranks')
    homology = [dim - (ranks[h] if h < len(ranks) else 0) - (ranks[h-1] if h else 0)
                for h, dim in enumerate(dimensions)]
    require(all(v >= 0 for v in homology) and sum(homology) >= 1, 'invalid knot homology')
    integer_list(c.get('homology'), homology, 'wrong homology dimensions')
    status = 'UNKNOT' if sum(homology) == 1 else 'KNOTTED'
    require(c.get('status') == status, 'wrong cube verdict')
    return status
