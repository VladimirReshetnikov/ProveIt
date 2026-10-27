"""Exact component prototype, not a SAT solver. Authored for this study.

Both engines make the same conditional-expectation decisions, including ties.
The reference independently evaluates the literal candidate sum. No imported
research program is executed. Counters count candidate-score rational
arithmetic only, excluding shared setup and updates; they are not bit times.
"""
from fractions import Fraction as F


def require(ok, message):
    if not ok:
        raise ValueError(message)


def balance(matrix, labels, h=8, engine='incremental', trace=False):
    require(type(labels) is int and labels > 0, 'positive integer label count')
    require(type(h) is int and h >= 2, 'integer smoothness at least two')
    require(engine in ('incremental', 'reference', 'cached'), 'known engine')
    A = [list(row) for row in matrix]
    nv = len(A[0]) if A else 0
    require(all(len(row) == nv for row in A), 'rectangular matrix')
    require(all(type(x) is int and x >= 0 for row in A for x in row), 'nonnegative multiplicities')
    Q = labels
    C = max([sum(row[j] for row in A) for j in range(nv)] + [1])
    z = F(h*C+1, h*C)
    mass = sum(map(sum, A))
    # Identical power table for the two engines isolates score computation.
    powers = [F(1)]
    for _ in range(mass):
        powers.append(powers[-1]*z)
    totals = [0]*Q
    rows = []
    for row in A:
        a = min(range(Q), key=lambda b: (totals[b], b))
        totals[a] += sum(row)
        rows.append(a)
    W = [dict() for _ in range(nv)]
    for a, row in zip(rows, A):
        for j, w in enumerate(row):
            if w:
                W[j][a] = W[j].get(a, 0)+w
    factors = [{a: (Q-1+powers[w])/Q for a,w in col.items()} for col in W]
    future = [F(1)]*Q
    for col in factors:
        for a, f in col.items():
            future[a] *= f
    initial = Q*sum(future)
    current = initial
    loads = [[0]*Q for _ in range(Q)]
    row_sums = [F(Q)]*Q
    choices, certificates = [], []
    ops = dict(add=0, mul=0, div=0, candidate_terms=0)
    for j, col in enumerate(W):
        after = {a: future[a]/factors[j][a] for a in col}
        ops['div'] += len(col)
        if engine == 'cached':
            # Prior packet already caches row sums. This stronger comparator
            # also shares our streaming future products and power table.
            scores = []
            for b in range(Q):
                score = F(0)
                for a in range(Q):
                    old = loads[a][b]
                    subtotal = row_sums[a]-powers[old]+powers[old+col.get(a,0)]
                    score += after.get(a, future[a])*subtotal
                    ops['add'] += 3
                    ops['mul'] += 1
                    ops['candidate_terms'] += 1
                scores.append(score)
            chosen = min(range(Q), key=lambda b: (scores[b], b))
            new = scores[chosen]
        elif engine == 'reference':
            scores = []
            for b in range(Q):
                score = F(0)
                for a in range(Q):
                    subtotal = F(0)
                    for k in range(Q):
                        subtotal += powers[loads[a][k] + (col.get(a,0) if k == b else 0)]
                        ops['add'] += 1
                        ops['candidate_terms'] += 1
                    score += after.get(a, future[a])*subtotal
                    ops['mul'] += 1
                    ops['add'] += 1
                scores.append(score)
            chosen = min(range(Q), key=lambda b: (scores[b], b))
            new = scores[chosen]
        else:
            base = current
            deltas = [F(0)]*Q
            for a, w in col.items():
                base += (after[a]-future[a])*row_sums[a]
                coefficient = after[a]*(powers[w]-1)
                ops['add'] += 3
                ops['mul'] += 2
                for b in range(Q):
                    deltas[b] += coefficient*powers[loads[a][b]]
                    ops['mul'] += 1
                    ops['add'] += 1
                    ops['candidate_terms'] += 1
            chosen = min(range(Q), key=lambda b: (deltas[b], b))
            new = base+deltas[chosen]
            ops['add'] += 1
            scores = [base+d for d in deltas] if trace else None
        if trace:
            require(sum(scores)/Q == current, 'averaging identity')
            certificates.append(tuple(scores))
        require(new <= current, 'potential decreased')
        for a, w in col.items():
            row_sums[a] += powers[loads[a][chosen]]*(powers[w]-1)
            loads[a][chosen] += w
            future[a] = after[a]
        current = new
        choices.append(chosen)
    final = sum(powers[x] for row in loads for x in row)
    require(final == current and final <= initial, 'final certificate')
    return dict(rows=rows, columns=choices, loads=loads, initial=initial,
                final=final, scores=certificates, operations=ops,
                active_pairs=sum(map(len,W)), mass=mass)
