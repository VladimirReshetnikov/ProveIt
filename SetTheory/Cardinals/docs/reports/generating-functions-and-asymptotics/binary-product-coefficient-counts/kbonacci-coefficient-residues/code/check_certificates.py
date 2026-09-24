"""Independent verifier for the two modulo-three JSON certificates.

This deliberately does not import the main implementation. It reconstructs
all transitions and all sequence entries from the certificate's state list,
then applies the finite tests justified by the article's Cayley--Hamilton
lemma. No floating-point arithmetic or third-party package is used.
"""
from __future__ import annotations

import json
from pathlib import Path


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def check_file(path: Path) -> None:
    data = json.loads(path.read_text())
    k, m = data['k'], data['modulus']
    require(k >= 2 and m >= 2, 'invalid parameters')
    states = [(tuple(s['counter']), s['run']) for s in data['states']]
    edges = data['edges_by_input_0_1']
    N = len(states)
    require(N == len(edges) == data['matrix_dimension'], 'dimension mismatch')
    index = {s:i for i,s in enumerate(states)}
    require(len(index) == N, 'duplicate state')
    require(data['initial_state'] == 0, 'unexpected initial state index')
    require(states[0] == ((1,)+(0,)*k,0), 'incorrect initial state')
    for i,(v,r) in enumerate(states):
        require(len(v) == k+1 and all(0 <= c < m for c in v), 'invalid counter')
        require(0 <= r <= k and len(edges[i]) == 2, 'invalid run or edges')
        p, b = v[0], v[1:]
        for bit in (0,1):
            target = edges[i][bit]
            if bit == 0 and r == k:
                require(target == -1, 'forbidden input not rejected')
                continue
            if bit == 0:
                next_v, next_r = (p,(p+b[-1]) % m)+b[:-1], 0
            else:
                next_v, next_r = ((p+b[-1]) % m,b[-1])+(0,)*(k-1), min(k,r+1)
            require((next_v,next_r) in index, 'state space not closed')
            require(target == index[next_v,next_r], 'incorrect edge')
    seen, frontier = {0}, [0]
    for i in frontier:
        for j in edges[i]:
            if j >= 0 and j not in seen:
                seen.add(j)
                frontier.append(j)
    require(len(seen) == N, 'unreachable states in supplied reachable graph')
    P, Q = data['numerator_ascending'], data['denominator_ascending']
    d = len(Q)-1
    require(d > 0 and Q[0] == 1 and len(P) <= d, 'invalid rational candidate')
    counts = [1]+[0]*(N-1)
    sequence = []
    for _ in range(N+d):
        sequence.append(sum(counts[i] for i,(v,_) in enumerate(states)
                            if v[0] == data['target_residue']))
        nxt = [0]*N
        for i,row in enumerate(edges):
            for j in row:
                if j >= 0:
                    nxt[j] += counts[i]
        counts = nxt
    require(sequence == data['sequence_prefix'], 'prefix does not match graph')
    for n in range(N+d):
        coefficient = sum(Q[j]*sequence[n-j] for j in range(min(n,d)+1))
        expected = P[n] if n < len(P) else 0
        require(coefficient == expected, f'failed convolution at degree {n}')
    print(f'{path.name}: PASS; {N} states; {d} initial coefficients; '
          f'{N} zero residuals; all-n identity certified.')


if __name__ == '__main__':
    root = Path(__file__).resolve().parent.parent
    for k in (2,3):
        check_file(root/f'certificates/mod3_k{k}.json')
