"""Amortized-linear cyclic free reduction and singleton endpoint descent.

Trace indices refer to original letters; no step stores an entire word.
The endpoint algorithm does not discover internal connected-sum cuts.
"""
from __future__ import annotations
from collections import deque
from .core import Braid


def linear_descent(braid: Braid, *, stop_strands: int = 3) -> tuple[Braid, dict]:
    braid = Braid.checked(braid.strands, braid.word)
    if type(stop_strands) is not int or stop_strands < 1:
        raise ValueError('stop_strands must be positive')
    w, n = braid.word, len(braid.word)
    next_ = [(i+1) % n for i in range(n)]
    prev = [(i-1) % n for i in range(n)]
    active = [True]*n
    count, position_xor = [0]*braid.strands, [0]*braid.strands
    for i,g in enumerate(w):
        count[abs(g)] += 1
        position_xor[abs(g)] ^= i
    head, size, lo, hi = (0 if n else -1), n, 0, braid.strands
    queue = deque(range(n))
    steps = []
    queue_pops = 0

    def erase(i):
        nonlocal size, head
        a, z = prev[i], next_[i]
        active[i] = False
        count[abs(w[i])] -= 1
        position_xor[abs(w[i])] ^= i
        size -= 1
        if not size:
            head = -1
        else:
            next_[a], prev[z] = z, a
            if head == i:
                head = z
        return a, z

    while True:
        while queue:
            a = queue.popleft()
            queue_pops += 1
            if not active[a] or size < 2:
                continue
            z = next_[a]
            if w[a] != -w[z]:
                continue
            before = prev[a]
            steps.append({'op': 'cancel', 'first': a, 'second': z})
            erase(a)
            erase(z)
            if size:
                queue.append(before)
        if hi-lo <= stop_strands:
            break
        if count[hi-1] == 1:
            side, a = 'right', position_xor[hi-1]
        elif count[lo+1] == 1:
            side, a = 'left', position_xor[lo+1]
        else:
            break
        before, following = prev[a], next_[a]
        steps.append({'op': 'destabilize', 'side': side, 'position': a})
        erase(a)
        if size:
            head = following  # conjugate to put the removed endpoint last
            queue.append(before)
        if side == 'right':
            hi -= 1
        else:
            lo += 1
    positions = []
    if size:
        p = head
        for _ in range(size):
            positions.append(p)
            p = next_[p]
    final = Braid.checked(hi-lo, [(1 if w[p] > 0 else -1)*(abs(w[p])-lo) for p in positions])
    certificate = {'schema': 'linear-endpoint-descent-v1', 'input_strands': braid.strands,
                   'input_length': n, 'steps': steps, 'final_positions': positions,
                   'final_braid': final.to_json(), 'queue_pops': queue_pops,
                   'stop_strands': stop_strands}
    return final, certificate


def verify_descent(braid: Braid, certificate: dict) -> Braid:
    """Linear replay checks every local move, without testing search choices.

    It proves the supplied equivalence; it does not certify maximal descent.
    queue_pops is a diagnostic, not a trusted mathematical assertion.
    """
    braid = Braid.checked(braid.strands, braid.word)
    if not isinstance(certificate, dict) or certificate.get('schema') != 'linear-endpoint-descent-v1':
        raise ValueError('unknown descent certificate')
    w, n = braid.word, len(braid.word)
    if certificate.get('input_strands') != braid.strands or certificate.get('input_length') != n:
        raise ValueError('wrong input dimensions')
    nxt = [(i+1) % n for i in range(n)]
    prv = [(i-1) % n for i in range(n)]
    live = [True]*n
    count = [0]*braid.strands
    for g in w:
        count[abs(g)] += 1
    lo, hi, size, head = 0, braid.strands, n, (0 if n else -1)
    def check_position(p):
        if type(p) is not int or not 0 <= p < n or not live[p]:
            raise ValueError('position is not a live original letter')
    def remove(p):
        nonlocal size, head
        a, z = prv[p], nxt[p]
        count[abs(w[p])] -= 1
        live[p] = False
        size -= 1
        if size:
            nxt[a], prv[z] = z, a
            if head == p:
                head = z
        else:
            head = -1
    steps = certificate.get('steps')
    if not isinstance(steps, list) or len(steps) > n:
        raise ValueError('invalid trace length')
    for step in steps:
        if not isinstance(step, dict):
            raise ValueError('invalid move record')
        if step.get('op') == 'cancel':
            a, z = step.get('first'), step.get('second')
            check_position(a); check_position(z)
            if a == z or nxt[a] != z or w[a] != -w[z]:
                raise ValueError('invalid cyclic inverse cancellation')
            remove(a); remove(z)
        elif step.get('op') == 'destabilize':
            p, side = step.get('position'), step.get('side')
            check_position(p)
            if hi-lo < 2 or side not in ('left', 'right'):
                raise ValueError('invalid endpoint')
            endpoint = lo+1 if side == 'left' else hi-1
            if abs(w[p]) != endpoint or count[endpoint] != 1:
                raise ValueError('endpoint is not a singleton')
            following = nxt[p]
            remove(p)
            if size:
                head = following
            if side == 'left':
                lo += 1
            else:
                hi -= 1
        else:
            raise ValueError('unknown move')
    positions = []
    if size:
        p = head
        for _ in range(size):
            positions.append(p)
            p = nxt[p]
    final = Braid.checked(hi-lo, [(1 if w[p] > 0 else -1)*(abs(w[p])-lo) for p in positions])
    if certificate.get('final_positions') != positions or certificate.get('final_braid') != final.to_json():
        raise ValueError('claimed terminal word differs from replay')
    return final
