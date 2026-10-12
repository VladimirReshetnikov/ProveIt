"""Amortized-linear cyclic free reduction and singleton endpoint descent.

Adapted from reports/34/braidkernel/descent.py (MIT-0).
Trace indices refer to original letters; no step stores an entire word.
The endpoint algorithm does not discover internal connected-sum cuts.
"""
from __future__ import annotations
from collections import deque



def linear_descent(strands, word, check):
    """Internal entry: the caller validates the explicit braid first."""
    check()
    w, n = word, len(word)
    if strands > n+1:
        raise ValueError("linear certificate requires strands <= input letters + 1")
    next_ = [(i+1) % n for i in range(n)]
    prev = [(i-1) % n for i in range(n)]
    active = [True]*n
    count, position_xor = [0]*strands, [0]*strands
    for i,g in enumerate(w):
        if i & 255 == 0:
            check()
        count[abs(g)] += 1
        position_xor[abs(g)] ^= i
    head, size, lo, hi = (0 if n else -1), n, 0, strands
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
            if queue_pops & 255 == 0:
                check()
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
        check()
        if hi-lo <= 3:
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
        for index in range(size):
            if index & 255 == 0:
                check()
            positions.append(p)
            p = next_[p]
    final = tuple((1 if w[p] > 0 else -1)*(abs(w[p])-lo) for p in positions)
    certificate = {'kind': 'singleton-markov-descent-v2', 'input_strands': strands,
                   'input_length': n, 'steps': steps, 'final_positions': positions,
                   'final_strands': hi-lo, 'final_word': list(final),
                   'queue_pops': queue_pops}
    return hi-lo, final, certificate


def verify_descent(strands, word, certificate, check):
    """Linear replay checks every local move, without testing search choices.

    It proves the supplied equivalence; it does not certify maximal descent.
    queue_pops is a diagnostic, not a trusted mathematical assertion.
    """
    check()
    fields = {'kind', 'input_strands', 'input_length', 'steps', 'final_positions',
              'final_strands', 'final_word', 'queue_pops'}
    if set(certificate) != fields or certificate['kind'] != 'singleton-markov-descent-v2':
        raise ValueError('unknown descent certificate')
    w, n = word, len(word)
    if strands > n+1:
        raise ValueError("linear certificate requires strands <= input letters + 1")
    for key in ('input_strands', 'input_length', 'final_strands', 'queue_pops'):
        if type(certificate[key]) is not int:
            raise ValueError('integer certificate field required')
    for key in ('final_positions', 'final_word'):
        if (type(certificate[key]) is not list or len(certificate[key]) > n
                or any(type(x) is not int for x in certificate[key])):
            raise ValueError('invalid terminal sequence')
    if not 0 <= certificate['queue_pops'] <= 2*n:
        raise ValueError('invalid queue diagnostic')
    if certificate.get('input_strands') != strands or certificate.get('input_length') != n:
        raise ValueError('wrong input dimensions')
    nxt = [(i+1) % n for i in range(n)]
    prv = [(i-1) % n for i in range(n)]
    live = [True]*n
    count = [0]*strands
    for index, g in enumerate(w):
        if index & 255 == 0:
            check()
        count[abs(g)] += 1
    lo, hi, size, head = 0, strands, n, (0 if n else -1)
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
        check()
        if not isinstance(step, dict):
            raise ValueError('invalid move record')
        if step.get('op') == 'cancel':
            if set(step) != {'op', 'first', 'second'}:
                raise ValueError('invalid cancellation fields')
            a, z = step.get('first'), step.get('second')
            check_position(a); check_position(z)
            if a == z or nxt[a] != z or w[a] != -w[z]:
                raise ValueError('invalid cyclic inverse cancellation')
            remove(a); remove(z)
        elif step.get('op') == 'destabilize':
            if set(step) != {'op', 'position', 'side'}:
                raise ValueError('invalid destabilization fields')
            p, side = step.get('position'), step.get('side')
            check_position(p)
            if hi-lo <= 3 or side not in ('left', 'right'):
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
        for index in range(size):
            if index & 255 == 0:
                check()
            positions.append(p)
            p = nxt[p]
    final = tuple((1 if w[p] > 0 else -1)*(abs(w[p])-lo) for p in positions)
    if (certificate['final_positions'] != positions
            or certificate['final_strands'] != hi-lo or certificate['final_word'] != list(final)):
        raise ValueError('claimed terminal word differs from replay')
    check()
    return hi-lo, final
