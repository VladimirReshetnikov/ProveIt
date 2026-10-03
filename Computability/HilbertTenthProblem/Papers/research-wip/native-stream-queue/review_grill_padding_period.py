#!/usr/bin/env python3
"""Independent period-padding synchronization and input-cone audit."""
import argparse
from collections import Counter, deque
import hashlib
import itertools
import json
from pathlib import Path

PIN = '299acc95d66b60fb7fe2b3e3a85ffd3ec7c77f8c53ce2f11d1b59d9f7d59ba48'

def need(ok, message):
    if not ok:
        raise ValueError(message)

def prefix(program, word, phase, steps):
    queue = deque(word)
    heads = []
    for _ in range(steps):
        need(bool(queue), 'early empty queue before prefix exhausted')
        bit = queue.popleft(); heads.append(bit)
        if bit:
            queue.extend((0,))
            for _ in range(program[phase]):
                queue.extend((1, 0))
        phase = (phase + 1) % len(program)
    return tuple(queue), phase, tuple(heads)

def fate(program, word, limit=256):
    seen = {}; phase = 0; word = tuple(word); heads = []
    for t in range(limit+1):
        if not word:
            return dict(kind='halt', time=t, heads=heads)
        state = (word, phase)
        if state in seen:
            return dict(kind='cycle', start=seen[state], period=t-seen[state])
        seen[state] = t
        word, phase, consumed = prefix(program, word, phase, 1)
        heads.extend(consumed)
    raise ValueError('fixture neither halts nor has a proved repeated state')

def bits(x, width):
    need(x > 0 and 2**width > x, 'ordinary binary width')
    return tuple((x >> i) & 1 for i in range(width))

def verify(source):
    need(hashlib.sha256(source.read_bytes()).hexdigest() == PIN, 'author source pin')
    count = Counter()
    for m in range(1, 4):
        for program in itertools.product(range(3), repeat=m):
            for length in range(1, 7):
                for word in itertools.product((0, 1), repeat=length):
                    for phase in range(m):
                        state, endphase, heads = prefix(program, word, phase, length)
                        need(heads == word, 'all initial symbols consumed first')
                        for q in (1, 2):
                            padding = q*m
                            after_initial, padded_phase, padded_heads = prefix(program, word+(0,)*padding, phase, length)
                            need(after_initial == (0,)*padding+state and padded_heads == word, 'literal zero-prefix identity')
                            after_padding, final_phase, zero_heads = prefix(program, after_initial, padded_phase, padding)
                            need(after_padding == state and final_phase == endphase, 'exact synchronized configuration')
                            need(zero_heads == (0,)*padding, 'padding appends nothing')
                            count['exact_period_synchronizations'] += 1
    # Both strict cones reduce to one representative per residue modulo m.
    for m, x, multiplier in itertools.product(range(1, 8), range(1, 128), (1, 3)):
        ell_min = (multiplier*x).bit_length()
        need(2**ell_min > multiplier*x and (ell_min == 0 or 2**(ell_min-1) <= multiplier*x), 'exact least strict width')
        for extra in range(3*m+1):
            quotient, residue = divmod(extra, m)
            ell = ell_min+extra; representative = ell_min+residue
            need(bits(x, ell) == bits(x, representative)+(0,)*(quotient*m), 'canonical finite padding residue')
            count['canonical_residue_identities'] += 1
        # Appending 2m zeros carries every weak-cone width into the strong cone.
        for extra in range(m):
            ell = x.bit_length()+extra
            need(2**(ell+2*m) > 3*x, 'uniform weak-to-strong lift')
            count['uniform_cone_lifts'] += 1
    fixtures = []
    for program, x, widths in (((0,1,1),2,(3,4,5)), ((1,0,0),1,(2,3)), ((2,0),1,(2,3))):
        for width in widths:
            need(2**width > 3*x, 'counterexample lies in original cone')
            result = fate(program, bits(x,width))
            fixtures.append(dict(program=program,x=x,width=width,**result))
    need([f['kind'] for f in fixtures] == ['cycle','cycle','halt','cycle','halt','halt','cycle'], 'padding changes halting truth')
    need(fixtures[2]['time']==9 and fixtures[4]['time']==7 and fixtures[5]['time']==9, 'literal first halts')
    # Repeated deterministic states are certificates of nonhalting, not timeouts.
    for f in fixtures:
        if f['kind']=='cycle':
            a,phase,_=prefix(f['program'],bits(f['x'],f['width']),0,f['start'])
            b,newphase,_=prefix(f['program'],a,phase,f['period'])
            need(a==b and phase==newphase and a, 'exact nonempty repeated configuration')
            count['certified_nonhalting_cycles'] += 1
        else:
            count['certified_first_halts'] += 1
    return json.loads(json.dumps(dict(status='PASS_INDEPENDENT_GRILL_PADDING_PERIOD',source_sha256=PIN,
        review_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),counts=dict(count),fixtures=fixtures,
        scope='Exact finite prefix synchronization supports the general deterministic proof; cycle fixtures prove nonhalting. Equality of existential input languages does not identify complete polynomials or positive witness fibers. No universal compiler established.')))

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source', type=Path, default=Path(__file__).with_name('grill_tag_padding_period.py'))
    p.add_argument('--output', type=Path)
    p.add_argument('--expect', type=Path)
    a = p.parse_args(); r = verify(a.source)
    if a.expect:
        need(r == json.loads(a.expect.read_text()), 'complete saved receipt')
    if a.output:
        a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
    print(json.dumps(r,indent=2,sort_keys=True))
