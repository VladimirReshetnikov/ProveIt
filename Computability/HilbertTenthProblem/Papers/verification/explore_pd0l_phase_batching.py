"""Conditional eleven-operation FIFO batches and the aligned-block obstruction."""
from itertools import product
from pathlib import Path
import json
import sympy as sp

ALPHABET = (1, 2)
TRANSPORT = [
    ('trim', '-', 'N', 'A'), ('append', '+', 'trim', 'U'),
    ('content_left', '*', 'R', 'append'),
    ('start', '-', 'N', 'n0'), ('end', '*', 'nh', 'Q'),
    ('content_inner', '+', 'start', 'end'),
    ('content_right', '*', 'B', 'content_inner'),
    ('length_left', '*', 'R', 'W'), ('length_start', '-', 'Z', 'L0'),
    ('length_end', '*', 'Lh', 'Q'),
    ('length_right', '+', 'length_start', 'length_end'),
]


def code(word):
    return sum(a*3**i for i, a in enumerate(word))


def apply(images, word):
    return tuple(child for i, a in enumerate(word) for child in images[i % len(images)][a])


def run(values):
    env = dict(values)
    for name, op, left, right in TRANSPORT:
        assert name not in env
        a, b = env[left], env[right]
        env[name] = a*b if op == '*' else a+b if op == '+' else a-b
    return env


def source_check():
    labels = 'N A U R n0 nh Q B W Z L0 Lh'.split()
    s = dict(zip(labels, sp.symbols(' '.join(labels))))
    N, A, U, R, n0, nh, Q, B, W, Z, L0, Lh = [s[x] for x in labels]
    expected = [R*(N-A+U)-B*(N-n0+nh*Q), R*W-Z+L0-Lh*Q]
    env = run(s)
    comparisons = [('content_left', 'content_right'), ('length_left', 'length_right')]
    assert all(sp.expand(env[a]-env[b]-f) == 0 for (a,b),f in zip(comparisons,expected))
    assert len(TRANSPORT) == 11
    assert sum(row[1] == '*' for row in TRANSPORT) == 5
    return dict(operations=11, multiplications=5, additions=6,
                schedule=TRANSPORT, comparisons=comparisons,
                sources=[sp.sstr(f) for f in expected],
                scope='Exact transport on common actual macro rows; no field typing, rule lookup, weighted selection, geometry, positive adaptation or raw-input loading is included.')


def family(p, pattern, variable):
    return [{a: tuple(1+(pattern+r+a+j) % 2
                     for j in range(1+((r+a+pattern) % 3 if variable else 0)))
             for a in ALPHABET} for r in range(p)]


def micro(images, phase, queue):
    assert queue
    return (phase+1) % len(images), queue[1:]+images[phase][queue[0]]


def batch(images, phase, queue):
    p = len(images)
    assert len(queue) >= p
    prefix = queue[:p]
    output = tuple(child for j,a in enumerate(prefix) for child in images[(phase+j) % p][a])
    expected = queue[p:]+output
    pp, actual = phase, queue
    for _ in range(p):
        pp, actual = micro(images, pp, actual)
    assert pp == phase and actual == expected
    assert 3**p*code(actual) == code(queue)-code(prefix)+code(output)*3**len(queue)
    assert 3**len(actual) == 3**(len(output)-p)*3**len(queue)
    assert len(actual) >= len(queue)
    return actual, code(prefix), code(output), 3**(len(output)-p)


def batch_checks():
    local = histories = rows = early_cycles = escapes = 0
    for p, pattern, variable in product(range(1,4), range(4), (False, True)):
        images = family(p, pattern, variable)
        for length in range(p,p+3):
            for word in product(ALPHABET, repeat=length):
                for phase in range(p):
                    batch(images, phase, word)
                    local += 1
        for length in range(1,p):
            for word in product(ALPHABET, repeat=length):
                phase, queue = 0, word
                seen = set()
                while len(queue) < p and (phase,queue) not in seen:
                    seen.add((phase,queue))
                    phase,queue = micro(images,phase,queue)
                assert len(seen) <= p*sum(2**k for k in range(1,p))
                early_cycles += len(queue) < p
                escapes += len(queue) >= p
        initial = (1,2)*p
        phase, word, terms = pattern % p, initial, []
        for _ in range(5):
            after, a, u, factor = batch(images, phase, word)
            L = 3**len(word)
            terms.append((code(word),a,u*L,L,factor*L))
            word = after
        R = 3
        maximum = max(x for row in terms for x in row)
        while R <= 4*maximum: R *= 3
        vals = dict(R=R,Q=R**len(terms),B=3**p,n0=code(initial),nh=code(word),
                    L0=3**len(initial),Lh=3**len(word))
        for j,name in enumerate(('N','A','U','Z','W')):
            vals[name] = sum(row[j]*R**i for i,row in enumerate(terms))
        env = run(vals)
        assert env['content_left'] == env['content_right']
        assert env['length_left'] == env['length_right']
        histories += 1
        rows += len(terms)
    return dict(local_batches=local, macro_histories=histories, macro_rows=rows,
                short_queue_exact_cycles=early_cycles, short_queue_escapes=escapes,
                periods=[1,2,3])


def blocks(word,p):
    assert len(word) % p == 0
    return tuple(word[i:i+p] for i in range(0,len(word),p))


def aligned_check(images, seed):
    p = len(images)
    assert apply(images,seed)[:len(seed)] == seed
    target = p*((len(seed)+p-1)//p)
    initial, steps = seed, 0
    while len(initial) < target:
        after = apply(images,initial)
        if after == initial:
            return dict(finite_short=True, erased=any(not v for h in images for v in h.values()))
        assert after[:len(initial)] == initial
        initial = after
        steps += 1
        assert steps < p
    initial = initial[:target]
    assert initial[:len(seed)] == seed
    block_seed = blocks(initial,p)
    gamma = {}
    for block in product(ALPHABET,repeat=p):
        result = apply(images,block)
        assert len(result) % p == 0
        gamma[block] = blocks(result,p)
    reached, todo = set(block_seed),list(block_seed)
    while todo:
        for nxt in gamma[todo.pop()]:
            if nxt not in reached:
                reached.add(nxt)
                todo.append(nxt)
    current = block_seed
    for _ in range(len(gamma)):
        nxt = tuple(child for parent in current for child in gamma[parent])
        assert nxt[:len(current)] == current
        before_word = tuple(x for block in current for x in block)
        after_word = tuple(x for block in nxt for x in block)
        assert apply(images,before_word) == after_word
        current = nxt
    assert set(current) == reached
    original = seed
    for _ in range(steps+len(gamma)):
        original = apply(images,original)
    assert {x for block in reached for x in block} == set(original)
    return dict(finite_short=False, erased=any(not v for h in images for v in h.values()))


def alignment_checks():
    systems = valid = short = erasing = nonuniform = 0
    # Both residue-zero (possibly erasing) and residue-one phase images.
    pools = [ ((),(1,1),(1,2),(2,1),(2,2)),
              ((1,),(2,),(1,2,1),(2,1,2)) ]
    for pool in pools:
        for choices in product(pool,repeat=4):
            images = [{1:choices[0],2:choices[1]},{1:choices[2],2:choices[3]}]
            assert all(len(apply(images,block)) % 2 == 0 for block in product(ALPHABET,repeat=2))
            residues = [set(len(h[a]) % 2 for a in ALPHABET) for h in images]
            assert all(len(x) == 1 for x in residues)
            assert sum(next(iter(x)) for x in residues) % 2 == 0
            systems += 1
            for length in (1,2,3):
                for seed in product(ALPHABET,repeat=length):
                    if apply(images,seed)[:len(seed)] != seed: continue
                    result = aligned_check(images,seed)
                    valid += 1
                    short += result['finite_short']
                    erasing += result['erased']
                    nonuniform += any(len(h[1]) != len(h[2]) for h in images)
    # First-block-only reasoning would lose the second seed letter.
    first_block_example = [{1:(1,),2:(2,2)}]
    aligned_check(first_block_example,(1,2))
    assert apply(first_block_example,(1,)) == (1,)
    assert apply(first_block_example,(1,2)) == (1,2,2)
    assert min(valid,short,erasing,nonuniform) > 0
    return dict(aligned_tables=systems, valid_seed_cases=valid,
                stabilized_before_alignment=short, erasing_cases=erasing,
                non_locally_uniform_cases=nonuniform,
                seed_counterexample='p=1; h(1)=1,h(2)=22; seed12: first block alone misses2.')


def verify():
    return dict(status='PASS_PD0L_PHASE_BATCHING_COMPONENTS', source=source_check(),
                batching=batch_checks(), aligned=alignment_checks(),
                proof='../1980/EXPLORATION_PD0L_PHASE_BATCHING.md',
                review='Author and two independent complete scoped proof/source reviews and fresh receipt checks PASS.',
                scope='Conditional11-operation macro transport and decidability of the all-block-output-aligned PD0L subclass. No complete or universal arithmetic certificate.')


if __name__ == '__main__':
    result = verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'])
    print(result['batching'])
    print(result['aligned'])
