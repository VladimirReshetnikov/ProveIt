#!/usr/bin/env python3
"""Binary radius-six conservative expanding shuttle; standard library only."""
from itertools import product
from pathlib import Path
import json

REWRITE = {
    (0,1):(1,2),
    (0,2):(-1,1),
    (0,1,3):(-1,1,4),
    (0,2,4):(0,3,4),
}


def step(c):
    if not c:
        return set()
    components=[]
    for x in sorted(c):
        if not components or x-components[-1][-1]>2:
            components.append([x])
        else:
            components[-1].append(x)
    out=set()
    for comp in components:
        a=comp[0]
        normalized=tuple(x-a for x in comp)
        target=REWRITE.get(normalized,normalized)
        transformed={a+x for x in target}
        assert not out & transformed, (c, components)
        out |= transformed
    return out


def radius_six_table():
    return [int(0 in step({i-6 for i in range(13) if code >> i & 1}))
            for code in range(1<<13)]


def table_step(c,table):
    if not c:
        return set()
    out=set()
    # Exact finite propagation of this rule is at most one site per step.
    for x in range(min(c)-1,max(c)+2):
        mask=sum(1 << i for i in range(13) if x+i-6 in c)
        if table[mask]:
            out.add(x)
    return out


def conservation_potential(table):
    """Check every de Bruijn edge: f(w)-w[6]=P(suffix)-P(prefix)."""
    from collections import deque
    potential={0:0}
    todo=deque([0])
    while todo:
        prefix=todo.popleft()
        for last in (0,1):
            word=prefix | (last<<12)
            suffix=word>>1
            delta=table[word]-((word>>6)&1)
            value=potential[prefix]+delta
            if suffix in potential:
                assert potential[suffix]==value,(word,potential[suffix],value)
            else:
                potential[suffix]=value
                todo.append(suffix)
    assert len(potential)==4096
    for word in range(8192):
        assert table[word]-((word>>6)&1)==potential[word>>1]-potential[word&4095]
    return [potential[i] for i in range(4096)]


def run():
    table=radius_six_table()
    potential=conservation_potential(table)
    certificate={
        'alphabet':[0,1], 'radius':6,
        'encoding':'For window w_0...w_12 at coordinates -6...6, index=sum(w_i*2^i).',
        'rule_bits_indexed_by_window':''.join(map(str,table)),
        'potential_index_encoding':'For a 12-bit vertex v_0...v_11, index=sum(v_i*2^i).',
        'potential_by_vertex':potential,
        'verified_identity':'f(word)-word[6] = P(word>>1)-P(word & 4095)',
        'verified_edges':8192,'verified_vertices':4096,
    }
    Path(__file__).with_name('binary-radius6-conservation-certificate.json').write_text(json.dumps(certificate,separators=(',',':'))+'\n')
    conservation=locality=trajectory_steps=hits_checked=0
    for code in range(1<<18):
        c={i for i in range(18) if code>>i & 1}
        assert len(step(c)) == len(c)
        conservation += 1
        if code < (1<<13):
            assert step(c) == table_step(c,table), code
            locality += 1
    for d in range(7,31):
        c={0,3,4,d}
        expected={k*k+(2*d-11)*k for k in range(101)}
        actual=set()
        horizon=10000+(2*d-11)*100
        for t in range(horizon+1):
            if c & set(range(5)) == {0,3,4}:
                actual.add(t)
                k=len(actual)-1
                assert c == {0,3,4,d+k}
                hits_checked += 1
            if t<horizon:
                c=step(c)
                assert len(c)==4
                trajectory_steps += 1
        assert actual==expected,(d, actual ^ expected)
    # Test large unrecognized components and arbitrary local contexts.
    import random
    rng=random.Random(46331)
    random_cases=0
    for _ in range(10000):
        c={i for i in range(-30,31) if rng.randrange(2)}
        assert step(c) == table_step(c,table)
        offset=rng.randint(-1000000,1000000)
        assert step({x+offset for x in c}) == {x+offset for x in step(c)}
        random_cases += 1
    # Verify the unique natural witness formula on a finite exhaustive ledger.
    witness_checks=0
    for x in range(20):
        values={k*k+(2*x+3)*k:k for k in range(101)}
        assert len(values)==101
        for t in range(1000):
            roots=[k for k in range(101) if (t-k*k-(2*x+3)*k)**2==0]
            assert len(roots)<=1
            assert bool(roots)==(t in values)
            witness_checks += 1
    result={
        'status':'PASS', 'alphabet':[0,1], 'numerical_mass':4,
        'radius_upper_bound':6,'radius_table_entries':len(table),
        'exact_de_bruijn_edges_verified':8192,'potential_vertices':4096,
        'dense_conservation_cases':conservation,
        'exhaustive_window_local_table_comparisons':locality,
        'random_large_context_locality_translation_checks':random_cases,
        'direct_trajectory_steps':trajectory_steps,
        'predicted_hit_times_checked':hits_checked,
        'finite_unique_witness_checks':witness_checks,
        'initial_configuration':'{0,3,4,d}, d>=7',
        'anchored_pattern':'10011 at sites 0..4',
        'hit_formula':'t_k=k^2+(2*d-11)*k, k>=0',
        'quartic':'[t-k^2-(2*x+3)*k]^2, d=7+x',
        'limits':'Tests supplement explicit global conservation/locality and orbit proofs.'
    }
    Path(__file__).with_name('binary-shuttle-test-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    run()
