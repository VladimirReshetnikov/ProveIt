#!/usr/bin/env python3
"""Independent spatial-blocking audit against the frozen actual generator.

All checks use explicit raises and remain active under python -O.
"""
import argparse
from collections import Counter, defaultdict
import hashlib
import importlib.util
import json
from pathlib import Path
import random
import sys
import time
from types import SimpleNamespace

from spatial_radius_one import SpatialRadiusOneCA


def main():
    parser = argparse.ArgumentParser()
    here = Path(__file__).resolve().parent
    default = here/'three_mass_collision_generator.py'
    parser.add_argument('--generator', type=Path, default=default)
    parser.add_argument('--output', type=Path, default=None)
    args = parser.parse_args()
    start = time.monotonic()
    counts = Counter()

    def check(value, label):
        counts['checks'] += 1
        if not value:
            raise RuntimeError(label)

    def rejects(fun):
        try:
            fun()
        except ValueError:
            counts['boundary_rejections'] += 1
        else:
            raise RuntimeError('malformed public input accepted')

    raw = args.generator.read_bytes()
    expected_hash = '14b8bde4362803181dbee33d81e083ba4758ee51df7b23fcfd920a6f1de12d52'
    check(hashlib.sha256(raw).hexdigest() == expected_hash, 'generator is not frozen revision')
    spec = importlib.util.spec_from_file_location('frozen_spatial_generator', args.generator)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = mod
    spec.loader.exec_module(mod)
    I, CA = mod.Instruction, mod.ThreeMassCA
    base = CA(['q0', 'q1', 'q2', 'q3', 'halt'], 'halt',
              [I('q0', 'q1', 'inc', 0), I('q1', 'q2', 'inc', 1),
               I('q2', 'q3', 'dec', 0), I('q3', 'q0', 'dec', 1)])
    blocked = SpatialRadiusOneCA(base)
    check(blocked.channel_count == 4*len(base.names) == 19488, 'type count')
    check(max(map(abs, blocked.displacement)) == 1, 'radius one')
    rng = random.Random(2026100301)
    inverse_single = {b: a for a, b in base.single.items()}
    inverse_pairs = {b: a for a, b in base.pairs.items()}

    def native_inverse(c):
        # Separate oracle implementation: unstream each original lane, then Pi^-1.
        cells = defaultdict(list)
        for x, t in c:
            cells[x-base.velocity[t]].append(t)
        out = []
        for x, types in cells.items():
            p = tuple(sorted(types))
            q = ((inverse_single[p[0]],) if len(p) == 1 else
                 inverse_pairs.get(p, p) if len(p) == 2 else p)
            out.extend((x, t) for t in q)
        return tuple(sorted(out))

    def all_laws(c):
        encoded = blocked.embed(c)
        check(blocked.project(encoded) == tuple(sorted(c)), 'B inverse B')
        nxt = blocked.step(encoded)
        check(nxt == blocked.embed(base.step(c)), 'one-step conjugacy')
        check(len(nxt) == len(encoded), 'mass')
        check(blocked.inverse_step(nxt) == encoded, 'G^-1 G')
        prev = blocked.inverse_step(encoded)
        check(blocked.step(prev) == encoded, 'G G^-1')
        check(prev == blocked.embed(native_inverse(c)), 'inverse conjugacy')

    all_laws(())
    counts['vacuum'] += 1
    # Every type and offset, signed sites including boundaries and huge integers.
    for t in range(len(base.names)):
        for a in range(4):
            all_laws(((-8+a, t),))
            counts['singleton_type_offset'] += 1
    for x in tuple(range(-25,26)) + (-10**100-1, -10**100, 10**100+3):
        encoded = blocked.embed(((x, base.R),))
        z, k = encoded[0]
        check(4*z+k%4 == x and 0 <= k%4 < 4, 'signed Euclidean division')
        all_laws(((x, base.R),))
        counts['signed_division_cases'] += 1
    # Exhaust every native supported pair at every offset in one configuration.
    # Four occupied pairs share a single block; each offset must act independently.
    for pair, target in base.pairs.items():
        c = tuple((a-4, t) for a in range(4) for t in pair)
        all_laws(c)
        counts['supported_pair_all_offsets'] += 1
    # Arbitrary mixed offsets, local pairs/triples, negative sites, and both inverses.
    for _ in range(2500):
        c = tuple(sorted(set((rng.randrange(-20,21), rng.randrange(len(base.names)))
                             for _ in range(rng.randrange(0,150)))))
        all_laws(c)
        counts['random_native_configurations'] += 1
    for _ in range(2500):
        c = tuple(sorted(set((rng.randrange(-3,4), rng.randrange(blocked.channel_count))
                             for _ in range(rng.randrange(0,150)))))
        check(blocked.embed(blocked.project(c)) == c, 'B B inverse surjectivity')
        all_laws(blocked.project(c))
        counts['random_mixed_offset_configurations'] += 1
    for positions in ((0,), (-1,0,1)):
        c = tuple((z,k) for z in positions for k in range(blocked.channel_count))
        all_laws(blocked.project(c))
        check(blocked.embed(blocked.project(c)) == c, 'dense full block recoding')
        counts['maximal_dense_states'] += 1

    # Explicit guard against mistaking total block popcount for per-offset popcount.
    p, target = next((p,q) for p,q in base.pairs.items() if p != q)
    channels = tuple([4*t for t in p] + [4*p[0]+1])
    wanted = tuple(sorted([blocked.lane_permutation[4*t] for t in target]
                          + [blocked.lane_permutation[4*base.single[p[0]]+1]]))
    check(blocked.local_collision(channels) == wanted, 'pair plus offset singleton')
    check(blocked.local_collision(wanted, True) == tuple(sorted(channels)), 'inverse local order')
    for _ in range(1000):
        channels = tuple(sorted(rng.sample(range(blocked.channel_count), rng.randrange(0,160))))
        check(blocked.local_collision(blocked.local_collision(channels), True) == channels, 'C^-1 C')
        check(blocked.local_collision(blocked.local_collision(channels, True)) == channels, 'C C^-1')
        counts['local_both_inverse_orders'] += 1

    trajectory_results = []

    def trajectory(machine, q, N, expected, limit, label):
        b = SpatialRadiusOneCA(machine)
        c = machine.initial(q,N)
        packed = b.embed(c)
        check(packed == tuple(sorted([(-3*N,4*machine.L(0,(q,0,0))),
                                     (-3*N,4*machine.S(0)), (0,4*machine.R)])), 'initial geometry')
        seen, times = [], []
        for tick in range(limit+1):
            check(packed == b.embed(c), 'whole-trajectory exact tick conjugacy')
            check(len(packed) == 3, 'whole-trajectory mass three')
            ready = machine.ready(c)
            halt = ready is not None and ready[0] == machine.halt
            check(b.committed_halt(packed,machine) == halt, 'canonical committed-halt equivalence')
            if tick and ready is not None:
                seen.append(ready)
                times.append(tick)
                if len(seen) == len(expected) and expected:
                    break
            if tick == limit:
                break
            previous = packed
            packed = b.step(packed)
            check(b.inverse_step(packed) == previous, 'whole-trajectory inverse')
            c = machine.step(c, require_specified=True)
        check(seen == expected, 'source Ready sequence')
        if expected:
            check(tick < limit, 'trajectory bound exhausted')
        counts['trajectory_native_ticks'] += tick
        counts['trajectory_blocked_ticks'] += tick
        trajectory_results.append({'case': label, 'input_N': N, 'ready_sequence': seen,
                                   'native_and_blocked_ticks': times, 'checked_ticks': tick})
        return b,c,packed,tick

    for N in (1,2,3,6):
        trajectory(base,'q0',N,[('q1',2*N),('q2',6*N),('q3',3*N),('q0',N)],
                   20000*N,'four-operation cycle')
    merge = CA(['zero_source','positive_source','halt'],'halt',
               [I('zero_source','halt','zero',0),I('positive_source','halt','positive',0)])
    for q,N in [('zero_source',1),('zero_source',3),('positive_source',2),('positive_source',6)]:
        b,c,packed,tick = trajectory(merge,q,N,[('halt',N)],10000*N,'inverse merge')
        check(tick == 192*N+8, 'merge tick formula')
        check(b.step(packed) != packed, 'halt is an occurrence, not absorbing')
        check(b.step(packed) == b.embed(merge.step(c)), 'posthalt completed step conjugacy')
    ops = [('inc',0),('inc',1),('positive',0),('positive',1),('dec',0),
           ('dec',1),('zero',0),('zero',1),('nop',0)]
    states = [f'q{i}' for i in range(9)]+['halt']
    mixed = CA(states,'halt',[I(states[i],states[i+1],op,counter)
                             for i,(op,counter) in enumerate(ops)])
    expected = list(zip(states[1:],(2,6,6,6,3,1,1,1,1)))
    b,c,packed,tick = trajectory(mixed,'q0',1,expected,10000,'nine-step mixed chain')
    check(tick == 5340, 'mixed physical clock_scale=1')
    check(b.committed_halt(b.embed(mixed.initial('halt',1)),mixed), 'zero-step halt')
    # Exact-cell test rejects correct pair contaminated at any other offset.
    halt = mixed.initial('halt',1)
    pair = tuple((z,k) for z,k in b.embed(halt) if z < 0)
    for a in (1,2,3):
        check(not b.committed_halt(pair+((-3,b.encode_channel(mixed.R,a)),),mixed),
              'observer must reject extra offset lane')
        shifted = tuple((z,k+a) for z,k in pair)
        check(not b.committed_halt(shifted,mixed), 'observer must require offset zero')
    trap = CA(['run','halt'],'halt',[I('run','halt','dec',0)])
    trajectory(trap,'run',1,[],1000,'invalid decrement trap')

    # Boundary validation and snapshot independence, including optimized Python.
    for width in (True,0,-1,3,4.0,'4',None):
        rejects(lambda width=width: SpatialRadiusOneCA(base,width))
    for fun in (blocked.embed,blocked.project,blocked.step,blocked.inverse_step):
        for bad in (None,'x',{},[(True,0)],[(0,True)],[(0,-1)],[(0,10**10)],[(0,0),(0,0)]):
            rejects(lambda fun=fun,bad=bad: fun(bad))
    for fun in (blocked.embed,blocked.project,blocked.step,blocked.inverse_step):
        check(fun(iter(())) == (), 'empty one-shot iterable')
    toy = SimpleNamespace(names=('a','b','c'),velocity=[-4,3,0],
                          single={0:1,1:2,2:0},pairs={(0,1):(1,2),(1,2):(0,1)})
    bt = SpatialRadiusOneCA(toy)
    sample = ((-1,0),(0,9),(2,5))
    before = bt.step(sample)
    toy.velocity[0] = 900
    toy.single.clear()
    toy.pairs.clear()
    check(bt.step(sample) == before, 'frozen descriptor snapshot')
    check(bt.inverse_step(before) == sample, 'toy singleton changes velocity')
    report = {'status':'PASS','optimization':sys.flags.optimize,'counts':dict(counts),
              'generator_sha256':expected_hash,'base_rule_sha256':base.fingerprint(),
              'base_types':len(base.names),'blocked_channels':blocked.channel_count,
              'block_width':4,'native_ticks_per_blocked_tick':1,
              'forward_radius_bound':1,'inverse_radius_bound':1,
              'trajectories':trajectory_results,
              'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()
                               for p in (Path(__file__),here/'spatial_radius_one.py')},
              'elapsed_seconds':round(time.monotonic()-start,3)}
    output = json.dumps(report,indent=2)+'\n'
    if args.output:
        args.output.write_text(output)
    print(output,end='')


if __name__ == '__main__':
    main()
