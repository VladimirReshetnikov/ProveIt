#!/usr/bin/env python3
"""Independent finite tests of slowdown against the actual three-mass generator."""
import argparse
from collections import defaultdict
import hashlib
import importlib.util
import json
from pathlib import Path
import random
import sys
import time

from radius_one import RadiusOneCA


def import_base(path):
    spec = importlib.util.spec_from_file_location('three_mass_generator_under_test', path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def apply_n(ca, c, n):
    for _ in range(n):
        c = ca.step(c)
    return c


def independent_partial_positions(base, c, phase, r):
    """Closed-form intermediate state from old Π, independent of wrapper steps."""
    cells = defaultdict(list)
    for x, t in c:
        cells[x].append(t)
    expected = []
    for x, types in cells.items():
        types = tuple(sorted(types))
        if len(types) == 1:
            out = (base.single[types[0]],)
        elif len(types) == 2:
            out = base.pairs.get(types, types)
        else:
            out = types
        for t in out:
            v = base.velocity[t]
            displacement = ((v > 0) - (v < 0))*min(phase, abs(v))
            expected.append((x + displacement, r*t + phase % r))
    return tuple(sorted(expected))


def check_block(base, slow, c, inverse=True):
    encoded = slow.embed(c)
    actual = encoded
    for phase in range(1, slow.r+1):
        previous = actual
        actual = slow.step(actual)
        assert actual == independent_partial_positions(base, c, phase, slow.r)
        if inverse:
            assert slow.inverse_step(actual) == previous
    expected = slow.embed(base.step(c))
    assert actual == expected
    return actual


def main():
    parser = argparse.ArgumentParser()
    here = Path(__file__).resolve().parent
    default_generator = here/'three_mass_collision_generator.py'
    if not default_generator.exists():
        default_generator = here.parent/'three_mass_collision_generator.py'
    parser.add_argument('--generator', default=str(default_generator))
    parser.add_argument('--output', default=None)
    args = parser.parse_args()
    start = time.monotonic()
    mod = import_base(args.generator)
    I, CA = mod.Instruction, mod.ThreeMassCA
    base = CA(['q0','q1','q2','q3','halt'], 'halt',
              [I('q0','q1','inc',0), I('q1','q2','inc',1),
               I('q2','q3','dec',0), I('q3','q0','dec',1)])
    slow = RadiusOneCA(base)
    assert slow.r == 4 and slow.channel_count == 19488
    rng = random.Random(2026100201)
    counts = defaultdict(int)
    check_block(base, slow, ())
    counts['vacuum'] += 1

    # Exhaustive singleton coverage: each old type, velocity and singleton clock.
    for t in range(len(base.names)):
        check_block(base, slow, ((0,t),))
        counts['singleton_blocks'] += 1

    # Exhaustive coverage of every prescribed AND every completion pair row.
    # A coincident extra unit of the same old type in phase 1 must not suppress
    # the phase-zero pair permutation, despite total cell cardinality being 3.
    for pair, target in base.pairs.items():
        c = tuple((0,t) for t in pair)
        actual = check_block(base, slow, c)
        counts['supported_pair_blocks'] += 1
        assert actual == tuple(sorted((base.velocity[t], slow.r*t) for t in target))
        mixed = tuple(sorted([(0,slow.encode_channel(t)) for t in pair]
                             +[(0,slow.encode_channel(pair[0],1))]))
        observed = slow.step(mixed)
        expected = tuple(sorted([(slow.epsilon(t,0),slow.encode_channel(t,1)) for t in target]
                                +[(slow.epsilon(pair[0],1),slow.encode_channel(pair[0],2))]))
        assert observed == expected
        assert slow.inverse_step(observed) == mixed
        counts['pair_plus_nonzero_phase_inverse'] += 1

    # Random phase-zero configurations include unsupported pairs and sectors >=3.
    for _ in range(2500):
        c = tuple(sorted(set((rng.randrange(-8,9), rng.randrange(len(base.names)))
                             for j in range(rng.randrange(0,90)))))
        check_block(base, slow, c)
        counts['random_arbitrary_cardinality_blocks'] += 1

    # Both inverse orders on arbitrary mixed-phase inputs with dense local states.
    for _ in range(5000):
        c = tuple(sorted(set((rng.randrange(-3,4), rng.randrange(slow.channel_count))
                             for j in range(rng.randrange(0,130)))))
        assert slow.inverse_step(slow.step(c)) == c
        assert slow.step(slow.inverse_step(c)) == c
        counts['random_mixed_phase_both_inverse_orders'] += 1

    # Wraparound and Boolean capacity: all phases of one old type occupy a cell.
    for t in range(len(base.names)):
        c = tuple((0,slow.encode_channel(t,p)) for p in range(slow.r))
        assert slow.inverse_step(slow.step(c)) == c
        assert slow.step(slow.inverse_step(c)) == c
        counts['all_phases_one_type_inverse'] += 1

    # Maximal cell occupancy and multi-cell dense states exercise every phase
    # sector simultaneously, including the high-popcount identity restriction.
    for positions in ((0,),(-1,0,1)):
        dense = tuple((x,k) for x in positions for k in range(slow.channel_count))
        assert slow.inverse_step(slow.step(dense)) == dense
        assert slow.step(slow.inverse_step(dense)) == dense
        counts['maximal_dense_states_both_inverse_orders'] += 1

    cycle_results = []
    # Actual complete source runs, checked at EVERY old tick and EVERY new phase.
    for N in (1,2,3,6):
        c = base.initial('q0',N)
        observed = slow.embed(c)
        seen, times = [], []
        for tick in range(1,20000*N):
            for phase in range(1,slow.r+1):
                observed = slow.step(observed)
                assert observed == independent_partial_positions(base,c,phase,slow.r)
                assert len(observed) == 3
                assert not slow.committed_halt(observed,base)
                if phase < slow.r:
                    assert all(k % slow.r == phase for x,k in observed)
            c = base.step(c,require_specified=True)
            assert observed == slow.embed(c)
            ready = base.ready(c)
            if ready is not None:
                seen.append(ready)
                times.append(slow.r*tick)
                if len(seen) == 4:
                    break
        assert seen == [('q1',2*N),('q2',6*N),('q3',3*N),('q0',N)]
        assert observed == slow.embed(base.initial('q0',N))
        cycle_results.append({'N':N,'ready_sequence':seen,'slow_ticks':times})
        counts['cycle_base_ticks'] += tick
        counts['cycle_radius_one_ticks'] += slow.r*tick

    # Query/unquery: all residues, arbitrary finite scratch, exact end tick.
    for N in range(1,7):
        for z in (0,3,5):
            for sign,stage,end_stage in [(1,0,1),(-1,2,3)]:
                c = slow.embed(base.initial('q0',N,i=2,z=z,stage=stage))
                ticks = slow.r*(4*base.D*N+1)
                result = apply_n(slow,c,ticks)
                assert result == slow.embed(base.initial('q0',N,i=2,z=(z+sign*N)%6,stage=end_stage))
                counts['query_blocks'] += 1
                counts['query_radius_one_ticks'] += ticks

    merge = CA(['zero_source','positive_source','halt'],'halt',
               [I('zero_source','halt','zero',0),I('positive_source','halt','positive',0)])
    ms = RadiusOneCA(merge,4)
    halt_results=[]
    for q,N in [('zero_source',1),('zero_source',3),('positive_source',2),('positive_source',6)]:
        old = merge.initial(q,N)
        c = ms.embed(old)
        first_halt = None
        for tick in range(1,10000*N):
            for phase in range(1,5):
                c=ms.step(c)
                if ms.committed_halt(c,merge):
                    assert phase == 4
                    first_halt=4*(tick-1)+phase
                    break
            old=merge.step(old,require_specified=True)
            assert c == ms.embed(old)
            if first_halt is not None:
                break
            assert merge.ready(old) != ('halt',N)
        assert first_halt == 4*(192*N+8)
        assert merge.ready(old) == ('halt',N)
        # Explicitly follow the first completed row out of Ready(halt).
        check_block(merge,ms,old)
        halt_results.append({'source':q,'N':N,'base_halt_tick':first_halt//4,'radius_one_halt_tick':first_halt})

    trap=CA(['run','halt'],'halt',[I('run','halt','dec',0)])
    ts=RadiusOneCA(trap,4)
    old=trap.initial('run',1)
    c=ts.embed(old)
    for tick in range(1,1001):
        for phase in range(1,5):
            c=ts.step(c)
            assert not ts.committed_halt(c,trap)
        old=trap.step(old,require_specified=True)
        assert c == ts.embed(old)
    counts['invalid_decrement_radius_one_ticks']=4000

    # The construction also covers r=1, an unnecessarily larger r, and a local
    # permutation changing a particle's velocity. The actual base singleton
    # clock preserves velocity, so this toy guards against a stronger assumption.
    class Toy:
        names=tuple(range(4))
        velocity=(-1,0,1,0)
        single={0:2,2:1,1:0,3:3}
        pairs={(0,1):(2,3),(2,3):(0,1)}
        def step(self,c):
            cells=defaultdict(list)
            for x,t in c: cells[x].append(t)
            out=[]
            for x,ts in cells.items():
                ts=tuple(sorted(ts))
                dest=(self.single[ts[0]],) if len(ts)==1 else self.pairs.get(ts,ts) if len(ts)==2 else ts
                out.extend((x+self.velocity[t],t) for t in dest)
            return tuple(sorted(out))
    toy=Toy()
    for r in (1,2,4,7):
        tiny=RadiusOneCA(toy,r)
        for mask in range(1 << 8):
            c=tuple((j//4,j%4) for j in range(8) if mask & (1 << j))
            check_block(toy,tiny,c)
            counts['toy_type_change_and_r_boundary_blocks'] += 1
    result={'status':'passed','seed':2026100201,'source_file':Path(args.generator).name,
            'source_sha256':hashlib.sha256(Path(args.generator).read_bytes()).hexdigest(),
            'base_rule_sha256':base.fingerprint(),'base_types':len(base.names),
            'base_radius':4,'slowdown':slow.r,'radius_one_types':slow.channel_count,
            'radius_one_alphabet_cardinality':'2^19488','maximum_stream_displacement':1,
            'prescribed_pair_rows':base.required_pair_count,'all_supported_pair_rows':len(base.pairs),
            'completion_pair_rows':len(base.pairs)-base.required_pair_count,
            'counts':dict(counts),'cycle_results':cycle_results,'halt_results':halt_results,
            'elapsed_seconds':round(time.monotonic()-start,3)}
    encoded=json.dumps(result,indent=2)+'\n'
    if args.output:
        Path(args.output).write_text(encoded)
    print(encoded,end='')


if __name__=='__main__':
    main()
