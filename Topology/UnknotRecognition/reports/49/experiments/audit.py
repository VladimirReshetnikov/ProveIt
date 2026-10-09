#!/usr/bin/env python3
"""Reproduce exact arithmetic, literal-word, and source-derived updater audits."""
from __future__ import annotations
import argparse
from itertools import product
import json
from math import gcd
from pathlib import Path
import random
import sys
import time
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'src'))
from anchored_unknot import Arena, Source, AnchoredState, replay
from anchored_unknot.fixtures import signed_tree, power_chain, christoffel
from anchored_unknot.linear_audit import audit_state
from anchored_unknot.reference_update import apply_projection, native_witnesses, exact_rle


def main(output: Path):
    started = time.perf_counter()
    rng = random.Random(2026100801)
    counts = {'random_presentations': 0, 'cofactor_prefixes': 0, 'updater_prefixes': 0,
              'exact_root_rle_comparisons': 0, 'positive_words': 0, 'signed_profile_cases': 0,
              'independent_replays': 0, 'nonunit_primitive_cases': 0}
    for case in range(600):
        r = rng.randrange(2, 11)
        parents = [rng.randrange(1, i) for i in range(2, r + 1)]
        powers = [rng.choice((-11, -5, -2, -1, 1, 2, 3, 7, 13)) for _ in range(r - 1)]
        source = signed_tree(parents, powers, duplicates=bool(case % 2))
        state = AnchoredState(source)
        ref_arena, ref_roots = source.materialize(state.images, set())
        ref_alive = set(source.generators)
        while len(state.alive) > 1:
            batch = state.plan(max_pairs=rng.choice((1, 2, 3, 10)))
            assert batch
            apply_projection(ref_arena, ref_roots, ref_alive, native_witnesses(batch))
            state.apply_planned(batch)
            audit_state(source, state.images, state.dead, with_cofactors=True)
            flat_arena, flat_roots = source.materialize(state.images, state.dead)
            assert exact_rle(ref_arena, ref_roots) == exact_rle(flat_arena, flat_roots)
            assert ref_alive == state.alive
            counts['cofactor_prefixes'] += 1
            counts['updater_prefixes'] += 1
            counts['exact_root_rle_comparisons'] += len(source.roots)
        proof = state.run()
        result = replay(source, proof)
        assert result.rank_one_zero and not result.needs_torsion_freeness
        assert result.images == state.images
        counts['independent_replays'] += 1
        counts['random_presentations'] += 1

    print('random trees complete', counts, flush=True)
    # All binary positive words through length 12. The independent expected set
    # consists of literal cyclic rotations of a mechanical Christoffel period.
    for n in range(2, 13):
        allowed = {}
        for P in range(1, n):
            Q = n - P; d = gcd(P, Q)
            base = christoffel(P // d, Q // d)
            allowed[P] = { (base[j:] + base[:j]) * d for j in range(len(base)) }
        for word in product((1, 2), repeat=n):
            if len(set(word)) != 2:
                continue
            expected = word in allowed[word.count(1)]
            counts['positive_words'] += 1
            for sa, sb in ((1, 1), (1, -1), (-1, 1), (-1, -1)):
                signed = tuple(sa if x == 1 else 2 * sb for x in word)
                a = Arena(); source = Source.from_arena(a, [a.word(signed)], (1, 2))
                state = AnchoredState(source)
                planned = state.plan()
                assert bool(planned) == expected
                if planned:
                    state.apply_planned(planned)
                    assert replay(source, state.run()).rank_one_zero
                    counts['independent_replays'] += 1
                counts['signed_profile_cases'] += 1

    print('exhaustive words complete', counts, flush=True)
    # Nonunit primitive pairs with third and fourth generators, signs and rotations.
    for p, q in ((2, 3), (3, 5), (5, 8), (8, 13), (13, 21)):
        for signa, signb in ((1, 1), (1, -1), (-1, 1), (-1, -1)):
            base = christoffel(p, q, signa, 2 * signb)
            for shift in range(len(base)):
                a = Arena()
                roots = [a.word(base[shift:] + base[:shift]), a.word((2, 2, -3)),
                         a.word((3, 3, 3, -4)), a.word((4, -4, 1, -1))]
                source = Source.from_arena(a, roots, (1, 2, 3, 4))
                state = AnchoredState(source)
                ref_arena, ref_roots = source.materialize(state.images, set())
                ref_alive = set(source.generators)
                while len(state.alive) > 1:
                    batch = state.plan(max_pairs=1)
                    assert batch
                    apply_projection(ref_arena, ref_roots, ref_alive, native_witnesses(batch))
                    state.apply_planned(batch)
                    audit_state(source, state.images, state.dead)
                    fa, fr = source.materialize(state.images, state.dead)
                    assert exact_rle(ref_arena, ref_roots) == exact_rle(fa, fr)
                    counts['cofactor_prefixes'] += 1
                    counts['updater_prefixes'] += 1
                    counts['exact_root_rle_comparisons'] += len(source.roots)
                assert replay(source, state.run()).rank_one_zero
                counts['independent_replays'] += 1
                counts['nonunit_primitive_cases'] += 1

    print('nonunit primitive fixtures complete', counts, flush=True)
    large = []
    for rank, bits in ((12, 64), (20, 64), (24, 128)):
        source = power_chain(rank, 1 << bits)
        state = AnchoredState(source)
        ref_arena, ref_roots = source.materialize(state.images, set())
        ref_alive = set(source.generators)
        while len(state.alive) > 1:
            batch = state.plan(max_pairs=1)
            apply_projection(ref_arena, ref_roots, ref_alive, native_witnesses(batch))
            state.apply_planned(batch)
        flat_arena, flat_roots = source.materialize(state.images, state.dead)
        assert exact_rle(ref_arena, ref_roots) == exact_rle(flat_arena, flat_roots)
        result = replay(source, state.run())
        assert result.rank_one_zero
        max_bits = max(abs(k).bit_length() for _, k in state.images.values())
        assert max_bits == (rank - 1) * bits + 1
        large.append({'rank': rank, 'local_power_bits_parameter': bits,
                      'largest_image_exponent_bits': max_bits, 'source_nodes': len(source.rules),
                      'chained_allocated_nodes': len(ref_arena.rules),
                      'flat_export_allocated_nodes': len(flat_arena.rules),
                      'rounds': len(state.steps), 'certificate_bytes': len(json.dumps(state.run()))})
        counts['independent_replays'] += 1
        counts['exact_root_rle_comparisons'] += len(source.roots)
    source = power_chain(64, 1 << 1024)
    state = AnchoredState(source)
    proof = state.run(max_pairs=1)
    rr = replay(source, proof)
    assert rr.rank_one_zero and rr.images[64][1].bit_length() == 64513
    counts['independent_replays'] += 1
    large.append({'rank': 64, 'local_power_bits_parameter': 1024,
                  'largest_image_exponent_bits': 64513, 'source_nodes': len(source.rules),
                  'rounds': len(state.steps), 'certificate_bytes': len(json.dumps(proof)),
                  'comparison_scope': 'anchored producer and independent source replay only'})
    result = {'status': 'PASS', 'seed': 2026100801, 'counts': counts,
              'huge_exponent_cases': large, 'seconds': time.perf_counter() - started,
              'scope': 'algebraic fixtures; exact source-derived updater excerpt, not full production',
              'python': sys.version}
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, default=Path('data/audit.json'))
    args = parser.parse_args()
    main(args.output)
