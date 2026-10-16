#!/usr/bin/env python3
"""Finite regressions for the equality-free PSC decoder lemmas.

Exhausts every binary relation on domains of sizes 1 through --max-n.
Objects are 0,...,n-1; profiles[x] is the bitset of raw members of x.
No finite structure is asserted to satisfy the complete PSC schema.
The fragment-descent check is conditional on that exact profile fragment
being represented by an object of the finite structure.
"""

import argparse
import hashlib
import json
from pathlib import Path
import time


def elements(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def describe(profiles, **extra):
    return {
        "domain_size": len(profiles),
        "members_by_object": [list(elements(p)) for p in profiles],
        **extra,
    }


def positive_hull(initial_inputs, transitions):
    """Positive closure: seed inputs need not themselves be in the output."""
    output = 0
    pending = initial_inputs
    processed = 0
    while pending:
        x = next(elements(pending))
        pending &= ~(1 << x)
        processed |= 1 << x
        new = transitions[x]
        output |= new
        pending |= new & ~processed
    return output


def audit(max_n):
    counts = {
        "structures": 0,
        "profile_equivalence_structures": 0,
        "local_bound_inputs": 0,
        "monochromatic_inputs": 0,
        "monochromatic_endpoint_pairs": 0,
        "direct_descent_memberships": 0,
        "nonmonochromatic_memberships": 0,
        "fragment_descent_witnesses": 0,
        "fragment_missing_memberships": 0,
        "all_fragment_structures": 0,
        "closed_hull_checks_with_all_fragments": 0,
    }
    by_size = []
    gate_witness = None
    old_witness = None

    for n in range(1, max_n + 1):
        full = (1 << n) - 1
        size_count = 0
        for relation_code in range(1 << (n * n)):
            profiles = tuple((relation_code >> (n * x)) & full for x in range(n))
            d = tuple(tuple(profiles[x] == profiles[y] for y in range(n))
                      for x in range(n))
            assert all(d[x][x] for x in range(n))
            assert all(d[x][y] == d[y][x] for x in range(n) for y in range(n))
            assert all(not (d[x][y] and d[y][z]) or d[x][z]
                       for x in range(n) for y in range(n) for z in range(n))
            counts["profile_equivalence_structures"] += 1
            classes = tuple(sum(1 << z for z in range(n) if d[z][y]) for y in range(n))
            subsets = tuple(sum(1 << y for y in range(n)
                                if profiles[y] & ~profiles[x] == 0) for x in range(n))
            mono = tuple(sum(1 << y for y in range(n)
                             if profiles[x] != 0
                             and all(d[z][y] for z in elements(profiles[x])))
                         for x in range(n))
            delta = tuple(mono[x] if mono[x] else subsets[x] for x in range(n))

            for x in range(n):
                if mono[x]:
                    bound = next(elements(mono[x]))
                    counts["monochromatic_inputs"] += 1
                    for y in elements(mono[x]):
                        for z in elements(mono[x]):
                            assert d[y][z]
                            counts["monochromatic_endpoint_pairs"] += 1
                else:
                    bound = x
                assert all(profiles[y] & ~profiles[bound] == 0
                           for y in elements(delta[x]))
                counts["local_bound_inputs"] += 1

            fragments_available = True
            for x in range(n):
                for y in elements(profiles[x]):
                    fragment = profiles[x] & classes[y]
                    witnesses = [s for s in range(n) if profiles[s] == fragment]
                    if not witnesses:
                        fragments_available = False
                    if mono[x]:
                        assert delta[x] & (1 << y)
                        counts["direct_descent_memberships"] += 1
                    else:
                        counts["nonmonochromatic_memberships"] += 1
                        if not witnesses:
                            counts["fragment_missing_memberships"] += 1
                        for s in witnesses:
                            assert profiles[s] & (1 << y)
                            assert delta[x] & (1 << s)
                            assert mono[s] & (1 << y)
                            assert delta[s] & (1 << y)
                            counts["fragment_descent_witnesses"] += 1

            if fragments_available:
                counts["all_fragment_structures"] += 1
                for seed in range(n):
                    hull = positive_hull(subsets[seed], delta)
                    assert profiles[seed] & ~hull == 0
                    assert all(profiles[x] & ~hull == 0 for x in elements(hull))
                    counts["closed_hull_checks_with_all_fragments"] += 1

                if old_witness is None:
                    exact_ps = tuple(sum(1 << y for y in range(n)
                                         if profiles[x] == classes[y]) for x in range(n))
                    old_delta = tuple(exact_ps[x] if exact_ps[x] else subsets[x]
                                      for x in range(n))
                    for seed in range(n):
                        saturated = all((profiles[seed] & c) in (0, c) for c in classes)
                        if saturated:
                            continue
                        old_hull = positive_hull(subsets[seed], old_delta)
                        missing_root = profiles[seed] & ~old_hull
                        bad_members = [x for x in elements(old_hull)
                                       if profiles[x] & ~old_hull]
                        if missing_root or bad_members:
                            new_hull = positive_hull(subsets[seed], delta)
                            old_witness = describe(
                                profiles, seed=seed,
                                all_profile_fragments_exist=True,
                                seed_is_saturated=False,
                                old_exact_singleton_hull=list(elements(old_hull)),
                                new_monochromatic_hull=list(elements(new_hull)),
                                old_missing_root_members=list(elements(missing_root)),
                                old_nontransitive_member_objects=bad_members,
                            )
                            break

            if gate_witness is None:
                empty_inputs = [x for x in range(n) if profiles[x] == 0]
                no_universal_subset_bound = not any(
                    all(profiles[y] & ~profiles[b] == 0 for y in range(n))
                    for b in range(n))
                if empty_inputs and no_universal_subset_bound:
                    x = empty_inputs[0]
                    ungated = sum(1 << y for y in range(n)
                                  if all(d[z][y] for z in elements(profiles[x])))
                    assert ungated == full
                    gate_witness = describe(
                        profiles, empty_input=x,
                        ungated_monochromatic_outputs=list(range(n)),
                        has_common_subset_bound=False,
                        gated_monochromatic_outputs=list(elements(mono[x])),
                        correct_decoder_outputs=list(elements(delta[x])),
                    )

            counts["structures"] += 1
            size_count += 1
        by_size.append({"domain_size": n, "structures": size_count})

    assert counts["structures"] == sum(1 << (n * n) for n in range(1, max_n + 1))
    if max_n >= 3:
        assert gate_witness is not None
    return {
        "status": "all assertions passed",
        "scope": "All binary relations on nonempty labeled domains up to max_n; not full PSC models.",
        "fragment_condition": "Two-step descent is checked whenever the exact fragment is represented.",
        "max_n": max_n,
        "by_domain_size": by_size,
        "counts": counts,
        "nonempty_gate_necessity_witness": gate_witness,
        "old_exact_singleton_decoder_failure": old_witness,
        "old_decoder_witness_scope": (
            "If present: all profile fragments exist, but the old positive hull fails root coverage "
            "or transitivity at a nonsaturated seed. This is a local-lemma example, not a PSC model."
        ),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=4, choices=range(1, 5))
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("monochromatic_decoder_audit.json"))
    args = parser.parse_args()
    started = time.perf_counter()
    result = audit(args.max_n)
    result["elapsed_seconds"] = round(time.perf_counter() - started, 3)
    result["script_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
