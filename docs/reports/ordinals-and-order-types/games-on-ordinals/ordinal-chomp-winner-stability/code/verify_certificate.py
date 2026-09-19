#!/usr/bin/env python3
"""Independently verify the ordinal-Chomp certificate by exact finite games.

Python 3.9+, standard library only.  Does not import the certificate generator.
It reconstructs S by dynamic programming, solves all 4,301 displayed positions
using untruncated integer Grundy values, checks the local residual identities,
and checks the repeated 187-entry boundary state.  The article proves why that
last finite check entails the infinite assertion.
"""
import argparse
import csv
from functools import lru_cache
import hashlib
import itertools
import json
from pathlib import Path
import sys
from typing import Dict, List, Set, Tuple


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def mex(values) -> int:
    values = set(values)
    result = 0
    while result in values:
        result += 1
    return result


def check_certificate(path: Path, output_dir: Path = None) -> Dict:
    certificate_bytes = path.read_bytes()
    cert = json.loads(certificate_bytes)
    require(cert["generators"] == [4, 6, 9], "Wrong generators")
    require(cert["cutoff"] == 2, "Wrong cutoff")
    require((cert["row_first"], cert["row_last"]) == (12, 264), "Wrong row range")
    require((cert["state_first"], cert["state_repeat"]) == (237, 265), "Wrong state claim")
    require((cert["period_start"], cert["period"]) == (226, 28), "Wrong period claim")
    require(cert["prefix_low_values"] == [], "Unexpected prefix")
    first, last = cert["row_first"], cert["row_last"]
    bound = last + 11

    # Independent membership calculation from generators, not from a gap list.
    membership = [False] * (bound + 1)
    membership[0] = True
    for n in range(1, bound + 1):
        membership[n] = any(n >= a and membership[n-a] for a in [4, 6, 9])
    gaps = tuple(n for n, present in enumerate(membership) if not present)
    require(gaps == (1, 2, 3, 5, 7, 11), "Unexpected semigroup gaps")
    require(cert["gaps"] == list(gaps), "Certificate gap mismatch")
    require(all(membership[n] for n in range(12, 16)), "Conductor witnesses fail")

    def belongs(n: int) -> bool:
        return n >= 0 and membership[n]

    # This enumeration is deliberately different from the generator's masks.
    ideals = []
    for size in range(len(gaps) + 1):
        for candidate in itertools.combinations(gaps, size):
            current = frozenset(candidate)
            if all(a in current for b in current for a in gaps if belongs(b-a)):
                ideals.append(current)
    ideals.sort(key=lambda c: (len(c), tuple(sorted(c))))
    require([sorted(c) for c in ideals] == cert["ideals"], "Gap-ideal list mismatch")
    require(len(ideals) == 17, "Wrong number of gap ideals")
    index = {c: i for i, c in enumerate(ideals)}
    full = index[frozenset(gaps)]
    require(full == 16 == cert["full_ideal_index"], "Wrong full-ideal index")

    # Exact normal-play game on positive elements only: 0 is poisoned/omitted.
    elements = [n for n in range(1, bound + 1) if membership[n]]
    bit = {n: 1 << i for i, n in enumerate(elements)}
    up = [sum(bit[y] for y in elements if y >= x and membership[y-x]) for x in elements]

    @lru_cache(maxsize=None)
    def grundy(mask: int) -> int:
        options = set()
        remaining = mask
        while remaining:
            selected = remaining & -remaining
            i = selected.bit_length() - 1
            remaining ^= selected
            options.add(grundy(mask & ~up[i]))
        return mex(options)

    def mask_of(position: Set[int]) -> int:
        return sum(bit[n] for n in position)

    def state(x: int, c) -> Set[int]:
        return {n for n in range(1, x) if membership[n]} | {x+g for g in c}

    # Fully reconstruct and solve EVERY finite position in the certificate.
    rows = {}
    exact = {}
    require(len(cert["rows"]) == last-first+1, "Wrong number of rows")
    for x, text in zip(range(first, last+1), cert["rows"]):
        require(len(text) == 17 and all(a in "012" for a in text), "Malformed row")
        exact[x] = tuple(grundy(mask_of(state(x, c))) for c in ideals)
        rows[x] = tuple(min(2, value) for value in exact[x])
        require(text == "".join(map(str, rows[x])), "Exact finite-game mismatch at x=" + str(x))
        require(rows[x][full] == 2, "Forbidden small Apéry value at x=" + str(x))

    # All exceptional small first moves, before the uniform boundary region.
    early = []
    for t in range(1, 12):
        if membership[t]:
            apery = {n for n in elements if n <= t+11 and not belongs(n-t)}
            value = grundy(mask_of(apery))
            require(value >= 2, "Small first-move exception")
            early.append([t, value])
    require(early == cert["early_apery_values"], "Early Apéry values mismatch")

    # Independently check every translation-invariant local residual identity
    # at x=23.  The proof shows that translating x does not change the identity.
    local_checks = 0
    recent_indices, tail_indices = [], []
    for c in ideals:
        original = state(23, c)
        recent_row, tail_row = [], []
        for distance in range(1, 12):
            move = 23-distance
            residual = {n for n in original if not belongs(n-move)}
            target_c = frozenset(g for g in gaps if g < distance or g-distance in c)
            require(target_c in index, "Recent target is not an ideal")
            require(residual == state(move, target_c), "Recent residual identity fails")
            recent_row.append(index[target_c])
            local_checks += 1
        for a in sorted(c):
            residual = {n for n in original if not belongs(n-(23+a))}
            target_c = frozenset(g for g in c if not belongs(g-a))
            require(target_c in index, "Tail target is not an ideal")
            require(residual == state(23, target_c), "Tail residual identity fails")
            tail_row.append(index[target_c])
            local_checks += 1
        recent_indices.append(recent_row)
        tail_indices.append(tail_row)
    require(recent_indices == cert["transition_recent_indices"], "Recent-transition mismatch")
    require(tail_indices == cert["transition_tail_indices"], "Tail-transition mismatch")

    # Replay the bounded recurrence, without consulting any exact high value.
    for x in range(23, 265):
        replayed = []
        for i in range(17):
            options = {rows[x-d][recent_indices[i][d-1]] for d in range(1, 12)}
            options.update(replayed[j] for j in tail_indices[i])
            replayed.append(min(2, mex(options)))
        require(tuple(replayed) == rows[x], "Local recurrence mismatch")

    before_first = tuple(rows[x] for x in range(226, 237))
    before_repeat = tuple(rows[x] for x in range(254, 265))
    require(before_first == before_repeat, "187-entry states do not coincide")
    require(all(rows[x] == rows[x+28] for x in range(226, 237)), "Period witness fails")
    require(rows[225] != rows[253], "Advertised onset is not minimal for period 28")

    # Small independent game-theoretic checks used in the written proof.
    diamond = [0, 6, 9, 15]
    def finite_poset_value(values, comparison):
        upper = [sum(1 << j for j, y in enumerate(values) if comparison(x, y)) for x in values]
        @lru_cache(maxsize=None)
        def sg(mask):
            return mex(sg(mask & ~u) for i, u in enumerate(upper) if mask >> i & 1)
        mask = (1 << len(values))-1
        return sg(mask), {sg(mask & ~u) for u in upper}
    d_value, d_options = finite_poset_value(diamond, lambda x, y: belongs(y-x))
    require(d_value == 3 and d_options == {0, 1, 2}, "Diamond check failed")

    # A finite analogue of the infinite gadget, not an infinite truncation:
    # P = one minimum below two chains of length 2.  g(P)=1, options {0,3,4}.
    def chain(n):
        return [[i <= j for j in range(n)] for i in range(n)]
    def join(a, b, ordered=False):
        na, nb = len(a), len(b)
        return [
            [a[i][j] if i < na and j < na else
             b[i-na][j-na] if i >= na and j >= na else
             bool(ordered and i < na and j >= na)
             for j in range(na+nb)] for i in range(na+nb)]
    def matrix_value(matrix):
        return finite_poset_value(list(range(len(matrix))), lambda i, j: matrix[i][j])
    h = join(chain(2), chain(2))
    p = join(chain(1), h, True)
    k = join(join(p, p), p, True)
    diamond_matrix = [[belongs(y-x) for y in diamond] for x in diamond]
    r = join(h, join(diamond_matrix, k), True)
    require(matrix_value(p) == (1, {0, 3, 4}), "Finite block check failed")
    require(matrix_value(k)[0] == 3, "Finite ordered gadget check failed")
    require(matrix_value(r)[0] == 0, "Finite residual gadget check failed")

    result = {
        "verified": True,
        "certificate_sha256": hashlib.sha256(certificate_bytes).hexdigest(),
        "finite_positions_checked": 253*17,
        "exact_solver_distinct_positions": grundy.cache_info().currsize,
        "local_residual_identities_checked": local_checks,
        "rows_checked": 253,
        "early_apery_values": early,
        "window_entries": 187,
        "state_first": 237, "state_repeat": 265,
        "period": 28, "period_start": 226,
        "all_full_ideal_labels": [2],
        "diamond_normal_value": 3,
        "finite_analogue_residual_value": 0,
        "method": "Exact untruncated finite-poset recursion, local identities, recurrence, repeated state",
        "formal_proof_assistant_checked": False,
    }
    if output_dir is not None:
        output_dir.mkdir(parents=True, exist_ok=True)
        (output_dir/"verification.json").write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
        with (output_dir/"exact_boundary_values.csv").open("w", newline="", encoding="utf-8") as f:
            writer = csv.writer(f)
            writer.writerow(["x"]+["C"+str(i) for i in range(17)])
            writer.writerows([x]+list(exact[x]) for x in range(first, last+1))
        with (output_dir/"apery_values.csv").open("w", newline="", encoding="utf-8") as f:
            writer = csv.writer(f)
            writer.writerow(["first_move", "poisoned_apery_grundy", "normal_apery_grundy"])
            writer.writerows([t, value, value+1] for t, value in early)
            writer.writerows([x, exact[x][full], exact[x][full]+1] for x in range(first, last+1))
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    root = Path(__file__).resolve().parents[1]
    parser.add_argument("certificate", nargs="?", type=Path, default=root/"data"/"certificate.json")
    parser.add_argument("--output-dir", type=Path, default=root/"data")
    args = parser.parse_args()
    result = check_certificate(args.certificate, args.output_dir)
    print("VERIFIED")
    print("Exact finite positions:", result["finite_positions_checked"])
    print("Memoized finite states:", result["exact_solver_distinct_positions"])
    print("Local residual identities:", result["local_residual_identities_checked"])
    print("Repeated boundary state: 237 = 265 (187 entries); period 28")
    print("All full-ideal labels are 2, meaning Grundy value at least 2.")
    print("SHA-256:", result["certificate_sha256"])


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, OSError, json.JSONDecodeError) as error:
        print("VERIFICATION FAILED:", error, file=sys.stderr)
        sys.exit(1)
