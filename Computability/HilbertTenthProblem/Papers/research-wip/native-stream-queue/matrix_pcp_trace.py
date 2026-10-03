#!/usr/bin/env python3
"""Exact PCP/matrix trace checks; no universal Diophantine bound is claimed."""
from __future__ import annotations

import argparse
from collections import Counter, deque
from itertools import product
import json
from pathlib import Path


def value(word: str, radix: int = 3) -> int:
    result = 0
    for letter in word:
        result = radix * result + int(letter)
    return result


def code(word: str) -> int:
    return 3 ** len(word) + value(word)


def packed(values: list[int], radix: int) -> int:
    return sum(v * radix ** i for i, v in enumerate(values))


class Circuit:
    def __init__(self) -> None:
        self.counts: Counter[str] = Counter()

    def add(self, x: int, y: int) -> int:
        self.counts["A"] += 1
        return x + y

    def sub(self, x: int, y: int) -> int:
        self.counts["A"] += 1
        return x - y

    def mul(self, x: int, y: int) -> int:
        self.counts["M"] += 1
        return x * y

    def sum(self, xs: list[int]) -> int:
        assert xs
        result = xs[0]
        for x in xs[1:]:
            result = self.add(result, x)
        return result


def aggregate_residuals(c: Circuit, B: int, Q: int, z: int,
                        H: tuple[int, int], P: tuple[int, int],
                        C: tuple[int, int], A: int, K: int, beta: int
                        ) -> tuple[int, int, int]:
    endpoint = c.sub(c.mul(z, Q), 1)
    residuals = []
    for h, p, d in zip(H, P, C):
        left = c.mul(B, c.add(p, d))
        right = c.add(h, endpoint)
        # Subtraction here records an equality residual, not a paid DAG gate.
        residuals.append(left - right)
    margin = c.add(c.add(c.mul(A, K), A), beta)
    return (*residuals, B - margin)


def split_residuals(c: Circuit, tiles: tuple[tuple[str, str], ...],
                    B: int, Q: int, z: int,
                    shifted_H: tuple[list[int], list[int]], shifted_S: list[int],
                    K: int, beta: int, positive: bool
                    ) -> tuple[int, int, int]:
    """Literal 10m+5 nonnegative / 10m+7 positive-coordinate schedule."""
    H, V = [], []
    for lane in range(2):
        words = [tile[lane] for tile in tiles]
        slopes = [3 ** len(w) for w in words]
        offsets = [value(w) for w in words]
        terms = [c.mul(a, h) for a, h in zip(slopes, shifted_H[lane])]
        terms += [c.mul(d, s) for d, s in zip(offsets, shifted_S)]
        v = c.sum(terms)
        h = c.sum(shifted_H[lane])
        if positive:
            # The corrections are fixed numerals; constructing them is free.
            v = c.sub(v, sum(slopes) + sum(offsets))
        V.append(v)
        H.append(h)
    # Each hatted H exceeds its unshifted field by m.  Absorb the same
    # correction for both lanes into this already-paid fixed endpoint offset.
    endpoint = c.sub(c.mul(z, Q), len(tiles) + 1 if positive else 1)
    residuals = [c.mul(B, v) - c.add(h, endpoint) for v, h in zip(V, H)]
    A = max(3 ** len(w) for tile in tiles for w in tile)
    margin = c.add(c.add(c.mul(A, K), A), beta)
    return (*residuals, B - margin)


def cancel(top: str, bottom: str) -> tuple[str, str] | None:
    if top.startswith(bottom):
        return top[len(bottom):], ""
    if bottom.startswith(top):
        return "", bottom[len(top):]
    return None


def residual_step(state: tuple[str, str], tile: tuple[str, str], D: int
                  ) -> tuple[str, str] | None:
    result = cancel(state[0] + tile[0], state[1] + tile[1])
    if result is None or max(map(len, result)) > D:
        return None
    return result


def bounded_automaton(tiles: tuple[tuple[str, str], ...], D: int
                      ) -> tuple[set[tuple[str, str]], dict]:
    origin = ("", "")
    states = {origin}
    todo = deque([origin])
    transitions = {}
    while todo:
        state = todo.popleft()
        for i, tile in enumerate(tiles):
            target = residual_step(state, tile, D)
            transitions[state, i] = target
            if target is not None and target not in states:
                states.add(target)
                todo.append(target)
    # Alphabet size two: epsilon, or a nonempty residual on either side.
    assert len(states) <= 1 + 2 * sum(2 ** j for j in range(1, D + 1))
    return states, transitions


def matrix_product_code(tiles: tuple[tuple[str, str], ...], indices: tuple[int, ...]
                        ) -> tuple[int, int]:
    # Independent dense 3x3 multiplication, acting on a column vector.
    total = [[int(i == j) for j in range(3)] for i in range(3)]
    for i in indices:
        u, v = tiles[i]
        matrix = [[3 ** len(u), 0, value(u)],
                  [0, 3 ** len(v), value(v)], [0, 0, 1]]
        total = [[sum(matrix[r][k] * total[k][s] for k in range(3))
                  for s in range(3)] for r in range(3)]
    return sum(total[0]), sum(total[1])


def check() -> dict:
    counts: Counter[str] = Counter()
    # Includes a nontrivial two-tile match: 1|21 = 12|1.
    instances = (
        (("1", "12"), ("21", "1")),
        (("1", "1"), ("2", "2"), ("12", "21")),
        (("12", "1"), ("1", "21"), ("2", "22")),
        (("1", "2"), ("2", "1"), ("11", "22")),
        (("1", "1"), ("12", "12"), ("2", "2"), ("21", "21"), ("11", "11")),
    )
    for tiles in instances:
        m = len(tiles)
        A = max(3 ** len(w) for tile in tiles for w in tile)
        for length in range(1, 5):
            for indices in product(range(m), repeat=length):
                words = ["", ""]
                histories = [[], []]
                successors = [[], []]
                constants = [[], []]
                for i in indices:
                    for lane in range(2):
                        histories[lane].append(code(words[lane]))
                        successors[lane].append(3 ** len(tiles[i][lane]) * code(words[lane]))
                        constants[lane].append(value(tiles[i][lane]))
                        words[lane] += tiles[i][lane]
                endpoints = tuple(map(code, words))
                assert endpoints == matrix_product_code(tiles, indices)
                assert (endpoints[0] == endpoints[1]) == (words[0] == words[1])
                K = max(endpoints)
                B = A * K + A + 1
                Q = B ** length
                H = tuple(packed(h, B) for h in histories)
                P = tuple(packed(h, B) for h in successors)
                C = tuple(packed(h, B) for h in constants)
                z = endpoints[0]
                c = Circuit()
                residuals = aggregate_residuals(c, B, Q, z, H, P, C, A, K, 1)
                assert c.counts == {"M": 4, "A": 7}
                assert (residuals == (0, 0, 0)) == (words[0] == words[1])
                S = [packed([int(i == j) for i in indices], B) for j in range(m)]
                split_H = tuple([packed([h if i == j else 0 for h, i in zip(histories[lane], indices)], B)
                                 for j in range(m)] for lane in range(2))
                for positive in (False, True):
                    shift = int(positive)
                    sh = tuple([h + shift for h in lane] for lane in split_H)
                    ss = [s + shift for s in S]
                    cc = Circuit()
                    rr = split_residuals(cc, tiles, B, Q, z, sh, ss, K, 1, positive)
                    assert rr == residuals
                    assert cc.counts == {"M": 4 * m + 4, "A": 6 * m + 1 + 2 * shift}
                    if positive:
                        assert all(v > 0 for lane in sh for v in lane) and min(ss) > 0
                counts["matrix_and_three_trace_circuits"] += 1
                counts["matching_words"] += int(words[0] == words[1])

        # The positive adapter is an algebraic identity on arbitrary fields,
        # not only on typed traces.  In particular its computed endpoint
        # register may be negative; only supplied coordinates are positive.
        for seed in range(16):
            sh = tuple([1 + (seed + 3*lane + j) % 5 for j in range(m)]
                       for lane in range(2))
            ss = [1 + (2*seed + j) % 4 for j in range(m)]
            raw_h = tuple([h-1 for h in lane] for lane in sh)
            raw_s = [s-1 for s in ss]
            cc, dd = Circuit(), Circuit()
            positive = split_residuals(cc, tiles, 2, 1, 1, sh, ss, 1, 1, True)
            nonnegative = split_residuals(dd, tiles, 2, 1, 1, raw_h, raw_s, 1, 1, False)
            assert positive == nonnegative
            assert 1*1-(m+1) < 0
            assert cc.counts == {"M": 4*m+4, "A": 6*m+3}
            counts["arbitrary_positive_adapter_identities"] += 1

        for D in range(5):
            _, transitions = bounded_automaton(tiles, D)
            for length in range(1, 6):
                for indices in product(range(m), repeat=length):
                    state = ("", "")
                    top = bottom = ""
                    good = True
                    for i in indices:
                        top += tiles[i][0]
                        bottom += tiles[i][1]
                        good &= abs(len(top) - len(bottom)) <= D
                        if state is not None:
                            state = transitions[state, i]
                    assert (state == ("", "")) == (top == bottom and good)
                    counts["automaton_vs_direct_words"] += 1

    # Exhaust all supplied short histories, not merely histories generated by updates.
    # Here a_t and c_t range independently; this tests the carry lemma beyond PCP.
    A, K, beta, h = 3, 4, 1, 2
    B = A * K + A + beta
    for xs in product(range(1, K + 1), repeat=h + 1):
        for slopes in product(range(1, A + 1), repeat=h):
            for constants in product(range(A), repeat=h):
                residuals = [a * x + c - y for a, x, c, y in zip(slopes, xs, constants, xs[1:])]
                assert all(abs(r) < B for r in residuals)
                scalar = B * packed([a*x+c for a, x, c in zip(slopes, xs, constants)], B)
                scalar -= packed(list(xs[:-1]), B) + xs[-1] * B ** h - 1
                assert scalar == 1 - xs[0] + B * packed(residuals, B)
                assert (scalar == 0) == (xs[0] == 1 and all(r == 0 for r in residuals))
                counts["arbitrary_bounded_history_tests"] += 1

    # Deleting only the carry margin admits a wrong trace of the actual
    # append words '11', '1', with perfectly ordinary base-B history digits.
    B, xs, slopes, constants = 11, (1, 2, 8), (9, 3), (4, 1)
    errors = [a*x+c-y for a, x, c, y in zip(slopes, xs, constants, xs[1:])]
    assert errors == [11, -1] and packed(errors, B) == 0
    assert max(xs) < B and all(x > 0 for x in xs)
    false_H = packed(list(xs[:-1]), B)
    false_P = packed([a*x for a, x in zip(slopes, xs)], B)
    false_C = packed(list(constants), B)
    false_source = aggregate_residuals(
        Circuit(), B, B ** 2, xs[-1], (false_H, false_H),
        (false_P, false_P), (false_C, false_C), 9, max(xs), 1)
    assert false_source[:2] == (0, 0) and false_source[2] != 0

    # A fixed two-tile PCP system has solutions with arbitrarily large lag.
    # This is outside every fixed-D recognizer for sufficiently large n.
    tiles = (("11", "1"), ("1", "11"))
    for n in range(1, 21):
        indices = (0,) * n + (1,) * n
        top = "".join(tiles[i][0] for i in indices)
        bottom = "".join(tiles[i][1] for i in indices)
        assert top == bottom
        state = ("", "")
        for i in indices:
            state = None if state is None else residual_step(state, tiles[i], n - 1)
        assert state is None
        counts["unbounded_lag_family"] += 1

    return {
        "status": "pass",
        "aggregate_schedule": {"M": 4, "A": 7, "total": 11},
        "split_nonnegative_schedule": "(4m+4)M+(6m+1)A = 10m+5",
        "split_positive_schedule": "(4m+4)M+(6m+3)A = 10m+7",
        "five_tile_positive_schedule": {"M": 24, "A": 33, "total": 57},
        "tests": dict(counts),
        "carry_omission_counterexample": {"B": 11, "history": list(xs), "errors": errors},
        "scope": "Conditional finite PCP trace and fixed lag automaton; typing, selectors, powers, control, and raw input remain unpaid; complete75 unchanged.",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-receipt", action="store_true")
    args = parser.parse_args()
    receipt = check()
    receipt_path = Path(__file__).with_suffix(".json")
    if args.write_receipt:
        receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
    else:
        assert json.loads(receipt_path.read_text()) == receipt, "receipt mismatch"
    print(json.dumps(receipt, indent=2))
