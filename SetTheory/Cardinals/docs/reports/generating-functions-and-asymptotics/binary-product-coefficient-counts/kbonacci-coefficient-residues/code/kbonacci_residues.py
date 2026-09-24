"""Exact finite-state coefficient counting for Stanley's k-bonacci products.

All words are read from LOW weight to HIGH weight. Core routines use only
Python's standard library and integer arithmetic. See article.tex for proofs.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, Sequence


def _check_k(k: int) -> None:
    if not isinstance(k, int) or k < 2:
        raise ValueError("k must be an integer at least 2")


def weights(k: int, n: int) -> list[int]:
    """Return F_k^(k), ..., F_(k+n-1)^(k), with F_1=...=F_k=1."""
    _check_k(k)
    if not isinstance(n, int) or n < 0:
        raise ValueError("n must be a nonnegative integer")
    f = [1] * k
    for _ in range(max(0, n - 1)):
        f.append(sum(f[-k:]))
    return f[k - 1:k - 1 + n]


def multiply_factor(coefficients: Sequence[int], weight: int) -> list[int]:
    """Multiply a dense coefficient vector by 1+x**weight."""
    if weight < 1:
        raise ValueError("weight must be positive")
    result = [0] * (len(coefficients) + weight)
    for j, c in enumerate(coefficients):
        result[j] += c
        result[j + weight] += c
    return result


def expand(k: int, n: int) -> list[int]:
    """Exact dense coefficients, INCLUDING zero positions through the degree."""
    coefficients = [1]
    for w in weights(k, n):
        coefficients = multiply_factor(coefficients, w)
    return coefficients


def _word(word: Iterable[int]) -> tuple[int, ...]:
    bits = tuple(word)
    if any(bit not in (0, 1) for bit in bits):
        raise ValueError("a word must contain only 0 and 1")
    return bits


def is_canonical(word: Iterable[int], k: int) -> bool:
    _check_k(k)
    run = 0
    for bit in _word(word):
        if bit == 0:
            if run >= k:
                return False
            run = 0
        else:
            run += 1
    return True


def normalize(word: Iterable[int], k: int) -> tuple[int, ...]:
    """Apply 1**k 0 -> 0**k 1, using the leftmost available rewrite."""
    _check_k(k)
    bits = list(_word(word))
    target = [1] * k + [0]
    while True:
        for i in range(len(bits) - k):
            if bits[i:i + k + 1] == target:
                bits[i:i + k + 1] = [0] * k + [1]
                break
        else:
            return tuple(bits)


def value(word: Iterable[int], k: int) -> int:
    bits = _word(word)
    return sum(b * w for b, w in zip(bits, weights(k, len(bits))))


def counter_step(vector: tuple[int, ...], bit: int,
                 modulus: int | None = None,
                 cap: int | None = None) -> tuple[int, ...]:
    """The exact Z/O recurrence, optionally reduced or saturated."""
    if len(vector) < 3 or bit not in (0, 1):
        raise ValueError("invalid counter vector or input bit")
    if modulus is not None and cap is not None:
        raise ValueError("choose modulus OR cap")
    if modulus is not None and modulus < 2:
        raise ValueError("modulus must be at least 2")
    if cap is not None and cap < 1:
        raise ValueError("cap must be positive")
    p, *b = vector
    total = p + b[-1]
    if modulus is not None:
        total %= modulus
    if cap is not None:
        total = min(total, cap)
    if bit == 0:
        return (p, total, *b[:-1])
    return (total, b[-1], *((0,) * (len(b) - 1)))


def coefficient_for_canonical(word: Iterable[int], k: int) -> int:
    bits = _word(word)
    if not is_canonical(bits, k):
        raise ValueError("input is not canonical")
    vector = (1,) + (0,) * k
    for bit in bits:
        vector = counter_step(vector, bit)
    return vector[0]


@dataclass
class CountingMachine:
    """Reachable deterministic states; -1 denotes a rejecting transition."""
    states: list[tuple[tuple[int, ...], int]]
    edges: list[tuple[int, int]]
    k: int
    modulus: int | None
    cap: int | None

    def distributions(self, n_max: int) -> list[list[int]]:
        """Count canonical words by output counter value, for 0<=n<=n_max."""
        if n_max < 0:
            raise ValueError("n_max must be nonnegative")
        width = self.modulus if self.modulus is not None else self.cap + 1
        counts = [1] + [0] * (len(self.states) - 1)
        answer = []
        for n in range(n_max + 1):
            row = [0] * width
            for count, (vector, _) in zip(counts, self.states):
                row[vector[0]] += count
            answer.append(row)
            if n == n_max:
                break
            nxt = [0] * len(counts)
            for count, targets in zip(counts, self.edges):
                if count:
                    for target in targets:
                        if target >= 0:
                            nxt[target] += count
            counts = nxt
        return answer

    def certificate_dict(self) -> dict:
        return {
            "k": self.k, "modulus": self.modulus, "cap": self.cap,
            "initial_state": 0,
            "states": [{"counter": list(v), "run": r} for v, r in self.states],
            "edges_by_input_0_1": [list(e) for e in self.edges],
            "rejecting_transition": -1,
        }


def build_machine(k: int, *, modulus: int | None = None,
                  cap: int | None = None,
                  max_states: int = 1_000_000) -> CountingMachine:
    """Build a residue or capped-counter machine by deterministic BFS.

    To count coefficients exactly q, use cap=q+1 and final counter q.
    A guard raises an error rather than silently truncating a large machine.
    """
    _check_k(k)
    if (modulus is None) == (cap is None):
        raise ValueError("supply exactly one of modulus and cap")
    if modulus is not None and modulus < 2:
        raise ValueError("modulus must be at least 2")
    if cap is not None and cap < 1:
        raise ValueError("cap must be at least 1")
    initial = ((1,) + (0,) * k, 0)
    states = [initial]
    index = {initial: 0}
    edges = []
    for vector, run in states:
        targets = []
        for bit in (0, 1):
            if bit == 0 and run == k:
                targets.append(-1)
                continue
            next_run = 0 if bit == 0 else min(k, run + 1)
            state = (counter_step(vector, bit, modulus, cap), next_run)
            if state not in index:
                if len(states) >= max_states:
                    raise RuntimeError(f"state limit {max_states} exceeded")
                index[state] = len(states)
                states.append(state)
            targets.append(index[state])
        edges.append(tuple(targets))
    return CountingMachine(states, edges, k, modulus, cap)


def support_counts(k: int, n_max: int) -> list[int]:
    """Coefficients of 1/(1-2z+z**(k+1))."""
    _check_k(k)
    result = [1]
    for n in range(1, n_max + 1):
        result.append(2 * result[-1] - (result[n-k-1] if n > k else 0))
    return result


def hole_counts(k: int, n_max: int) -> list[int]:
    support = support_counts(k, n_max)
    return [sum((k-j) * support[n-j]
                for j in range(2, min(k-1, n) + 1))
            for n in range(n_max + 1)]


def residue_counts(k: int, modulus: int, n_max: int,
                   *, include_holes: bool = True) -> list[list[int]]:
    rows = build_machine(k, modulus=modulus).distributions(n_max)
    if include_holes:
        for row, holes in zip(rows, hole_counts(k, n_max)):
            row[0] += holes
    return rows


def parity_machine(k: int) -> tuple[list[str], list[tuple[int, int]], list[bool]]:
    """Uniform 4k+2-state DFA, including the dead state X."""
    _check_k(k)
    names = ([f"A{j}" for j in range(k+1)]
             + [f"B{j}" for j in range(2, k+1)]
             + [f"C{j}" for j in range(1, k+1)]
             + ["D"] + [f"E{j}" for j in range(2, k+1)] + ["F", "X"])
    edges: dict[str, tuple[str, str]] = {}
    for j in range(k):
        edges[f"A{j}"] = (f"A{j+1}", "C1")
    edges[f"A{k}"] = ("B2", "D")
    for j in range(2, k):
        edges[f"B{j}"] = (f"B{j+1}", "D")
    edges[f"B{k}"] = ("A0", "D")
    for j in range(1, k):
        edges[f"C{j}"] = ("A1", f"C{j+1}")
    edges[f"C{k}"] = ("X", f"C{k}")
    edges["D"] = ("E2", "X")
    for j in range(2, k):
        edges[f"E{j}"] = (f"E{j+1}", "X")
    edges[f"E{k}"] = ("D", "F")
    edges["F"] = ("A2", "C2")
    edges["X"] = ("X", "X")
    index = {s: i for i, s in enumerate(names)}
    return (names, [tuple(index[t] for t in edges[s]) for s in names],
            [s[0] in "ABCF" for s in names])


def dfa_sequence(edges: Sequence[tuple[int, int]], final: Sequence[bool],
                 n_max: int) -> list[int]:
    counts = [1] + [0] * (len(edges) - 1)
    answer = []
    for n in range(n_max + 1):
        answer.append(sum(c for c, accept in zip(counts, final) if accept))
        if n == n_max:
            break
        nxt = [0] * len(edges)
        for c, targets in zip(counts, edges):
            for t in targets:
                if t >= 0:
                    nxt[t] += c
        counts = nxt
    return answer


def odd_counts(k: int, n_max: int) -> list[int]:
    _check_k(k)
    answer = [1]
    for n in range(1, n_max + 1):
        if n <= k:
            answer.append(2 ** n)
        else:
            answer.append(2*answer[n-1] - 2*answer[n-k] + 2*answer[n-k-1])
    return answer


def rational_series(numerator: Sequence[int], denominator: Sequence[int],
                    n_max: int) -> list[int]:
    """Exact expansion for an integer rational series with denominator[0]=1."""
    if not denominator or denominator[0] != 1:
        raise ValueError("denominator constant must be 1")
    answer = []
    for n in range(n_max + 1):
        answer.append((numerator[n] if n < len(numerator) else 0)
                      - sum(denominator[j]*answer[n-j]
                            for j in range(1, min(n, len(denominator)-1) + 1)))
    return answer


if __name__ == "__main__":
    import argparse
    import json
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("k", type=int)
    parser.add_argument("modulus", type=int)
    parser.add_argument("n_max", type=int)
    parser.add_argument("--exclude-holes", action="store_true")
    args = parser.parse_args()
    print(json.dumps(residue_counts(args.k, args.modulus, args.n_max,
                                   include_holes=not args.exclude_holes)))
