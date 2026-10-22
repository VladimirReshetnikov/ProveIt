#!/usr/bin/env python3
"""Exact finite-window to fixed-numeral compiler for the modified75 system.

This is a standalone port of ProveIt's compile_windows functions at
cdd582bec13f908df3711fa9e05d1ddac368a5db. It uses standard-library integer
arithmetic only. It does not decide any machine's halting problem.

The ordered windows must start with Start, End. All remaining windows are
ordered lexicographically. For the delivered ZFC instance their exact finite
enumeration is specified by the companion normalized-machine module.

The constants can have astronomically many bits. compile_windows constructs
the sparse finite recipe; constants_mod evaluates it modulo a supplied
positive modulus without allocating the full constants. The optional
materialize method is deliberately explicit, and has a bit-size guard.
"""
from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
from itertools import product
import json
from pathlib import Path

SNAPSHOT = "cdd582bec13f908df3711fa9e05d1ddac368a5db"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def next_five_power(value: int) -> int:
    """Least power of 5 greater than or equal to value, including 5**0."""
    result = 1
    while result < value:
        result *= 5
    return result


def add_term(poly: dict[int, int], exponent: int, coefficient: int) -> None:
    poly[exponent] = poly.get(exponent, 0) + coefficient


@dataclass
class Compiled:
    windows: tuple[tuple[int, ...], ...]
    a: int
    A: int
    coeff: dict[int, int]
    mu: int
    padding: int
    m: int
    positions: tuple[int, ...]
    payload: dict[tuple[int, int, int], int]
    dummy: tuple[int, ...]
    anchors: tuple[int, ...]
    anchor_unit: int
    H: int
    T1: int
    T2: int
    L: int
    radix_bits: int
    d: int
    DCpoly: dict[int, int]
    MFpoly: dict[int, int]
    high_degree: int
    high_correction: int
    old_unit_mod5: int
    unit_mod5: int

    @property
    def extra_dummy(self) -> int:
        return self.dummy[0]

    @property
    def R(self) -> int:
        return 1 << self.radix_bits

    @property
    def MF_native_poly(self) -> dict[int, int]:
        result = dict(self.MFpoly)
        add_term(result, 0, 4)
        return result

    def constants_mod(self, modulus: int, raw_input: int = 1) -> dict[str, int]:
        """Exact residues of the fixed numerals. No approximate arithmetic."""
        require(type(modulus) is int and modulus > 0, "positive integer modulus required")
        require(type(raw_input) is int and raw_input > 0, "positive fixed raw input required")
        b, d = self.radix_bits, self.d
        B = pow(2, d, modulus)
        evaluate = lambda p: sum(c * pow(2, b * e, modulus) for e, c in p.items()) % modulus
        DC = evaluate(self.DCpoly)
        DR = pow(2, b * self.H, modulus)
        MC = (B - 1 - sum(pow(2, b * e, modulus)
                          for e in self.positions if e != 1)
              - 2 * pow(2, b * self.extra_dummy, modulus)) % modulus
        MF = (evaluate(self.MFpoly) + 4) % modulus
        return {
            "B": B, "DC": DC, "DR": DR,
            "MC": MC, "MF_native": MF,
            "Bm1": (B - 1) % modulus,
            "Kconstant": (DC + B * DR) % modulus,
            "twice_cell_bits": (2 * d) % modulus,
            "inner_bits": b % modulus,
            "MF": (MF + B - 1) % modulus,
            "W0": pow(2, b + 2 * d * raw_input, modulus),
        }

    def materialize(self, raw_input: int = 1, max_bits: int = 1_000_000) -> dict[str, int]:
        """Materialize all fixed constants only if within the explicit limit."""
        largest_bit = self.radix_bits + 2 * self.d * raw_input + 2
        require(largest_bit <= max_bits,
                f"fixed constants require up to {largest_bit} bits; max_bits={max_bits}")
        b, d = self.radix_bits, self.d
        B = 1 << d
        evaluate = lambda p: sum(c << (b * e) for e, c in p.items())
        DC, DR = evaluate(self.DCpoly), 1 << (b * self.H)
        MC = B - 1 - sum(1 << (b * e) for e in self.positions if e != 1)
        MC -= 2 << (b * self.extra_dummy)
        MF = evaluate(self.MFpoly) + 4
        require(0 < MC < B - 1 and 0 < MF < B - 1, "native mask range failure")
        require(MC % 4 == 2 and MF % 8 == 4, "native mask residue failure")
        require(MC.bit_count() + MF.bit_count() == d, "native mask population failure")
        return {"B": B, "DC": DC, "DR": DR, "MC": MC, "MF_native": MF,
                "Bm1": B - 1, "Kconstant": DC + B * DR,
                "twice_cell_bits": 2 * d, "inner_bits": b,
                "MF": MF + B - 1, "W0": 1 << (b + 2 * d * raw_input)}

    def recipe(self, raw_input: int = 1) -> dict:
        """JSON-serializable exact sparse recipe, without expanded constants."""
        require(type(raw_input) is int and raw_input > 0, "positive fixed raw input required")
        # Large coefficients are represented as hexadecimal strings so Python's
        # decimal conversion limit is irrelevant to this serialization.
        sparse = lambda p: [[e, hex(c)] for e, c in sorted(p.items())]
        return {
            "source_snapshot": SNAPSHOT,
            "window_count": len(self.windows), "tile_alphabet_size": self.a,
            "A": hex(self.A), "mu": hex(self.mu),
            "padding": self.padding, "m": self.m,
            "positions": list(self.positions), "dummy": list(self.dummy),
            "anchors": list(self.anchors), "anchor_unit": self.anchor_unit,
            "H": self.H, "T1": self.T1, "T2": self.T2, "L": self.L,
            "inner_bits": self.radix_bits, "cell_bits": self.d,
            "high_degree": self.high_degree, "high_correction": self.high_correction,
            "unit_mod5": self.unit_mod5, "DCpoly_hex": sparse(self.DCpoly),
            "MFbase_poly_hex": sparse(self.MFpoly), "extra_dummy": self.extra_dummy,
            "definitions": {
                "R": "2^inner_bits", "B": "2^cell_bits",
                "DC": "sum(c*R^e for (e,c) in DCpoly_hex)",
                "DR": "R^H",
                "MC": "B-1-sum(R^e for e in positions if e!=1)-2*R^extra_dummy",
                "MF_native": "sum(c*R^e for (e,c) in MFbase_poly_hex)+4",
                "Bm1": "B-1", "Kconstant": "DC+B*DR",
                "MF": "MF_native+B-1",
                "twice_cell_bits": "2*cell_bits",
                "W0": f"2^(inner_bits+2*cell_bits*{raw_input})",
            },
        }


def compile_windows(windows, alphabet_size: int) -> Compiled:
    """Faithful deterministic modified75 layout, with no semantic assumptions.

    Input validity here checks syntax. Acceptance equivalence additionally
    uses the helical local-rule theorem and the complete75 arithmetic theorem.
    """
    windows = tuple(tuple(w) for w in windows)
    a, k = alphabet_size, len(windows)
    require(type(a) is int and a > 0, "positive alphabet size required")
    require(k >= 2 and len(set(windows)) == k, "at least two distinct windows required")
    require(all(len(w) == 9 and all(type(s) is int and 0 <= s < a for s in w)
                for w in windows), "windows must have nine tile indices")
    A = 1 << max(2, (k + 1).bit_length())
    start = k + 3 * a
    payload = {(r, c, s): start + (2-r)*3*a + (2-c)*a + s
               for r, c, s in product(range(3), range(3), range(a))}
    coeff = {i: 1 for i in range(k)}
    mu = A - 2
    for j, ((r, c, s), e) in enumerate(payload.items(), 1):
        value = A ** j
        coeff[e] = value
        mu += value
        for i, w in enumerate(windows):
            if w[3*r+c] == s:
                coeff[i] += value
    anchor_coeff = []
    for j in range(1+9*a, 1+9*a+4):
        value = A ** j
        anchor_coeff.append(value)
        mu += value
        for i in range(k):
            coeff[i] += value
    padding = 0
    m = 2 * mu.bit_count() + 12*a + 2
    next_clause = 1 + 9*a + 4
    while m + 1 < k + 9*a + 5:
        mu += A ** (next_clause + padding)
        padding += 1
        m += 2
    dummy = tuple(range(start+9*a, start+9*a + (m+1-k-9*a-4)))
    require(bool(dummy), "missing control dummy")
    old_positions = tuple(range(k)) + tuple(payload.values()) + dummy
    M0 = max(old_positions) + 3*a + 1
    anchors = tuple(mult*M0 for mult in (1, 3, 9, 27))
    positions = old_positions + anchors
    for e, value in zip(anchors, anchor_coeff):
        coeff[e] = value
    require(len(set(positions)) == len(positions) == m+1, "position collision")
    E = max(positions)
    H = E + 24*M0 + 3*a + 1
    T1 = H + 2*E + a + 1
    T2 = T1 + 2*E + 1
    high_degree = T2 + E + 1
    L = next_five_power(high_degree + E + 1)
    DCpoly = {}
    for e in (3*a, H+a, 8*M0, 24*M0):
        add_term(DCpoly, e, 1)
    for e, value in coeff.items():
        add_term(DCpoly, T1-e, value)
        add_term(DCpoly, T2-e, value)
    old_unit = (2*sum(c*pow(2, e, 5) for e, c in DCpoly.items()) - pow(2, H, 5)) % 5
    high_correction = int(old_unit == 0)
    if high_correction:
        add_term(DCpoly, high_degree, 1)
    unit = (2*sum(c*pow(2, e, 5) for e, c in DCpoly.items()) - pow(2, H, 5)) % 5
    require(unit != 0, "nonunit dummy-control coefficient")
    MFpoly = {T1: mu, T2: mu}
    for r, c, s in product(range(2), range(3), range(a)):
        add_term(MFpoly, payload[r, c, s], 1)
    for r, c, s in product(range(3), range(2), range(a)):
        add_term(MFpoly, H + payload[r, c, s], 1)
    for e in anchors[2:]:
        add_term(MFpoly, e, 1)
    require(sum(v.bit_count() for v in MFpoly.values()) == m, "mask population mismatch")
    require(max(DCpoly)+E < L and max(MFpoly) < high_degree, "coefficient support overflow")
    K = len(positions)
    mass = (K+2)*(2*sum(coeff.values())+6)
    target = max(4*mass+8, 2*mu+4, 16)
    radix_bits = next_five_power((target-1).bit_length())
    d = radix_bits * L
    require(dummy[0]+1 < E, "control dummy support overflow")
    require(mass <= (1 << radix_bits)//4-2, "radix bound failure")
    return Compiled(windows, a, A, coeff, mu, padding, m, positions, payload,
                    dummy, anchors, M0, H, T1, T2, L, radix_bits, d,
                    DCpoly, MFpoly, high_degree, high_correction, old_unit, unit)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--windows-json", type=Path, required=True,
                        help='JSON object with "alphabet_size" and ordered "windows"')
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    source = json.loads(args.windows_json.read_text())
    compiled = compile_windows(source["windows"], source["alphabet_size"])
    args.output.write_text(json.dumps(compiled.recipe(), indent=2) + "\n")
    print(json.dumps({"window_count": len(compiled.windows),
                      "cell_bits": compiled.d,
                      "mod_1000000007": compiled.constants_mod(1000000007)}, indent=2))


if __name__ == "__main__":
    main()
