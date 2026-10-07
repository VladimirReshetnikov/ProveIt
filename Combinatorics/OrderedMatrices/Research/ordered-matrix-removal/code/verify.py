#!/usr/bin/env python3
"""Exact finite checks for the ordered binary matrix research article.

Only the Python standard library is used. All mathematical comparisons are
integer or rational. The checks supplement the written proofs; they do not
constitute a Lean formalization or prove assertions at untested depths.

Run from any directory:
    python3 verify.py
    python3 -O verify.py
    python3 verify.py --extended
    python3 verify.py --anchor-s 4 --legacy-c4

The default JSON output is verification_results.json beside this program.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import combinations, product
import json
from math import comb, factorial
from pathlib import Path
import time


class VerificationError(RuntimeError):
    """An exact finite check failed."""


def require(condition, message):
    if not condition:
        raise VerificationError(message)


def fraction_record(value):
    return {"numerator": value.numerator, "denominator": value.denominator}


class TreeHost:
    """The complete binary host, with explicit twins or one per block.

    A block descriptor is ('A', mode, group), ('+', depth, node),
    ('-', depth, node), ('L', depth, node), or ('D', 0, 0).
    An expanded position is (block_descriptor, within_block_index).
    Compressed matrices retain the descriptor and its exact multiplicity.
    All role indices in this program are zero-based.
    """

    def __init__(self, depth, anchor_size=3, repaired=False):
        require(depth >= 1, "The tree depth must be positive.")
        require(anchor_size >= 2, "At least two anchor signatures are needed.")
        self.h = depth
        self.s = anchor_size
        self.m = 1 << depth
        self.repaired = repaired
        self.modes = []
        for i in range(1, depth + 1):
            self.modes.extend([("V", i, "+", None), ("V", i, "-", None)])
            self.modes.extend(("W", i, sign, d) for sign in ("+", "-")
                              for d in (0, 1))
        anchors = [("A", t, u) for t in range(len(self.modes))
                   for u in range(anchor_size)]
        self.dummy = ("D", 0, 0)
        self.row_blocks = anchors + self._walk(0, 0, True) + [self.dummy]
        self.col_blocks = anchors + [self.dummy] + self._walk(0, 0, False)
        self.row_index = {block: i for i, block in enumerate(self.row_blocks)}
        self.col_index = {block: i for i, block in enumerate(self.col_blocks)}
        self.dimension = ((6 * anchor_size + 2) * depth + 2) * self.m
        require(sum(self.weight(x) for x in self.row_blocks) == self.dimension,
                "Expanded row count is wrong.")
        require(sum(self.weight(x) for x in self.col_blocks) == self.dimension,
                "Expanded column count is wrong.")

    def _walk(self, depth, node, row):
        if depth == self.h:
            return [("L", depth, node)]
        first, last = ("-", "+") if row else ("+", "-")
        return ([(first, depth, node)] + self._walk(depth + 1, 2 * node, row)
                + self._walk(depth + 1, 2 * node + 1, row)
                + [(last, depth, node)])

    def weight(self, block):
        if block[0] in ("A", "D"):
            return self.m
        return self.m >> block[1]

    def expanded_axes(self):
        return ([ (b, j) for b in self.row_blocks for j in range(self.weight(b)) ],
                [ (b, j) for b in self.col_blocks for j in range(self.weight(b)) ])

    @staticmethod
    def _matches(block, depth, sign, parity=None):
        return (block[0] in (sign, "L") and block[1] == depth
                and (parity is None or block[2] % 2 == parity))

    def role(self, block, mode_index, row):
        kind, depth, sign, parity = self.modes[mode_index]
        match = self._matches
        if row:
            if kind == "V":
                if sign == "+":
                    return (0 if match(block, depth, sign) else
                            1 if match(block, depth - 1, sign) else None)
                return (0 if match(block, depth - 1, sign) else
                        1 if match(block, depth, sign) else None)
            return (0 if match(block, depth, sign, parity) else
                    1 if block[0] == "D" else None)
        if kind == "V":
            return (0 if block[0] == "D" else
                    1 if match(block, depth - 1, sign) else None)
        if sign == "+":
            return (0 if match(block, depth - 1, sign) else
                    1 if match(block, depth, sign, parity) else None)
        return (0 if match(block, depth, sign, parity) else
                1 if match(block, depth - 1, sign) else None)

    def entry(self, row, col):
        if row[0] == "A" and col[0] == "A":
            return int(row[1] == col[1] and row[2] != col[2])
        if row[0] == "A":
            return int(self.role(col, row[1], False) == row[2])
        if col[0] == "A":
            return int(self.role(row, col[1], True) == col[2])
        if row[0] == "D" or col[0] == "D":
            return int(not (self.repaired and row[0] == "D" and col[0] == "L"))
        sign, depth, node = row
        csign, cdepth, cnode = col
        if depth == cdepth:
            if sign in ("+", "L") and csign in ("+", "L"):
                return int(node <= cnode)
            if sign == csign == "-":
                return int(node < cnode)
        if depth == cdepth + 1:
            if sign in ("+", "L") and csign == "+":
                return int(node // 2 <= cnode)
            if sign in ("-", "L") and csign == "-":
                return int(node // 2 < cnode)
        return 0

    def compressed_matrix(self):
        return [bytearray(self.entry(r, c) for c in self.col_blocks)
                for r in self.row_blocks]

    def expanded_matrix(self):
        rows, cols = self.expanded_axes()
        return rows, cols, [bytearray(self.entry(r[0], c[0]) for c in cols)
                            for r in rows]


def pinned_anchor(rows, cols):
    return (all(p[0] == "A" for p in rows + cols)
            and len({p[1] for p in rows + cols}) == 1)


def exhaustive_anchor_check(host):
    """Inspect every ordered row quadruple and every viable column chain."""
    require(host.s == 4, "This exhaustive check is specialized to C4.")
    matrix = host.compressed_matrix()
    n = len(matrix)
    full = (1 << n) - 1
    bits = [sum(value << j for j, value in enumerate(row)) for row in matrix]
    found = 0
    viable_rows = 0
    for rr in combinations(range(n), 4):
        a, b, c, d = (bits[i] for i in rr)
        masks = [(~a & b & c & d) & full, (a & ~b & c & d) & full,
                 (a & b & ~c & d) & full, (a & b & c & ~d) & full]
        lower = -1
        feasible = True
        for mask in masks:
            mask &= full ^ ((1 << (lower + 1)) - 1)
            if not mask:
                feasible = False
                break
            lower = (mask & -mask).bit_length() - 1
        if not feasible:
            continue
        viable_rows += 1

        def visit(level, chosen):
            nonlocal found
            if level == 4:
                selected_rows = [host.row_blocks[i] for i in rr]
                selected_cols = [host.col_blocks[i] for i in chosen]
                require(pinned_anchor(selected_rows, selected_cols),
                        f"Unpinned C4 at h={host.h}, repair={host.repaired}: "
                        f"{selected_rows}; {selected_cols}")
                found += 1
                return
            mask = masks[level]
            if chosen:
                mask &= full ^ ((1 << (chosen[-1] + 1)) - 1)
            while mask:
                bit = mask & -mask
                mask -= bit
                visit(level + 1, chosen + [bit.bit_length() - 1])

        visit(0, [])
    require(found == 6 * host.h, "The compressed pinned-anchor count is wrong.")
    return {"depth": host.h, "repaired": host.repaired, "compressed_order": n,
            "row_quadruples": n * (n - 1) * (n - 2) * (n - 3) // 24,
            "viable_row_quadruples": viable_rows, "anchor_copies": found,
            "unpinned_copies": 0}


def exhaustive_full_pattern_check(host, stop_at_unpinned=False):
    """Enumerate full H(s) copies, since C3 prefixes alone need not be pinned.

    Every row set is inspected. Column-signature masks and the earliest
    increasing chain reject impossible row sets; every viable column chain
    is then enumerated. Twin multiplicities give exact expanded copy counts.
    The optional early exit is used solely to locate an H4 counterexample.
    """
    matrix = host.compressed_matrix()
    n, k = len(matrix), host.s + 2
    full = (1 << n) - 1
    bits = [sum(value << j for j, value in enumerate(row)) for row in matrix]
    expected = [[pattern_entry(i, j, host.s) for j in range(k)] for i in range(k)]
    ones = [[i for i in range(k) if expected[i][j]] for j in range(k)]
    zeros = [[i for i in range(k) if not expected[i][j]] for j in range(k)]
    inspected = viable = copies = weighted_copies = 0
    first_unpinned = None
    for rr in combinations(range(n), k):
        inspected += 1
        selected_bits = [bits[i] for i in rr]
        masks = []
        lower = -1
        for j in range(k):
            mask = full
            for i in ones[j]:
                mask &= selected_bits[i]
            for i in zeros[j]:
                mask &= ~selected_bits[i]
            masks.append(mask)
            later = mask & (full ^ ((1 << (lower + 1)) - 1))
            if not later:
                break
            lower = (later & -later).bit_length() - 1
        else:
            viable += 1

            def visit(level, chosen):
                nonlocal copies, weighted_copies, first_unpinned
                if level == k:
                    selected_rows = [host.row_blocks[i] for i in rr]
                    selected_cols = [host.col_blocks[i] for i in chosen]
                    copies += 1
                    weight = 1
                    for block in selected_rows + selected_cols:
                        weight *= host.weight(block)
                    weighted_copies += weight
                    if not pinned_anchor(selected_rows[:host.s], selected_cols[:host.s]):
                        first_unpinned = {
                            "rows": selected_rows, "columns": selected_cols,
                            "entries": [[matrix[i][j] for j in chosen] for i in rr],
                        }
                        if not stop_at_unpinned:
                            raise VerificationError(
                                f"Unpinned H{host.s + 2}, h={host.h}, "
                                f"repair={host.repaired}: {first_unpinned}")
                    return
                mask = masks[level]
                if chosen:
                    mask &= full ^ ((1 << (chosen[-1] + 1)) - 1)
                while mask:
                    bit = mask & -mask
                    mask -= bit
                    visit(level + 1, chosen + [bit.bit_length() - 1])
                    if stop_at_unpinned and first_unpinned is not None:
                        return

            visit(0, [])
            if stop_at_unpinned and first_unpinned is not None:
                break
    result = {
        "depth": host.h, "anchor_size": host.s, "pattern_size": k,
        "repaired": host.repaired, "compressed_order": n,
        "inspected_row_tuples": inspected, "viable_row_tuples": viable,
        "compressed_full_copies": copies, "weighted_expanded_copies": weighted_copies,
        "first_unpinned_copy": first_unpinned,
        "exhaustive": first_unpinned is None,
    }
    if not stop_at_unpinned:
        expected_copies = 0 if host.repaired else 2 * host.m ** (2 * host.s + 2)
        require(weighted_copies == expected_copies,
                "Full-pattern exhaustive count disagrees with the exact formula.")
        require(copies == (0 if host.repaired else host.m),
                "Unexpected number of full copies in the compressed host.")
        result["formula_copies"] = expected_copies
    return result


def crown_check(host):
    """Exclude unordered crown triples, including repaired dummy traces."""
    rows = [r for r in host.row_blocks if r[0] != "A"]
    cols = [c for c in host.col_blocks if c[0] != "A"]
    columns = [sum(host.entry(r, c) << j for j, r in enumerate(rows)) for c in cols]
    full = (1 << len(rows)) - 1
    for i, j, k in combinations(range(len(cols)), 3):
        x, y, z = columns[i], columns[j], columns[k]
        require(not ((x & y & ~z & full) and (x & ~y & z & full)
                     and (~x & y & z & full)),
                f"Non-anchor crown at depth {host.h}, repair={host.repaired}.")
    return {"depth": host.h, "repaired": host.repaired,
            "nonanchor_blocks_per_axis": len(rows),
            "column_triples": len(cols) * (len(cols) - 1) * (len(cols) - 2) // 6,
            "crowns": 0}


def class_and_signature_checks(host):
    """Check the structural hypotheses used in the crown-anchor proof."""
    matrix = host.compressed_matrix()
    anchor_rows = [i for i, r in enumerate(host.row_blocks) if r[0] == "A"]
    anchor_cols = [j for j, c in enumerate(host.col_blocks) if c[0] == "A"]
    nonrows = [i for i, r in enumerate(host.row_blocks) if r[0] != "A"]
    noncols = [j for j, c in enumerate(host.col_blocks) if c[0] != "A"]

    def cls(block):
        return block[:2]

    for row in anchor_rows:
        classes = {cls(host.col_blocks[j]) for j in noncols if matrix[row][j]}
        require(len(classes) <= 1, "An anchor row meets two non-anchor classes.")
    for col in anchor_cols:
        classes = {cls(host.row_blocks[i]) for i in nonrows if matrix[i][col]}
        require(len(classes) <= 1, "An anchor column meets two non-anchor classes.")
    for row_axis in (True, False):
        axis = host.row_blocks if row_axis else host.col_blocks
        nonaxis = nonrows if row_axis else noncols
        opposite = noncols if row_axis else nonrows
        anchors = anchor_cols if row_axis else anchor_rows
        groups = {}
        for i in nonaxis:
            groups.setdefault(cls(axis[i]), []).append(i)
        for group in groups.values():
            anchor_traces = set()
            nonanchor_traces = []
            for i in group:
                get = (lambda j: matrix[i][j]) if row_axis else (lambda j: matrix[j][i])
                anchor_traces.add(tuple(get(j) for j in anchors))
                nonanchor_traces.append(sum(get(j) << u for u, j in enumerate(opposite)))
            require(len(anchor_traces) <= 2, "A variable class has three anchor traces.")
            for x, y in combinations(nonanchor_traces, 2):
                require((x & ~y) == 0 or (y & ~x) == 0,
                        "Non-anchor traces in one class are not nested.")
    return {"depth": host.h, "repaired": host.repaired,
            "single_role_class": True, "nested_nonanchor_traces": True,
            "at_most_two_anchor_traces": True}


def body_enumeration(host):
    """Weighted enumeration over mode roles, independent of the leaf formula."""
    nonrows = [r for r in host.row_blocks if r[0] != "A"]
    noncols = [c for c in host.col_blocks if c[0] != "A"]
    totals = []
    for t, mode in enumerate(host.modes):
        rr = [[r for r in nonrows if host.role(r, t, True) == j] for j in (0, 1)]
        cc = [[c for c in noncols if host.role(c, t, False) == j] for j in (0, 1)]
        count = 0
        for r0, r1 in product(*rr):
            if host.row_index[r0] >= host.row_index[r1]:
                continue
            for c0, c1 in product(*cc):
                if host.col_index[c0] >= host.col_index[c1]:
                    continue
                if (host.entry(r0, c0), host.entry(r0, c1),
                        host.entry(r1, c0), host.entry(r1, c1)) == (1, 0, 1, 1):
                    count += (host.weight(r0) * host.weight(r1)
                              * host.weight(c0) * host.weight(c1))
        expected = (host.m ** 2 if not host.repaired and mode[0] == "W"
                    and mode[1] == host.h and mode[2] == "-" else 0)
        require(count == expected, f"Wrong body count in mode {mode}.")
        if count:
            totals.append({"mode": list(mode), "body_copies": count})
    total = sum(x["body_copies"] for x in totals) * host.m ** (2 * host.s)
    expected_total = 0 if host.repaired else 2 * host.m ** (2 * host.s + 2)
    require(total == expected_total, "Exact copy enumeration disagrees with formula.")
    return {"depth": host.h, "repaired": host.repaired, "nonzero_modes": totals,
            "pinned_copies": total, "formula_copies": expected_total,
            "scope": "All copies at arbitrary depth require the written pinning proof."}


def pattern_entry(i, j, s=3):
    if i < s and j < s:
        return int(i != j)
    if i < s:
        return int(i == j - s)
    if j < s:
        return int(j == i - s)
    return int(i == s + 1 or j == s)


def explicit_disjoint_copies(depth, anchor_size=3):
    host = TreeHost(depth, anchor_size)
    rows, cols = host.expanded_axes()
    row_indices = {r: i for i, r in enumerate(rows)}
    col_indices = {c: j for j, c in enumerate(cols)}
    used_rows, used_cols, used_cells = set(), set(), set()
    for p in range(host.m):
        t = host.modes.index(("W", depth, "-", p % 2))
        rr = [(("A", t, u), p) for u in range(host.s)]
        rr += [(("L", depth, p), 0), (host.dummy, p)]
        cc = [(("A", t, u), p) for u in range(host.s)]
        cc += [(("L", depth, p), 0), (("-", depth - 1, p // 2), p % 2)]
        ri, ci = [row_indices[r] for r in rr], [col_indices[c] for c in cc]
        require(ri == sorted(ri) and ci == sorted(ci), "Explicit copy is not ordered.")
        require(not (used_rows & set(ri)) and not (used_cols & set(ci)),
                "The claimed disjoint copies share an axis position.")
        for i, r in enumerate(rr):
            for j, c in enumerate(cc):
                require(host.entry(r[0], c[0]) == pattern_entry(i, j, host.s),
                        "Explicit full-pattern copy has an incorrect entry.")
        cells = set(product(ri, ci))
        require(not (used_cells & cells), "Explicit copies share a matrix cell.")
        used_rows.update(ri)
        used_cols.update(ci)
        used_cells.update(cells)
    repaired = TreeHost(depth, anchor_size, repaired=True)
    changed = sum(host.weight(r) * host.weight(c)
                  for r in host.row_blocks for c in host.col_blocks
                  if host.entry(r, c) != repaired.entry(r, c))
    require(changed == host.m ** 2, "Repair changed the wrong number of entries.")
    return {"depth": depth, "expanded_order": host.dimension,
            "explicit_copies": host.m, "disjoint_rows": len(used_rows),
            "disjoint_columns": len(used_cols), "disjoint_cells": len(used_cells),
            "repair_changed_entries": changed}


def expanded_twin_check(depth, anchor_size=3):
    host = TreeHost(depth, anchor_size)
    rows, cols, matrix = host.expanded_matrix()
    compressed = host.compressed_matrix()
    for i, (r, _) in enumerate(rows):
        require(len(matrix[i]) == host.dimension, "Expanded matrix has wrong width.")
        for j, (c, _) in enumerate(cols):
            require(matrix[i][j] == compressed[host.row_index[r]][host.col_index[c]],
                    "Expanded twins disagree with the compressed matrix.")
    return {"depth": depth, "expanded_order": host.dimension,
            "checked_expanded_entries": host.dimension ** 2, "twins_agree": True}


def bernoulli_formula(m, a, b, s=3):
    beta = 1 - (1 - a) ** m
    alpha = beta ** s * (1 - (1 - b) ** m) ** s
    c = 1 - (1 - b) ** 2
    one_parity = 1 - (1 - c * a * b) ** (m // 2)
    both = 1 - (1 - c * (2 * a * b - a * a * b * b)) ** (m // 2)
    actual = beta * (2 * alpha * (1 - alpha) * one_parity + alpha ** 2 * both)
    return both, actual


def direct_bernoulli(m, a, b, s=3):
    """Enumerate every relevant leaf-row, leaf-column, parent-column outcome.

    Whole-anchor-mode events and the dummy-row event are integrated exactly;
    their groups are disjoint from every enumerated variable position.
    """
    require(m in (2, 4, 8), "Direct enumeration is intentionally small.")
    A, B, C, D = a.numerator, a.denominator, b.numerator, b.denominator
    weights = [0, 0, 0, 0]
    for row_mask in range(1 << m):
        rcount = row_mask.bit_count()
        row_weight = A ** rcount * (B - A) ** (m - rcount)
        for col_mask in range(1 << (2 * m)):
            ccount = col_mask.bit_count()
            weight = row_weight * C ** ccount * (D - C) ** (2 * m - ccount)
            parity = 0
            for p in range(m):
                parent_start = m + 2 * (p // 2)
                if ((row_mask >> p) & 1 and (col_mask >> p) & 1
                        and ((col_mask >> parent_start) & 3)):
                    parity |= 1 << (p % 2)
            weights[parity] += weight
    denominator = B ** m * D ** (2 * m)
    require(sum(weights) == denominator, "Bernoulli outcome weights do not sum to one.")
    critical = Fraction(sum(weights[1:]), denominator)
    beta = 1 - (1 - a) ** m
    alpha = beta ** s * (1 - (1 - b) ** m) ** s
    actual = beta * (Fraction(weights[1] + weights[2], denominator) * alpha
                     + Fraction(weights[3], denominator) * (2 * alpha - alpha ** 2))
    return critical, actual


def bernoulli_checks(anchor_size=3):
    results = []
    for m, (a, b) in product((2, 4), ((Fraction(1, 2), Fraction(1, 2)),
                                     (Fraction(1, 3), Fraction(2, 5)),
                                     (Fraction(2, 3), Fraction(1, 4)))):
        exact = bernoulli_formula(m, a, b, anchor_size)
        direct = direct_bernoulli(m, a, b, anchor_size)
        require(exact == direct, "Bernoulli formula disagrees with direct enumeration.")
        results.append({"m": m, "row_probability": fraction_record(a),
                        "column_probability": fraction_record(b),
                        "enumerated_outcomes": 1 << (3 * m),
                        "critical_probability": fraction_record(exact[0]),
                        "actual_detection_probability": fraction_record(exact[1])})
    return results


def falling_integer(value, order):
    result = 1
    for offset in range(order):
        result *= value - offset
    return result


def fixed_size_factorial_formula(m, n, q, r):
    """The article's exact formula for the r-th witness factorial moment."""
    def rho(j):
        return (Fraction(falling_integer(q, j), falling_integer(n, j))
                if j <= q else Fraction(0))

    total = Fraction(0)
    for j in range((r + 1) // 2, r + 1):
        if j > m // 2 or r - j > j:
            continue
        coefficient = (factorial(r) * comb(m // 2, j) * comb(j, r - j)
                       * 2 ** (2 * j - r))
        inner = sum(((-1) ** a * comb(j, a) * 2 ** (j - a) * rho(r + j + a)
                     for a in range(j + 1)), Fraction(0))
        total += coefficient * inner
    return rho(r) * total


def fixed_size_factorial_checks():
    """Independently enumerate every fixed-size sample of small witness models.

    Row positions 0..m-1 are leaf rows. Column positions 0..m-1 are
    matching leaf columns, and positions m..2m-1 are the disjoint parent
    pairs. Other positions are arbitrary filler. This checks the exact
    witness distribution, not full-host detection or anchor coverage.
    """
    results = []
    for m, n in ((2, 6), (4, 10)):
        by_sample_size = []
        for q in range(n + 1):
            subsets = [sum(1 << p for p in positions)
                       for positions in combinations(range(n), q)]
            totals = [0] * (m + 1)
            for rows in subsets:
                for cols in subsets:
                    x = sum(bool((rows >> p) & 1 and (cols >> p) & 1
                                 and (cols >> (m + 2 * (p // 2))) & 3)
                            for p in range(m))
                    falling = 1
                    for r in range(1, m + 1):
                        falling *= x - r + 1
                        totals[r] += falling
            sample_pairs = comb(n, q) ** 2
            moments = []
            for r in range(1, m + 1):
                actual = Fraction(totals[r], sample_pairs)
                expected = fixed_size_factorial_formula(m, n, q, r)
                require(actual == expected,
                        f"Fixed-size factorial moment mismatch: m={m}, n={n}, "
                        f"q={q}, r={r}, direct={actual}, formula={expected}.")
                moments.append({"order": r, "exact_moment": fraction_record(actual)})
            by_sample_size.append({"q": q, "sample_pairs": sample_pairs,
                                   "factorial_moments": moments})
        results.append({"m": m, "ambient_positions_per_axis": n,
                        "scope": "Exact witness submodel with filler positions; no anchors.",
                        "checked_moment_identities": m * (n + 1),
                        "sample_sizes": by_sample_size})
    return results


def three_anchor_counterexample():
    results = []
    for repaired in (False, True):
        host = TreeHost(2, anchor_size=3, repaired=repaired)
        v = host.modes.index(("V", 2, "+", None))
        w = host.modes.index(("W", 2, "+", 1))
        rows = [("A", w, 1), ("L", 2, 0), ("L", 2, 3)]
        cols = [("A", v, 0), ("A", w, 0), ("L", 2, 1)]
        require([host.row_index[x] for x in rows]
                == sorted(host.row_index[x] for x in rows), "C3 witness row order failed.")
        require([host.col_index[x] for x in cols]
                == sorted(host.col_index[x] for x in cols), "C3 witness column order failed.")
        entries = [[host.entry(r, c) for c in cols] for r in rows]
        require(entries == [[0, 1, 1], [1, 0, 1], [1, 1, 0]],
                "The smaller-anchor counterexample is incorrect.")
        require(not pinned_anchor(rows, cols), "The counterexample is actually pinned.")
        results.append({"depth": 2, "repaired": repaired, "rows": rows,
                        "columns": cols, "entries": entries})
    return results


def smaller_full_pattern_checks():
    """H4 fails full-pattern pinning and survives the proposed repair."""
    results = []
    for h in (1, 2, 3):
        for repaired in (False, True):
            result = exhaustive_full_pattern_check(
                TreeHost(h, anchor_size=2, repaired=repaired), stop_at_unpinned=True)
            require((result["first_unpinned_copy"] is None) == (h == 1),
                    "The recorded H4 boundary changed.")
            result["scope"] = ("No unpinned H4 at depth one only." if h == 1 else
                               "Explicit counterexample; search stops at its first witness.")
            results.append(result)
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--anchor-s", type=int, choices=(3, 4), default=3,
                        help="anchor size; the main result uses s=3 and a 5-by-5 pattern")
    parser.add_argument("--legacy-c4", action="store_true",
                        help="also check the stronger standalone C4 anchor lemma")
    parser.add_argument("--extended", action="store_true",
                        help="also enumerate full-pattern pinning at depth 3 and crowns at depth 7")
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("verification_results.json"))
    args = parser.parse_args()
    started = time.monotonic()
    s = args.anchor_s
    full_pattern_depths = range(1, 4 if args.extended else 3)
    structural_depths = range(1, 8 if args.extended else 7)
    result = {
        "schema": "ordered-binary-matrix-research-verification-v2",
        "status": "PASS",
        "arithmetic": "Exact integers and fractions; standard Python library only.",
        "formal_status": "Not a Lean formalization; finite checks supplement written proofs.",
        "anchor_size": s,
        "pattern_size": s + 2,
        "pattern": [[pattern_entry(i, j, s) for j in range(s + 2)] for i in range(s + 2)],
        "full_pattern_pinning": [exhaustive_full_pattern_check(TreeHost(h, s, repaired=r))
                                 for h in full_pattern_depths for r in (False, True)],
        "nonanchor_crowns": [crown_check(TreeHost(h, s, repaired=r))
                             for h in structural_depths for r in (False, True)],
        "structural_hypotheses": [class_and_signature_checks(TreeHost(h, s, repaired=r))
                                  for h in structural_depths for r in (False, True)],
        "body_copy_counts": [body_enumeration(TreeHost(h, s, repaired=r))
                             for h in range(1, 7) for r in (False, True)],
        "expanded_disjoint_copies": [explicit_disjoint_copies(h, s) for h in range(1, 5)],
        "expanded_twins": [expanded_twin_check(h, s) for h in (1, 2)],
        "bernoulli_sampling": bernoulli_checks(s),
        "fixed_size_factorial_moments": fixed_size_factorial_checks(),
        "three_anchor_counterexample": three_anchor_counterexample(),
        "four_by_four_counterexamples": smaller_full_pattern_checks(),
        "extended": args.extended,
    }
    if args.legacy_c4:
        result["legacy_c4_anchor_pinning"] = [
            exhaustive_anchor_check(TreeHost(h, 4, repaired=r))
            for h in (1, 2) for r in (False, True)]
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n",
                           encoding="utf-8")
    print(f"PASS: exact finite checks completed in {time.monotonic() - started:.2f}s")
    print(args.output.resolve())


if __name__ == "__main__":
    main()
