#!/usr/bin/env python3
"""Check and optionally regenerate the finite-field resource certificates.

This is an unbounded-register abstract interpretation of the pinned RM source.
It is not a proof that every represented abstract point is concretely reachable.
The existing natural-category invariant (0, 1, >=2) is checked first. Positive
decrements are not restricted to nonzero residues: a positive multiple of p
must remain possible. Regeneration starts at the exact dispatched root and
uses only affine hull, affine intersection, translation, and that product
invariant. Thus it also checks the least fixed point of the stated analysis.
"""
from collections import Counter, deque
from pathlib import Path
import argparse
import hashlib
import json
import time
import zlib

from affine_domain import Domain
from source_graph import PIN, source_graph, check_product

HERE = Path(__file__).resolve().parent
REGISTERS = [3, 0, 0, 0, 3, 0, 0, 0, 0]
EXCLUDED = [8202, 8203, 8204, 8358, 8359, 8360]
MODES = {"registers": "invariant", "header": "resource-invariant",
         "gap": "gap-invariant"}


def strip_zero(pc, count):
    while count:
        i = pc.rfind("0")
        if i < 0:
            return ""
        pc = pc[:i]
        count -= 1
    return pc


def carry_overflow(pc, op, register, zero):
    if op == "CI" or (op == "CD" and not zero):
        before = pc
    elif op == "CD":
        before = strip_zero(pc, 1)
    elif op == "CB":
        before = strip_zero(pc, register)
    else:
        return False
    return "0" not in before


def initial_point(p, mode):
    extra = [] if mode == "registers" else [176 if mode == "header" else 181, 167]
    return tuple(x % p for x in [1, *REGISTERS, *extra])


def effect(domain, B, case, mask, mode):
    _, pc, op, register, zero, _ = case
    B = domain.step(B, op, register, zero, mask)
    if not B or mode == "registers":
        return B
    delta_first = int(op == "CD" and not zero)
    if mode == "gap":
        delta_first += int(carry_overflow(pc, op, register, zero))
    delta_spares = int(op == "CI")
    if not (delta_first or delta_spares):
        return B
    rows = []
    for row in B:
        v = list(row)
        v[10] = (v[10] + delta_first * v[0]) % domain.p
        v[11] = (v[11] + delta_spares * v[0]) % domain.p
        rows.append(v)
    return domain.normalize_affine(rows)


def regenerate(p, mode, sites, cases, masks):
    d = Domain(p)
    spaces = [()] * len(sites)
    spaces[0] = (initial_point(p, mode),)
    outgoing = [[] for _ in sites]
    for case in cases:
        outgoing[case[0]].append(case)
    todo, queued = deque([0]), {0}
    while todo:
        i = todo.popleft()
        queued.remove(i)
        for case in outgoing[i]:
            j = case[5]
            if j is None:
                continue
            B = d.reduce(effect(d, spaces[i], case, masks[i], mode), masks[j])
            merged = d.join(spaces[j], B)
            if merged != spaces[j]:
                spaces[j] = merged
                if j not in queued:
                    todo.append(j)
                    queued.add(j)
    return spaces


def read_spaces(p, mode):
    filename = f"{MODES[mode]}-f{p}.json.zlib"
    raw = zlib.decompress((HERE / "certificates" / filename).read_bytes())
    data = json.loads(raw)
    assert data["prime"] == p
    spaces = [tuple(map(tuple, B)) for B in data["spaces"]]
    return spaces, hashlib.sha256(raw).hexdigest()


def check_one(p, mode, spaces, sites, cases, masks):
    d = Domain(p)
    width = 10 if mode == "registers" else 12
    assert len(spaces) == len(sites) == 6460
    for B in spaces:
        assert all(len(r) == width and all(0 <= x < p for x in r) for r in B)
        assert d.normalize_affine(B) == B
    assert d.included((initial_point(p, mode),), spaces[0])
    rejected, edges = [], 0
    for ci, case in enumerate(cases):
        i, _, _, _, _, j = case
        B = effect(d, spaces[i], case, masks[i], mode)
        if not B:
            rejected.append(ci)
        elif j is not None:
            assert d.included(d.reduce(B, masks[j]), spaces[j]), (p, mode, ci)
            edges += 1
    assert rejected == EXCLUDED
    assert sum(bool(B) for B in spaces) == 6456
    return {"reachable_abstract_sites": 6456, "checked_nonhalting_edges": edges,
            "excluded_case_indices": rejected}


def check_fibers(p, base, header, gap):
    d = Domain(p)
    header_dims, gap_dims = Counter(), Counter()
    conservation = [-15, *([1] * 9), 1, -1]
    for i, A in enumerate(base):
        for B, counts in [(header[i], header_dims), (gap[i], gap_dims)]:
            assert d.normalize_affine([r[:10] for r in B]) == A, (p, i)
            if B:
                counts[len(B) - len(A)] += 1
        assert all(sum(x * y for x, y in zip(r, conservation)) % p == 0
                   for r in header[i]), (p, i, "conservation")
    assert header_dims == {1: 6456}
    assert gap_dims == {2: 6456}
    return {
        "header_projection_exact": True,
        "header_fiber_dimension_histogram": dict(header_dims),
        "header_fiber_equation": "H + sum(registers) - K = 15 modulo p",
        "gap_projection_exact": True,
        "gap_fiber_dimension_histogram": dict(gap_dims),
        "gap_fiber_equation": "E_i = A_i x F_p^2 at every nonempty abstract site",
    }


def verify(recompute=False):
    began = time.monotonic()
    sites, cases = source_graph()
    product = check_product(cases)
    masks = json.loads((HERE / "reference/product-invariant.json").read_text())["masks"]
    overflow = [i for i, case in enumerate(cases)
                if carry_overflow(case[1], case[2], case[3], case[4])]
    assert overflow == [8267, 8356, 8387]
    results = []
    for p in [2, 3, 5, 7]:
        spaces, reports = {}, {}
        for mode in MODES:
            B, sha = read_spaces(p, mode)
            report = check_one(p, mode, B, sites, cases, masks)
            if recompute:
                assert regenerate(p, mode, sites, cases, masks) == B, (p, mode, "least closure")
            report["raw_certificate_sha256"] = sha
            spaces[mode], reports[mode] = B, report
        results.append({"prime": p, "modes": reports,
                        "fibers": check_fibers(p, spaces["registers"], spaces["header"], spaces["gap"])})
    return {"status": "PASS", "source_sha256": PIN, "source_nodes": 6459,
            "instruction_sites": 6460, "guarded_cases": 8391,
            "checked_product_invariant": product, "carry_overflow_case_indices": overflow,
            "least_affine_closures_regenerated": recompute, "results": results,
            "seconds": time.monotonic() - began,
            "scope": "Finite-field affine analysis; no assertion of concrete reachability of all abstract points."}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--recompute", action="store_true")
    parser.add_argument("--write-report", type=Path)
    args = parser.parse_args()
    if not __debug__:
        parser.error("Assertions are required; do not run with -O.")
    report = verify(args.recompute)
    text = json.dumps(report, indent=2) + "\n"
    if args.write_report:
        args.write_report.write_text(text)
    print(text, end="")
