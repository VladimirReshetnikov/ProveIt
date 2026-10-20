#!/usr/bin/env python3
"""Swap the two object-parameter roles in emitted axioms, preserving GEN.

The parameter-reading header and generalized cache are kept.  Everything
after those two operations uses the opposite object-parameter registers.
Thus AX(a,h,b,c,u,t,w) still emits GEN(a,h), followed by the eight rows with
a and b swapped and the gated bundle B(b,a,c).  It clears both parameters
as before.  This is an axiom-family reindexing, not instruction equivalence.
"""
import json
from functools import cache
import explore_source as e
from verify_full_dn_semantics import sealed_fingerprint

b = e.b
SCOPE = "11101001001"
EXCLUDED = ("111010010010", "111010010011000", "1110100100111011111")


def swap(node, path=""):
    if path in EXCLUDED:
        return node
    if b.is_leaf(node):
        op, arg = node
        if path.startswith(SCOPE) and op in ("CI", "CD") and arg in (4, 5):
            return op, 9 - arg
        return node
    return tuple(swap(node[i], path + str(i)) for i in (0, 1))


def main():
    out = e.OUTPUT_ROOT / "axiom_parameter_permutations"
    out.mkdir(parents=True, exist_ok=True)
    for label, source in [
        ("original", e.BASELINE_SOURCE),
        ("dn4", e.DN4_SOURCE),
    ]:
        root = b.tree(json.loads(source.read_text()))
        new = swap(root)
        b.graph(b.sites(new))
        stats = b.metrics(new)
        (out / f"sites_{label}_ba.json").write_bytes(b.json_bytes(b.sites(new), compact=True))
        (out / f"recipe_{label}_ba.json").write_bytes(b.json_bytes({
            "scope_path": SCOPE,
            "excluded_paths": EXCLUDED,
            "register_permutation": {4: 5, 5: 4},
            "semantics": "Same GEN(a,h); then rho_i(b,a,c[,u]) and B(b,a,c); all other command effects unchanged.",
            "source_metrics": stats,
        }))
        print(label, stats)
        old_nodes = set()
        def collect(n):
            if n in old_nodes:
                return
            old_nodes.add(n)
            if not b.is_leaf(n):
                collect(n[0]); collect(n[1])
        collect(root)
        available = {}
        for n in old_nodes:
            if b.boundary(n) == (0, 0, False):
                fingerprint = sealed_fingerprint(b, n)
                available.setdefault(fingerprint, []).append(n)
        canonicalizations = []
        @cache
        def canon(n):
            if n in old_nodes:
                return n
            if b.boundary(n) == (0, 0, False):
                matches = available.get(sealed_fingerprint(b, n), [])
                if matches:
                    best = min(matches, key=lambda t: (len(b.sites(t)), b.metrics(t)["maximum_depth"]))
                    canonicalizations.append({"old": b.metrics(n), "new": b.metrics(best)})
                    return best
            return n if b.is_leaf(n) else tuple(map(canon, n))
        canonical = canon(new)
        print(label, "canonical", b.metrics(canonical), "reused", len(canonicalizations))
        (out / f"sites_{label}_ba_canonical.json").write_bytes(b.json_bytes(b.sites(canonical), compact=True))
        (out / f"canonicalizations_{label}.json").write_bytes(b.json_bytes(canonicalizations))


if __name__ == "__main__":
    main()
