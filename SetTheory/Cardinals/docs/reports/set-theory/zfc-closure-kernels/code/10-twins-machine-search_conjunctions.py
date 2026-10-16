"""Bounded search of propositional conjunction commutations in the 252 route.

All sources are read from the pinned partial snapshot under repo/. No GitHub
write, source modification, or state-count calibration theorem is performed.
And_F(A,B)=((A -> (B -> F)) -> F) is symmetric for both Boolean values of F.
Swaps preserve binders, variable labels, matrix insertion, and all gate calls.
"""
from __future__ import annotations

import hashlib
import importlib
import itertools
import json
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parent
RESEARCH = ROOT / "repo/Computability/BusyBeaver/Research/ZFC"
sys.path.insert(0, str(RESEARCH))
sys.path.insert(0, str(ROOT / "backend_output"))
import theory_backend_experiment as t
from recover_wade_dag import builder_from_dag, git_bytes, parse_dag


def and_parts(f):
    if isinstance(f, tuple) and f[0] == "imp" and f[2] == 1:
        x = f[1]
        if (isinstance(x, tuple) and x[0] == "imp"
                and isinstance(x[2], tuple) and x[2][0] == "imp"
                and x[2][2] == 1):
            return x[1], x[2][1]
    return None


def variants(f):
    """Exactly the recursive And commutations, with locations recorded."""
    parts = and_parts(f)
    if parts is not None:
        out = []
        for (a, sa), (b, sb) in itertools.product(variants(parts[0]), variants(parts[1])):
            out.append((t.And(a, b), {"swap": False, "left": sa, "right": sb}))
            out.append((t.And(b, a), {"swap": True, "left": sa, "right": sb}))
        return out
    if isinstance(f, tuple):
        return [(tuple([f[0], a, b]), {"node": f[0], "left": sa, "right": sb})
                for (a, sa), (b, sb) in itertools.product(variants(f[1]), variants(f[2]))]
    return [(f, None)]


def main():
    start = time.monotonic()
    backend = importlib.import_module("TMBuilder")
    nodes, names = parse_dag(git_bytes(None, "ZF/m254/coq/prog/Dag254.v").decode())
    spec, digest = t.published_spec()
    logical = spec["ax_rows"]("a", "h", "b", "c", "u")
    logical[3] = t.Imp("b", t.All("a", t.Ex("a", "b")))
    C = variants(spec["bundle_C"]("a", "b", "c"))
    G = variants(spec["bundle_G"]("a", "b", "c"))
    V = t.Imp(t.Rel("a", "b"), t.All("c", t.Rel("a", "b")))
    assert len(C) == 8 and len(G) == 4
    bool_cases = 0
    for f, a, b in itertools.product((False, True), repeat=3):
        imp = lambda x, y: not x or y
        both = lambda x, y: imp(imp(x, imp(y, f)), f)
        assert both(a,b) == both(b,a)
        bool_cases += 1
    distribution = {}
    minimum = 1000
    winners = []
    cases = 0
    for ci, (c, cswaps) in enumerate(C):
        for gi, (g, gswaps) in enumerate(G):
            for order in itertools.permutations((1, 3, 5, 7)):
                prefix = [166, 121, 180, 176]
                for index in order:
                    prefix += t.emit(logical[index])
                for components in itertools.permutations(("C", "G", "V")):
                    for grouping in (0, 1):
                        x, y, z = [{"C": c, "G": g, "V": V}[n] for n in components]
                        bundle = t.And(t.And(x, y), z) if grouping == 0 else t.And(x, t.And(y, z))
                        program = prefix + t.emit(bundle) + t.TAIL
                        actual, _ = t.symbolic(program)
                        expected = ["old_top"] + [logical[i] for i in (0, *order)] + [bundle]
                        assert actual == expected
                        builder = builder_from_dag(backend, nodes, names)
                        builder.sequence_lookup = {s.seq: i for i, s in enumerate(builder.sequences)}
                        t.lower_program(builder, nodes, program, "and_commute_search", shared=True, base3=True)
                        builder.generate()
                        builder.tm.gc()
                        states = {q for q, _ in builder.tm.states}
                        count = len(states)
                        distribution[count] = distribution.get(count, 0) + 1
                        cases += 1
                        descriptor = {"C_variant": ci, "G_variant": gi,
                            "logical_rows": [9-i for i in order], "components": list(components),
                            "right_associated": bool(grouping)}
                        if count < minimum:
                            minimum, winners = count, [descriptor]
                            print(json.dumps({"cases": cases, "new_minimum": minimum,
                                "recipe": descriptor}), flush=True)
                            if count < 252:
                                dest = ROOT / f"conjunction-candidate-{count}.named.tm"
                                builder.tm.save(str(dest))
                                source = {"recipe": descriptor, "C_AST": c, "G_AST": g,
                                    "C_commutations": cswaps, "G_commutations": gswaps,
                                    "macro_program": program,
                                    "named_source_sha256": hashlib.sha256(dest.read_bytes()).hexdigest()}
                                (ROOT/f"conjunction-candidate-{count}-recipe.json").write_text(json.dumps(source, indent=2)+"\n")
                        elif count == minimum:
                            winners.append(descriptor)
    summary = {"pinned_ProveIt_commit": "17d0f2eaa650901cda59764dfcc4661c199e49c8",
        "source_spec_sha256": digest, "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "search_cases": cases, "C_variants": len(C), "G_variants": len(G),
        "outer_order_grouping_choices": 288, "minimum_working_states": minimum,
        "cost_distribution": distribution, "minimizers": winners,
        "relative_falsity_conjunction_commutativity_boolean_cases": bool_cases,
        "symbolic_macro_roundtrips_checked": cases,
        "compiler_expansion_invariants_checked": cases,
        "calibrated_ZFC_machine_claimed": False,
        "elapsed_seconds": time.monotonic()-start}
    (ROOT/"conjunction-search-results.json").write_text(json.dumps(summary, indent=2)+"\n")
    print(json.dumps({k:v for k,v in summary.items() if k!="minimizers"}, indent=2))
    print("minimizers", len(winners))


if __name__ == "__main__":
    main()
