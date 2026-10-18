#!/usr/bin/env python3
"""Emit sound candidate fusions of equality-congruence logical roots.

Uses the unchanged symbolic emitter and fine macro dictionary from the
attributed incoming source-search report.  The eight-row basis is replaced
by seven or six rows, while rho8 and rho6 remain individually available.
No binary-machine or bootstrap correctness claim is made by this emitter.
"""
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
BASE = ROOT / "formalism_reference"
spec = importlib.util.spec_from_file_location("fusion_emitter", BASE / "emitter.py")
d = importlib.util.module_from_spec(spec)
spec.loader.exec_module(d)


def conjunctions(items):
    if len(items) == 2:
        return [d.conjunction(*items)]
    assert len(items) == 3
    a, b, c = items
    return [d.conjunction(d.conjunction(a, b), c),
            d.conjunction(a, d.conjunction(b, c))]


def rewrite_labels(formula, mapping):
    if not isinstance(formula, tuple):
        return mapping.get(formula, formula)
    return (formula[0], rewrite_labels(formula[1], mapping),
            rewrite_labels(formula[2], mapping))


def main():
    specs = d.load_spec()
    old = specs["ax_rows"]("a", "old_cache", "b", "c", "u")
    original_bundle = specs["bundle"]("a", "b", "c")
    redexes = d.redexes(original_bundle)
    fine = json.loads((BASE / "macro_to_fine.json").read_text())
    # Original ax_rows list is GEN, rho8, rho7, rho6, rho5, rho4, rho3,
    # rho2, rho1.  Each of these conclusions uses common antecedent a=b.
    E = lambda a, b: ("eq", a, b)
    R = lambda a, b: ("rel", a, b)
    consequences = {
        2: d.imp(E("a", "c"), E("b", "c")),
        4: d.imp(R("a", "c"), R("b", "c")),
        6: d.imp(R("c", "a"), R("c", "b")),
    }
    results = []
    hashes = set()
    counts = {}
    for selected in [(2, 4), (2, 6), (4, 6), (2, 4, 6)]:
        other = [old[i] for i in range(1, len(old)) if i not in selected]
        for ordering in itertools.permutations(selected):
            for assoc, conjunct in enumerate(conjunctions([consequences[i] for i in ordering])):
                fused_base = d.imp(E("a", "b"), conjunct)
                for labels in itertools.permutations("abc"):
                    mapping = dict(zip("abc", labels))
                    fused = rewrite_labels(fused_base, mapping)
                    for position in range(len(other) + 1):
                        roots = other[:position] + [fused] + other[position:]
                        rows = [old[0]] + roots
                        for mask in (0, 32):
                            bundle = d.normalize(original_bundle,
                                {p for bit, p in enumerate(redexes) if mask & (1 << bit)})
                            word = [166, 121, 180, 176]
                            word += [m for formula in roots for m in d.emit(formula)]
                            word += d.emit(bundle) + d.TAIL
                            stack, events = d.execute_macros(word[:-len(d.TAIL)])
                            assert stack == ["old_top"] + rows + [bundle]
                            assert len(events) == 2 and events[0] == (176, 2)
                            assert events[1][0] == 158
                            assert word.count(158) == 1
                            text = "".join(fine[str(m)] for m in word)
                            sha = hashlib.sha256(text.encode()).hexdigest()
                            assert sha not in hashes
                            hashes.add(sha)
                            index = len(results)
                            result = {
                                "id": index,
                                "fused_original_row_indices": list(selected),
                                "consequence_order": list(ordering),
                                "association": assoc,
                                "label_images": labels,
                                "fused_position_after_GEN": position,
                                "DNE_mask": mask,
                                "logical_rows": len(roots),
                                "AX_stack_pushes": len(roots) + 2,
                                "rows": rows,
                                "bundle": bundle,
                                "word": word,
                                "fine_AX": text,
                                "fine_length": len(text),
                                "fine_sha256": sha,
                            }
                            results.append(result)
                            counts.setdefault(str(selected), []).append(len(text))
    output = ROOT / "formalism_fusions.json"
    output.write_text(json.dumps({
        "scope": "Exact symbolic axiom-root fusions; no binary compilation claim.",
        "variants": results,
    }, separators=(",", ":")) + "\n")
    summary = {
        "status": "PASS", "variants": len(results),
        "unique_fine_words": len(hashes),
        "families": {k: {"count": len(v), "min_fine_length": min(v),
                         "max_fine_length": max(v)} for k, v in counts.items()},
        "source_spec_sha256": d.SPEC_SHA,
        "symbolic_stack_preservation": True,
        "single_fourth_parameter_read": True,
        "core_rho8_rho6_unchanged": True,
        "cleanup_and_bundle_gate_unchanged": True,
        "output": output.name,
    }
    (ROOT / "formalism_fusions_summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
