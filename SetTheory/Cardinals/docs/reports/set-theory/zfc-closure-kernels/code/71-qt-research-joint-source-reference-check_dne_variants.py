#!/usr/bin/env python3
"""Reproduce and independently check the 64 fixed-bundle DNE variants.

Only the Python standard library is required.  This is an exact symbolic
emission checker, not a Turing-machine simulation or a replacement for the
ordinary proof in dne_calculus_transfer.md.  The original formula functions
are read, without importing their numeric runtime, from the attributed pinned
upstream spec.py included in snapshot/.  Formula constructors remain symbolic:
the resulting identities therefore quantify over all numerical parameters.

Run from any directory: python check_dne_variants.py
"""
from __future__ import annotations

import ast
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
SPEC = HERE / "snapshot/ZF/m254/tools/logic/spec.py"
SPEC_SHA = "7d96deff6994315b714579c74d10efeb65374694d476c802c727356e258578e9"
ORIGINAL_FINE_SHA = "4a331a23cc127322bbfc1421895ddee1c60568f9ed210ceb1fa499054548eea3"
ALL_DNE_FINE_SHA = "abc36ee4e512c424e23be967a907068421e2629782627a5caa83c5fe1375835f"
TAIL = [192, 131, 211, 197, 131]


def imp(x, y):
    return ("imp", x, y)


def neg(x):
    return imp(x, 1)


def conjunction(x, y):
    return neg(imp(x, neg(y)))


def existential(i, x):
    return neg(("all", i, neg(x)))


def load_spec():
    data = SPEC.read_bytes()
    assert hashlib.sha256(data).hexdigest() == SPEC_SHA
    tree = ast.parse(data)
    definitions = [n for n in tree.body if isinstance(n, ast.FunctionDef)
                   and n.name not in ("_code", "enum_step")]
    namespace = {"F": 1, "_code": lambda tag, x, y:
                 (("imp", "rel", "all", "eq")[tag], x, y)}
    exec(compile(ast.Module(body=definitions, type_ignores=[]), str(SPEC), "exec"), namespace)
    return namespace


def is_neg(t):
    return isinstance(t, tuple) and t[0] == "imp" and t[2] == 1


def redexes(t, address=()):
    if not isinstance(t, tuple):
        return []
    here = [address] if is_neg(t) and is_neg(t[1]) else []
    # Rel/Eq have numerical labels as arguments, not formula positions.
    if t[0] in ("rel", "eq"):
        return here
    if t[0] == "all":
        return here + redexes(t[2], address + (2,))
    assert t[0] == "imp"
    return here + redexes(t[1], address + (1,)) + redexes(t[2], address + (2,))


def normalize(t, selected, address=()):
    if not isinstance(t, tuple):
        return t
    if address in selected:
        assert is_neg(t) and is_neg(t[1])
        return normalize(t[1][1], selected, address + (1, 1))
    if t[0] in ("rel", "eq"):
        return t
    if t[0] == "all":
        return ("all", t[1], normalize(t[2], selected, address + (2,)))
    return ("imp", normalize(t[1], selected, address + (1,)),
            normalize(t[2], selected, address + (2,)))


def emit(t):
    """Emit the unchanged original Wade RPN macros, recognizing And and Ex."""
    if not isinstance(t, tuple):
        return {"a": [166], "b": [121], "c": [168], "u": [171, 158, 208],
                0: [171], 1: [177]}[t]
    if is_neg(t):
        inside = t[1]
        if (isinstance(inside, tuple) and inside[0] in ("imp", "all")
                and is_neg(inside[2])):
            return emit(inside[1]) + emit(inside[2][1]) + [178 if inside[0] == "imp" else 183]
        return emit(inside) + [218]
    return emit(t[1]) + emit(t[2]) + [{"imp": 119, "rel": 181, "all": 180, "eq": 182}[t[0]]]


def execute_macros(word):
    """An independent stack evaluator: bottom-to-top list, symbolic tail."""
    stack = ["old_top"]
    parameter_b = "old_cache"
    scratch_u = None
    input_events = []
    constructor = {
        119: imp, 181: lambda x, y: ("rel", x, y),
        180: lambda x, y: ("all", x, y), 182: lambda x, y: ("eq", x, y),
        178: conjunction, 183: existential,
    }
    for pc, macro in enumerate(word):
        if macro in (166, 121, 168, 171, 177):
            stack.append({166: "a", 121: parameter_b, 168: "c", 171: 0, 177: 1}[macro])
        elif macro in constructor:
            assert len(stack) >= 3, (pc, "protected old top would be consumed")
            right = stack.pop()
            left = stack.pop()
            stack.append(constructor[macro](left, right))
        elif macro == 218:
            assert len(stack) >= 2
            stack[-1] = neg(stack[-1])
        elif macro == 176:
            assert parameter_b == "old_cache"
            parameter_b = "b"
            input_events.append((macro, len(stack)))
        elif macro == 158:
            assert scratch_u is None
            scratch_u = "u"
            input_events.append((macro, len(stack)))
        elif macro == 208:
            assert scratch_u == "u" and stack[-1] == 0
            stack[-1] = scratch_u
            scratch_u = None
        else:
            raise AssertionError((pc, macro))
    assert scratch_u is None
    return stack, input_events


def freeze(t):
    return tuple(freeze(x) for x in t) if isinstance(t, list) else t


def nodes(t):
    return 1 + nodes(t[1]) + nodes(t[2]) if isinstance(t, tuple) else 1


def main():
    spec = load_spec()
    original = spec["bundle"]("a", "b", "c")
    rows = spec["ax_rows"]("a", "old_cache", "b", "c", "u")
    paths = redexes(original)
    assert len(paths) == 6
    archived = json.loads((HERE / "original_layout_dne_variants.json").read_text())
    assert paths == [tuple(p) for p in archived["redex_paths"]]
    fine = json.loads((HERE / "macro_to_fine.json").read_text())
    prefix = [166, 121, 180, 176] + [m for t in rows[1:] for m in emit(t)]
    result = []
    for mask in range(64):
        bundle = normalize(original, {p for bit, p in enumerate(paths) if mask & (1 << bit)})
        word = prefix + emit(bundle) + TAIL
        stack, events = execute_macros(word[:-len(TAIL)])
        assert stack == ["old_top"] + rows + [bundle]
        assert events == [(176, 2), (158, 4)], events
        assert word[:len(prefix)] == archived["variants"][0]["word"][:len(prefix)]
        assert bundle[0] == "imp"  # Consequently its numeric value is never F=1.
        fine_word = "".join(fine[str(m)] for m in word)
        row = archived["variants"][mask]
        assert row["mask"] == mask
        assert row["word"] == word
        assert freeze(row["bundle"]) == bundle
        assert row["fine_AX"] == fine_word
        assert row["fine_length"] == len(fine_word) == 1270 - 18 * mask.bit_count()
        assert row["formula_tree_nodes"] == nodes(bundle) == 145 - 4 * mask.bit_count()
        assert row["macro_length"] == len(word)
        result.append({"mask": mask, "redex_count": mask.bit_count(),
                       "fine_length": len(fine_word), "macro_length": len(word),
                       "formula_tree_nodes": nodes(bundle),
                       "fine_sha256": hashlib.sha256(fine_word.encode()).hexdigest()})
    assert result[0]["fine_sha256"] == ORIGINAL_FINE_SHA
    assert result[63]["fine_sha256"] == ALL_DNE_FINE_SHA
    report = {
        "status": "PASS", "checked_masks": 64, "logical_rows_unchanged": 8,
        "gen_prefix_unchanged": True, "read_events_unchanged": True,
        "protected_stack_tail_preserved": True, "bundle_root_imp_for_every_mask": True,
        "cleanup_and_gate_macros_unchanged": True,
        "upstream_spec_sha256": SPEC_SHA, "results": result,
        "scope": "Exact universal symbolic source-emission check; neither a Lean build nor a binary-machine proof.",
    }
    (HERE / "dne_variant_checks.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "results"}, indent=2))


if __name__ == "__main__":
    main()
