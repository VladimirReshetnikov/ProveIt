#!/usr/bin/env python3
"""Generate proved equality/membership orientation source experiments.

The output is a source word, not a calibrated binary machine.  The exact
logical-prefix macro words are inherited from the source-verified audit.
Explicit membership atoms in C/G may be reversed.  The equality anchor
basis may be globally reversed; the congruence premises may independently
be reversed using symmetry derived from the anchors.  Two harmless
schema-family symmetries are also enumerated.  The matrix-code placeholder
remains opaque, so the literal decoder needs no recursive transformation.
"""
from __future__ import annotations

import argparse
from collections import Counter
from functools import cache
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import random
import sys

ROOT = Path(__file__).resolve().parents[1]
REFERENCE = Path(__file__).resolve().parent / "reference"
PACKET = REFERENCE
SYMMETRY = REFERENCE


def load_module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def converse(form):
    """Relation converse on formulas/templates; scalar placeholders fixed."""
    if not isinstance(form, tuple):
        return form
    kind, a, b = form
    if kind == "rel":
        return kind, b, a
    if kind == "eq":
        return form
    if kind == "all":
        return kind, a, converse(b)
    if kind == "imp":
        return kind, converse(a), converse(b)
    raise ValueError(form)


def equality_converse(form):
    """Reverse every explicit equality atom, with formula placeholders opaque."""
    if not isinstance(form, tuple):
        return form
    kind, a, b = form
    if kind == "eq":
        return kind, b, a
    if kind == "rel":
        return form
    if kind == "all":
        return kind, a, equality_converse(b)
    if kind == "imp":
        return kind, equality_converse(a), equality_converse(b)
    raise ValueError(form)


def all_irreflexive_relations(n):
    edges = [(x, y) for x in range(n) for y in range(n) if x != y]
    for bits in range(1 << len(edges)):
        yield frozenset(e for i, e in enumerate(edges) if bits >> i & 1)


def finite_semantics(form, relation, env, phi, n):
    if form == "c":
        return bool(phi >> (env["a"] * n + env["b"]) & 1)
    if form == 0:
        return True
    if form == 1:
        return False
    kind, a, b = form
    if kind == "rel":
        return (env[a], env[b]) in relation
    if kind == "eq":
        return env[a] == env[b]
    if kind == "imp":
        return not finite_semantics(a, relation, env, phi, n) or finite_semantics(b, relation, env, phi, n)
    if kind == "all":
        return all(finite_semantics(b, relation, env | {a: v}, phi, n) for v in range(n))
    raise ValueError(form)


def construct():
    input_manifest = json.loads((REFERENCE / "inputs-manifest.json").read_text())
    for row in input_manifest:
        contents = (REFERENCE / row["path"]).read_bytes()
        assert len(contents) == row["bytes"]
        assert hashlib.sha256(contents).hexdigest() == row["sha256"]
    loader = load_module(SYMMETRY / "logic/vendor_loader.py", "converse_vendor_loader")
    theory, provenance = loader.load_theory()
    spec, _ = theory.published_spec()
    data = json.loads((PACKET / "research/architecture/semantic_rows.json").read_text())
    source = json.loads((PACKET / "inputs/closed-sequence-grammar-next22.json").read_text())
    symbols = json.loads((PACKET / "inputs/semantic-symbols.json").read_text())
    ast = source["ast_dag"]

    @cache
    def bounds(i):
        r = ast[i]
        if r[0] == "L":
            op, *arg = r[1]
            return (1, 0) if op == "dec" else (arg[0], 0) if op == "brk" else (0, arg[0]) if op == "cont" else (0, 0)
        a, b = bounds(r[1]), bounds(r[2])
        return max(a[0] - 1, b[0], 0), max(a[1], b[1] - 1, 0)

    @cache
    def finest(i):
        r = ast[i]
        return finest(r[1]) + finest(r[2]) if r[0] == "N" and bounds(r[1]) == bounds(r[2]) == (0, 0) else (i,)

    atoms = {c: finest(source["atoms"][name]["ast"]) for c, name in symbols.items()}

    def expand(word):
        return tuple(x for c in word for x in atoms[c])

    macros = {int(k): v for k, v in data["macros"].items()}
    macros[177] = "V"
    macros[218] = "V" + macros[119]

    def word(form):
        return "".join(macros[m] for m in theory.emit(form))

    C = spec["bundle_C"]("a", "b", "c")
    G = spec["bundle_G"]("a", "b", "c")
    vr = theory.Imp(theory.Rel("a", "b"), theory.All("c", theory.Rel("a", "b")))
    ve = theory.Imp(theory.Eq("a", "b"), theory.All("c", theory.Eq("a", "b")))
    old_bundle = theory.And(theory.And(C, G), theory.And(vr, ve))
    new_bundle = theory.And(theory.And(converse(C), converse(G)), theory.And(vr, ve))
    old_tail = word(old_bundle) + "".join(macros[m] for m in theory.TAIL)
    new_tail = word(new_bundle) + "".join(macros[m] for m in theory.TAIL)
    prefix = data["prefix"] + "".join(data["rows"])
    old = prefix + old_tail
    new = prefix + new_tail
    assert old_bundle == spec["bundle"]("a", "b", "c")
    assert old_tail == data["tail"]
    assert old == data["reencoded_AX_word"]
    assert expand(old) == expand(data["published_AX_word"])
    assert converse(converse(C)) == C and converse(converse(G)) == G
    assert len(expand(new)) == len(expand(old))
    expected_stack = ["old_top", new_bundle]
    assert theory.symbolic(theory.emit(new_bundle), initial_b="b")[0] == expected_stack

    def best_spelling(raw):
        target = expand(raw)
        best = [None] * (len(target) + 1)
        best[-1] = ""
        for i in range(len(target) - 1, -1, -1):
            for c, a in atoms.items():
                j = i + len(a)
                if target[i:j] == a and best[j] is not None:
                    v = c + best[j]
                    if best[i] is None or (len(v), v) < (len(best[i]), best[i]):
                        best[i] = v
        assert best[0] is not None
        return best[0]

    nchecks = 0
    for n in (1, 2):
        for relation in all_irreflexive_relations(n):
            op = frozenset((y, x) for x, y in relation)
            for phi in range(1 << (n * n)):
                for values in itertools.product(range(n), repeat=3):
                    env = dict(zip(("a", "b", "c"), values))
                    for form in (C, G):
                        assert finite_semantics(converse(form), relation, env, phi, n) == finite_semantics(form, op, env, phi, n)
                        nchecks += 1

    min_old, min_new = best_spelling(old), best_spelling(new)
    assert len(min_old) == 533
    logical_rows = spec["ax_rows"]("a", "h", "b", "c", "u")[1:]
    assert [word(form) for form in logical_rows] == data["rows"]
    eq_prefix = data["prefix"] + "".join(word(equality_converse(form)) for form in logical_rows)
    eq_bundle = equality_converse(old_bundle)
    both_bundle = equality_converse(new_bundle)
    eq_word = eq_prefix + word(eq_bundle) + "".join(macros[m] for m in theory.TAIL)
    both_word = eq_prefix + word(both_bundle) + "".join(macros[m] for m in theory.TAIL)
    assert all(equality_converse(equality_converse(form)) == form for form in [*logical_rows, old_bundle])
    assert len(expand(eq_word)) == len(expand(old)) == len(expand(both_word))
    variants = {}
    for name, raw_word, bundle, eq_op, mem_op in (
        ("original", old, old_bundle, False, False),
        ("converse_membership", new, new_bundle, False, True),
        ("converse_equality", eq_word, eq_bundle, True, False),
        ("both_converses", both_word, both_bundle, True, True),
    ):
        minimum = best_spelling(raw_word)
        variants[name] = dict(
            raw_AX_word=raw_word,
            minimum_AX_word=minimum,
            minimum_dictionary_calls=len(minimum),
            finest_operation_count=len(expand(raw_word)),
            explicit_equality_converse=eq_op,
            C_G_membership_converse=mem_op,
            bundle_ast=bundle,
            root_word_overrides={"76": minimum},
        )
    # Safe nonuniform equality orientations.  The existence row rho1 and
    # the two premises of rho7 must remain coupled as an anchor direction.
    # This basis derives E reflexivity and symmetry without rho3/rho5.
    # The conclusion of rho7 may be reversed because the schema family
    # is unchanged after swapping a,b and exchanging its two antecedents.
    # Equality vacuity may be reversed because its full gated family is
    # unchanged after swapping a,b.  The bundle gate is symmetric in a,b.
    # See converse_encodings.tex for the ordinary finite-proof argument.
    row_numbers = [8, 7, 6, 5, 4, 3, 2, 1]
    assert len(logical_rows) == len(row_numbers)
    prefix_macros = [166, 121, 180, 176]
    assert "".join(macros[m] for m in prefix_macros) == data["prefix"]
    original_gen = spec["ax_rows"]("a", "h", "b", "c", "u")[0]
    anchored_variants = {}
    for anchor, flip3, flip5, flip7concl, eqv_reverse, mem_op in itertools.product((0, 1), repeat=6):
        changed_rows = []
        for number, form in zip(row_numbers, logical_rows):
            changed = equality_converse(form) if anchor else form
            if (number == 3 and flip3) or (number == 5 and flip5):
                changed = equality_converse(changed)
            if number == 7 and flip7concl:
                assert changed[0] == "imp" and changed[2][0] == "imp" and changed[2][2][0] == "eq"
                changed = ("imp", changed[1], ("imp", changed[2][1], equality_converse(changed[2][2])))
            changed_rows.append(changed)
        chosen_C, chosen_G = (converse(C), converse(G)) if mem_op else (C, G)
        chosen_ve = equality_converse(ve) if eqv_reverse else ve
        chosen_bundle = theory.And(theory.And(chosen_C, chosen_G), theory.And(vr, chosen_ve))
        raw = data["prefix"] + "".join(word(form) for form in changed_rows)
        raw += word(chosen_bundle) + "".join(macros[m] for m in theory.TAIL)
        minimum = best_spelling(raw)
        assert expand(minimum) == expand(raw)
        assert len(expand(raw)) == len(expand(old))
        assert theory.symbolic(theory.emit(chosen_bundle), initial_b="b")[0] == ["old_top", chosen_bundle]
        entire_program = prefix_macros + [m for form in changed_rows for m in theory.emit(form)]
        entire_program += theory.emit(chosen_bundle) + theory.TAIL
        symbolic_stack, symbolic_events = theory.symbolic(entire_program)
        assert symbolic_stack == ["old_top", original_gen, *changed_rows, chosen_bundle]
        assert symbolic_events[0] == ("read_b", 2)
        assert symbolic_events[1:] == [(theory.MACROS[m], 11) for m in theory.TAIL]
        assert entire_program.count(158) == entire_program.count(208) == 1
        name = f"anchor{anchor}_r3{flip3}_r5{flip5}_r7c{flip7concl}_ev{eqv_reverse}_mu{mem_op}"
        anchored_variants[name] = dict(
            raw_AX_word=raw,
            raw_AX_prefix=data["prefix"],
            raw_AX_rows=[word(form) for form in changed_rows],
            raw_AX_row_numbers=row_numbers,
            raw_AX_tail=word(chosen_bundle) + "".join(macros[m] for m in theory.TAIL),
            minimum_AX_word=minimum,
            minimum_dictionary_calls=len(minimum),
            finest_operation_count=len(expand(raw)),
            equality_anchor_direction=anchor,
            rho3_premise_flip_relative_to_anchor=flip3,
            rho5_premise_flip_relative_to_anchor=flip5,
            rho7_conclusion_flip_relative_to_anchor=flip7concl,
            equality_vacuity_reversed=eqv_reverse,
            C_G_membership_converse=mem_op,
            logical_row_asts=changed_rows,
            bundle_ast=chosen_bundle,
            full_macro_stack_contract_checked=True,
            single_destructive_u_read_checked=True,
            root_word_overrides={"76": minimum},
        )
        rec = anchored_variants[name]
        assert rec["raw_AX_prefix"] + "".join(rec["raw_AX_rows"]) + rec["raw_AX_tail"] == raw
    assert len(anchored_variants) == 64
    assert anchored_variants["anchor0_r30_r50_r7c0_ev0_mu0"]["raw_AX_word"] == old
    assert anchored_variants["anchor1_r30_r50_r7c0_ev1_mu0"]["raw_AX_word"] == eq_word
    ranking = sorted(anchored_variants, key=lambda name: (anchored_variants[name]["minimum_dictionary_calls"], name))
    new_tokens = theory.emit(new_bundle)
    old_tokens = theory.emit(old_bundle)
    return dict(
        status="PASS_EXACT_SOURCE_EMISSION_AND_CONVERSE_TEMPLATE_CHECKS",
        proved_scope="Ordinary syntactic refutation equivalence of the native theories; source word only, no binary endpoint.",
        source_provenance=provenance,
        pinned_input_data=input_manifest,
        original_AX_word=data["published_AX_word"],
        original_reemitted_AX_word=old,
        modified_AX_word=new,
        original_minimum_dictionary_word=min_old,
        modified_minimum_dictionary_word=min_new,
        original_AX_word_length=len(data["published_AX_word"]),
        original_reemitted_AX_length=len(old),
        modified_reemitted_AX_length=len(new),
        minimum_original_dictionary_calls=len(min_old),
        minimum_modified_dictionary_calls=len(min_new),
        fine_operation_count=len(expand(old)),
        modified_fine_operation_count=len(expand(new)),
        original_prefix=prefix,
        original_bundle_ast=old_bundle,
        modified_bundle_ast=new_bundle,
        original_bundle_macro_word=old_tokens,
        modified_bundle_macro_word=new_tokens,
        prefix_and_logic_unchanged=True,
        formula_tags_unchanged=True,
        ordinary_gates_and_cleanup_unchanged=True,
        matrix_placeholder_opaque=True,
        original_reemission_finest_AST_equal=True,
        template_involution_checked=True,
        small_template_semantics_checks=nchecks,
        root_word_overrides={"76": min_new},
        variants=variants,
        anchored_variants=anchored_variants,
        anchored_variant_count=len(anchored_variants),
        equality_only_proved_scope="Mutual theoremhood by local axiom replacement in the unchanged numerical calculus; no matrix-code transformation.",
        membership_converse_proved_scope="Native full-schema refutation equivalence; separate numerical encodability and compiled endpoint required.",
        anchored_ranking_by_dictionary_calls=ranking,
    )


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, default=Path(__file__).with_name("converse_source.json"))
    args = ap.parse_args()
    result = construct()
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in (
        "status", "original_AX_word_length", "original_reemitted_AX_length", "modified_reemitted_AX_length",
        "minimum_original_dictionary_calls", "minimum_modified_dictionary_calls", "fine_operation_count",
        "modified_fine_operation_count", "small_template_semantics_checks")}, indent=2))
    print(json.dumps({name: v["minimum_dictionary_calls"] for name, v in result["variants"].items()}, indent=2))
    print(json.dumps({name: result["anchored_variants"][name]["minimum_dictionary_calls"] for name in result["anchored_ranking_by_dictionary_calls"][:16]}, indent=2))


if __name__ == "__main__":
    main()
