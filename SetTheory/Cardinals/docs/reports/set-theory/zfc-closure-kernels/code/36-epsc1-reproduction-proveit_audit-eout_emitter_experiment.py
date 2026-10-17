#!/usr/bin/env python3
"""Complete-row Eout compiler controls, retaining every original logical row.

The words shift explicit binder/atom indices by one and expand equality into
outgoing inclusion at reserved index zero. Formula-valued numerical payloads
are left unchanged. This is an exact emitter/compiler experiment, NOT a proof
that all emitted numerical payloads obey the source-translation invariant.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import importlib
import itertools
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
_paths = argparse.ArgumentParser(add_help=False)
_paths.add_argument("--repo", type=Path, default=ROOT / "sources/proveit")
_repo_args, _ = _paths.parse_known_args()
SOURCE = _repo_args.repo.resolve() / "Computability/BusyBeaver/Research/ZFC"
sys.path.insert(0, str(SOURCE))
import recover_wade_dag as recover
import theory_backend_experiment as theory
import full_grammar_experiment as grammar
from pairing_backend_experiment import execute_helper

INC = "3.topwff.inc"
NATIVE = {"rel_plus", "rel_leftplus", "all_plus", "exists_plus", "r0_plus", "all_zero"}


def shift(i):
    return i + 1 if isinstance(i, int) else ("succ", i)


def translate(a):
    if not isinstance(a, tuple):
        return a
    tag, x, y = a
    if tag == "imp":
        return theory.Imp(translate(x), translate(y))
    if tag == "rel":
        return theory.Rel(shift(x), shift(y))
    if tag == "all":
        return theory.All(shift(x), translate(y))
    if tag == "eq":
        return theory.All(0, theory.Imp(theory.Rel(shift(x), 0),
                                        theory.Rel(shift(y), 0)))
    raise ValueError(tag)


def emit(a):
    if a == "h":
        return [121]
    if isinstance(a, tuple) and a[0] == "succ":
        return emit(a[1]) + [INC]
    if isinstance(a, int) and a > 1:
        return [171] + [INC] * a
    if not isinstance(a, tuple):
        return theory.emit(a)
    if a[0] == "imp" and a[2] == 1:
        inner = a[1]
        if (isinstance(inner, tuple) and inner[0] in ("imp", "all")
                and isinstance(inner[2], tuple) and inner[2][0] == "imp"
                and inner[2][2] == 1):
            return emit(inner[1]) + emit(inner[2][1]) + [
                178 if inner[0] == "imp" else 183]
        return emit(inner) + [218]
    return emit(a[1]) + emit(a[2]) + [{"imp": 119, "rel": 181, "all": 180}[a[0]]]


def symbolic(word):
    stack, cache, u, events = ["old_top"], "h", None, []
    cons = {119: theory.Imp, 181: theory.Rel, 180: theory.All,
            178: theory.And, 183: theory.Ex}
    for token in word:
        if token in (166, 121, 168, 171, 177):
            stack.append({166: "a", 121: cache, 168: "c", 171: 0, 177: 1}[token])
        elif token == INC:
            stack[-1] = shift(stack[-1])
        elif token == "r0_plus":
            stack[-1] = theory.Rel(shift(stack[-1]), 0)
        elif token == "all_zero":
            stack[-1] = theory.All(0, stack[-1])
        elif token in NATIVE:
            y, x = stack.pop(), stack.pop()
            if token == "rel_plus":
                stack.append(theory.Rel(shift(x), shift(y)))
            elif token == "rel_leftplus":
                stack.append(theory.Rel(shift(x), y))
            elif token == "all_plus":
                stack.append(theory.All(shift(x), y))
            else:
                stack.append(theory.Ex(shift(x), y))
        elif token in cons:
            y, x = stack.pop(), stack.pop()
            stack.append(cons[token](x, y))
        elif token == 218:
            stack[-1] = theory.Not(stack[-1])
        elif token == 176:
            events.append(("read_b", len(stack)))
            cache = "b"
        elif token == 158:
            u = "u"
        elif token == 208:
            if stack[-1] != 0 or u != "u":
                raise ValueError("unexpected u load")
            stack[-1], u = "u", None
        elif token in theory.TAIL:
            events.append((theory.MACROS[token], len(stack)))
        else:
            raise ValueError(f"unknown macro {token}")
    return stack, events


def emit_native(a, specialized=False):
    """Charge index shifting once inside new shared constructors."""
    if not isinstance(a, tuple):
        return emit(a)
    tag, x, y = a
    if tag == "eq":
        if specialized:
            return emit(x) + ["r0_plus"] + emit(y) + ["r0_plus", 119, "all_zero"]
        return ([171] + emit(x) + [171, "rel_leftplus"] +
                emit(y) + [171, "rel_leftplus", 119, 180])
    if tag == "rel":
        return emit(x) + emit(y) + ["rel_plus"]
    if tag == "all":
        return emit(x) + emit_native(y, specialized) + ["all_plus"]
    if tag == "imp" and y == 1:
        if (isinstance(x, tuple) and x[0] in ("imp", "all")
                and isinstance(x[2], tuple) and x[2][0] == "imp"
                and x[2][2] == 1):
            return ((emit(x[1]) if x[0] == "all" else emit_native(x[1], specialized)) +
                    emit_native(x[2][1], specialized) + ["exists_plus" if x[0] == "all" else 178])
        return emit_native(x, specialized) + [218]
    return emit_native(x, specialized) + emit_native(y, specialized) + [119]


def tree_count(a):
    if not isinstance(a, tuple):
        return 1
    if a[0] == "succ":
        return 1
    if a[0] in ("rel", "eq"):
        return 1
    return 1 + tree_count(a[2]) + (tree_count(a[1]) if a[0] == "imp" else 0)


def constructor_counts(a):
    if not isinstance(a, tuple) or a[0] == "succ":
        return Counter({"formula_payload_or_falsity": 1})
    tag, x, y = a
    r = Counter({tag: 1})
    if tag == "imp":
        r += constructor_counts(x)
        r += constructor_counts(y)
    elif tag == "all":
        r += constructor_counts(y)
    return r


def make_word(order=tuple(range(1, 9)), components=("C", "G", "V"),
              grouping=0, shifted=True, native=False, specialized=False):
    spec, _ = theory.published_spec()
    rows = spec["ax_rows"]("a", "h", "b", "c", "u")
    vr = theory.Imp(theory.Rel("a", "b"), theory.All("c", theory.Rel("a", "b")))
    ve = theory.Imp(theory.Eq("a", "b"), theory.All("c", theory.Eq("a", "b")))
    parts = {"C": spec["bundle_C"]("a", "b", "c"),
             "G": spec["bundle_G"]("a", "b", "c"), "V": theory.And(vr, ve)}
    x, y, z = [parts[c] for c in components]
    bundle = theory.And(theory.And(x, y), z) if grouping == 0 else theory.And(x, theory.And(y, z))
    source = [rows[i] for i in (0, *order)] + [bundle]
    target = list(map(translate, source)) if shifted else source
    if not shifted:
        old = [166, 121, 180, 176]
        old += [m for a in source[1:] for m in theory.emit(a)] + theory.TAIL
        return old, source, target
    if native:
        word = emit_native(source[0], specialized) + [176]
        word += [m for a in source[1:] for m in emit_native(a, specialized)] + theory.TAIL
    else:
        word = emit(target[0]) + [176]
        word += [m for a in target[1:] for m in emit(a)] + theory.TAIL
    actual, events = symbolic(word)
    if actual != ["old_top"] + target:
        raise ValueError("independent stack execution disagrees with expanded formulas")
    if 182 in word:
        raise ValueError("primitive equality remains in emitted word")
    return word, source, target


def build(backend, nodes, names, word, radix, shared=True):
    b = recover.builder_from_dag(backend, nodes, names)
    b.sequence_lookup = {s.seq: i for i, s in enumerate(b.sequences)}
    extra_roots = {}
    if any(t in NATIVE for t in word):
        registers = [b.reg(name) for name in recover.REGISTERS]
        leftbase = b.add_sequence([160, registers[6].inc, 120])
        rel_left = b.add_sequence([leftbase, registers[1].inc])
        rel_both = b.add_sequence([registers[1].inc, rel_left])
        all_left = b.add_sequence([leftbase, 159])
        ex_left = b.add_sequence([218, all_left, 218])
        r0_plus = b.add_sequence([registers[1].inc, 216, 120, registers[1].inc])
        all_zero = b.add_sequence([120, 159])
        extra_roots = dict(rel_plus=rel_both, rel_leftplus=rel_left,
                           all_plus=all_left, exists_plus=ex_left,
                           r0_plus=r0_plus, all_zero=all_zero)
        word = [extra_roots.get(x, x) for x in word]
        for name, q in extra_roots.items():
            b.sequences[q].name = name + "().0"
    saved_macros = theory.MACROS.copy()
    theory.MACROS.update({q: name for name, q in extra_roots.items()})
    try:
        theory.lower_program(b, nodes, word, "Eout_complete", shared=shared,
                             base3=(radix == 3))
    finally:
        theory.MACROS.clear()
        theory.MACROS.update(saved_macros)
    b.generate()
    b.tm.gc()
    b.proxy_roots = extra_roots
    return b


def native_helper_checks(builder, radix):
    pair = lambda a, b: (a + b) * (a + b + 1) // 2 + b
    cases = 0
    for a, b, rest, kind in itertools.product(range(5), range(5), (0, 1, 5),
                                               ("rel_plus", "rel_leftplus", "all_plus")):
        v = [7, b, pair(a, rest), 0, 11, 13, 0, 0, 19]
        tag = 2 if kind == "all_plus" else 1
        y = b + 1 if kind == "rel_plus" else b
        wanted = [7, radix * pair(a + 1, y) + tag, rest, 0, 11, 13, 0, 0, 19]
        result = execute_helper(builder, builder.proxy_roots[kind], v)
        if result != ("normal",) or v != wanted:
            raise ValueError(f"native shifted-constructor check failed: {a,b,rest,kind,v,wanted}")
        cases += 1
    for a, rest, kind in itertools.product(range(10), (0, 1, 5), ("r0_plus", "all_zero")):
        v = [7, a, rest, 0, 11, 13, 0, 0, 19]
        wanted = v.copy()
        wanted[1] = radix * (pair(a + 1, 0) if kind == "r0_plus" else pair(0, a)) + (1 if kind == "r0_plus" else 2)
        result = execute_helper(builder, builder.proxy_roots[kind], v)
        if result != ("normal",) or v != wanted:
            raise ValueError(f"native zero constructor check failed: {a,rest,kind,v,wanted}")
        cases += 1
    return cases


def counts(machine):
    states = {q for q, _ in machine.states}
    return {"states": len(states), "framework": sum(q[0].isdigit() for q in states),
            "decision": sum(not q[0].isdigit() for q in states),
            "rows": len(machine.states),
            "primitive_equality_helper_reachable": any(q.startswith("weq(") for q in states)}


def formula_checks():
    """Finite pointed semantics for literal source formulas, using actual equality.

    We retain exactly the relations where outgoing inclusion is literal
    equality, and evaluate only false designated points. These diagnostics do
    not claim those finite pointed relations satisfy PSC or the full theory.
    """
    formulas = [theory.Rel(0, 0), theory.Rel(0, 1), theory.Eq(0, 1),
                theory.All(0, theory.Eq(0, 1)),
                theory.All(1, theory.Imp(theory.Rel(0, 1), theory.Rel(1, 0))),
                theory.Imp(theory.All(0, theory.Rel(0, 1)), 1),
                theory.All(0, theory.All(1, theory.Imp(theory.Eq(0, 1), theory.Rel(0, 1))))]
    cases = 0
    def evaluate(f, env, relation, n, bottom):
        if f == 1:
            return bottom
        tag, a, b = f
        if tag == "rel": return (env[a], env[b]) in relation
        if tag == "eq": return env[a] == env[b]
        if tag == "imp":
            return not evaluate(a, env, relation, n, bottom) or evaluate(b, env, relation, n, bottom)
        if tag == "all":
            return all(evaluate(b, env | {a: z}, relation, n, bottom) for z in range(n))
        raise ValueError(tag)
    def target_eval(f, env, relation, n):
        if f == 1:
            return (env[0], env[0]) in relation
        tag, a, b = f
        if tag == "rel": return (env[a], env[b]) in relation
        if tag == "imp": return not target_eval(a, env, relation, n) or target_eval(b, env, relation, n)
        if tag == "all": return all(target_eval(b, env | {a: z}, relation, n) for z in range(n))
        raise ValueError(tag)
    for n in (1, 2, 3):
        edges = list(itertools.product(range(n), repeat=2))
        for bits in range(1 << len(edges)):
            rel = {p for j, p in enumerate(edges) if bits >> j & 1}
            outgoing = lambda x, y: all((x, z) not in rel or (y, z) in rel for z in range(n))
            if not all(outgoing(x, y) == (x == y) for x, y in edges):
                continue
            for e in range(n):
                if (e, e) in rel:
                    continue
                for a, b in edges:
                    srcenv, dstenv = {0: a, 1: b}, {0: e, 1: a, 2: b}
                    for f in formulas:
                        if evaluate(f, srcenv, rel, n, False) != target_eval(translate(f), dstenv, rel, n):
                            raise ValueError("reserved-zero semantics mismatch")
                        cases += 1
    # Omitting the endpoint shift allows the proxy's local binder to capture
    # the left endpoint even in a two-cycle with literal outgoing equality.
    cycle = {(0, 1), (1, 0)}
    unshifted_eq = theory.All(0, theory.Imp(theory.Rel(0, 0), theory.Rel(1, 0)))
    endpoint_capture = (not evaluate(theory.Eq(0, 1), {0: 0, 1: 1}, cycle, 2, False)
                        and target_eval(unshifted_eq, {0: 0, 1: 1}, cycle, 2))
    # An ordinary translated binder at zero captures the falsity parameter.
    # This pointed permutation relation has Eout equal to literal equality.
    pointed = {(0, 2), (2, 0), (1, 1)}
    src = theory.All(0, theory.Imp(1, theory.Rel(1, 1)))
    bad = theory.All(0, theory.Imp(1, theory.Rel(2, 2)))
    falsity_capture = (evaluate(src, {0: 0, 1: 0}, pointed, 3, False)
                       and not target_eval(bad, {0: 0, 1: 0, 2: 0}, pointed, 3))
    if not endpoint_capture or not falsity_capture:
        raise ValueError("binder negative control stopped detecting capture")
    return {"formula_count": len(formulas), "pointed_semantics_cases": cases,
            "unshifted_equality_endpoint_capture_detected": endpoint_capture,
            "unrestricted_zero_falsity_capture_detected": falsity_capture}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo", type=Path, default=_repo_args.repo,
                   help="Pinned ProveIt source tree containing the recovered backend")
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--search", action="store_true")
    args = p.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    for name in ("TMBuilder.py", "tm.py", "tmdb.py", "LICENSE.wade"):
        (out / name).write_bytes(recover.git_bytes(None, "ZF/generator/" + name))
    sys.path.insert(0, str(out))
    backend = importlib.import_module("TMBuilder")
    nodes, names = recover.parse_dag(recover.git_bytes(None, "ZF/m254/coq/prog/Dag254.v").decode())
    _, _, old_contract = theory.old_contract(nodes)
    word, source, target = make_word()
    native_word, _, _ = make_word(native=True)
    special_word, _, _ = make_word(native=True, specialized=True)
    result = {"description": __doc__, "source_pin": "2c74914bdfc98920ddcc3ff7c092cce10db4d709",
              "upstream_pin": recover.COMMIT, "original_contract": old_contract,
              "semantic_diagnostics": formula_checks(),
              "source_formula_nodes": list(map(tree_count, source)),
              "target_formula_nodes": list(map(tree_count, target)),
              "source_constructor_counts": dict(sum(map(constructor_counts, source), Counter())),
              "target_constructor_counts": dict(sum(map(constructor_counts, target), Counter())),
              "emitter_macros": len(word), "top_increments": word.count(INC),
              "native_emitter_macros": len(native_word), "native_word": native_word,
              "specialized_emitter_macros": len(special_word), "specialized_word": special_word,
              "all_nine_logical_outputs_retained": True,
              "C_G_and_both_vacuity_families_retained": True,
              "independent_symbolic_stack_contract": True,
              "source_formulas": source, "target_formulas": target, "word": word,
              "complete_numeric_transport_proved": False,
              "binary_simulation_proved": False, "state_record_claimed": False,
              "variants": []}
    for label, w, radix, shared in [
        ("original_baseline", theory.expand(nodes, 1), 4, False),
        ("complete_proxy_base4_plain", word, 4, False),
        ("complete_proxy_base4_shared", word, 4, True),
        ("complete_proxy_base3_plain", word, 3, False),
        ("complete_proxy_base3_shared", word, 3, True),
        ("native_proxy_base4_shared", native_word, 4, True),
        ("native_proxy_base3_shared", native_word, 3, True),
        ("specialized_proxy_base4_shared", special_word, 4, True),
        ("specialized_proxy_base3_shared", special_word, 3, True)]:
        b = build(backend, nodes, names, w, radix, shared)
        table, _, missing = grammar.normalize(b.tm)
        path = out / (label + ".tm")
        path.write_bytes(table)
        item = {"variant": label, **counts(b.tm), "radix": radix,
                "normalized_total_rows": len(table.splitlines()) - 1,
                "totalized_rows": missing, "sha256": hashlib.sha256(table).hexdigest()}
        if b.proxy_roots:
            item["native_constructor_register_cases"] = native_helper_checks(b, radix)
        result["variants"].append(item)
        print(json.dumps(item), flush=True)
    if args.search:
        hist, best = Counter(), None
        # All bundle layouts; six transparent row orders. This is a declared
        # finite family, not an exhaustive permutation or minimality claim.
        orders = [tuple(range(1, 9)), tuple(reversed(range(1, 9))),
                  (1, 3, 5, 7, 2, 4, 6, 8), (2, 4, 6, 8, 1, 3, 5, 7),
                  (1, 7, 5, 3, 2, 4, 6, 8), (8, 6, 4, 2, 3, 5, 7, 1)]
        for order, components, grouping, radix, lane in itertools.product(
                orders, itertools.permutations(("C", "G", "V")), (0, 1), (3, 4), ("expanded", "native", "specialized")):
            w, _, _ = make_word(order, components, grouping, native=(lane != "expanded"), specialized=(lane == "specialized"))
            b = build(backend, nodes, names, w, radix)
            c = counts(b.tm)
            hist[f"{lane}_base{radix}_{c['states']}"] += 1
            key = c["states"], c["decision"], order, components, grouping, radix, lane
            if best is None or key < best[0]:
                best = key, b, w
        key, b, w = best
        table, _, missing = grammar.normalize(b.tm)
        (out / "best_complete_proxy.tm").write_bytes(table)
        result["search"] = {"recipes": sum(hist.values()), "histogram": dict(hist),
                            "best_key": key, **counts(b.tm), "best_word": w,
                            "sha256": hashlib.sha256(table).hexdigest()}
        print(json.dumps({k:v for k,v in result["search"].items() if k != "best_word"}), flush=True)
    (out / "evidence.json").write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
