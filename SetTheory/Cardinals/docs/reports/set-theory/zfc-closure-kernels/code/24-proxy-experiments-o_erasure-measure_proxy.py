"""Measure a full equality frontend with equality expanded as outgoing inclusion.

The strict control retains every original equality/quantifier row after a
syntactic translation. Two additional measured controls derive Euclidean
equality from symmetry and the proxy definition. Every object-atom label n
is shifted to n+1; formula payloads are unchanged. Equality is expanded as
  E(i,j) = forall 0 (Rel(i+1,0) -> Rel(j+1,0)).
This reserves binder 0 without a numerical fresh-variable routine. It is a
compiler experiment, not a proved literal consistency machine.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import importlib
import json
from pathlib import Path
import sys

INC = "3.topwff.inc"


def shifted_label(label):
    if isinstance(label, int):
        return label + 1
    if isinstance(label, tuple) and label[0] == "offset":
        return ("offset", label[1], label[2] + 1)
    return ("offset", label, 1)


def translate(p):
    """Translate an AX formula, distinguishing variable/payload positions."""
    if not isinstance(p, tuple):
        return p
    tag, left, right = p
    if tag == "imp":
        return (tag, translate(left), translate(right))
    if tag == "all":
        return (tag, shifted_label(left), translate(right))
    if tag == "rel":
        return (tag, shifted_label(left), shifted_label(right))
    if tag == "eq":
        return ("all", 0, ("imp", ("rel", shifted_label(left), 0),
                                      ("rel", shifted_label(right), 0)))
    raise ValueError(f"unsupported source constructor: {tag}")


def emit(p, tbe):
    if isinstance(p, tuple) and p[0] == "offset":
        return emit(p[1], tbe) + [INC] * p[2]
    if not isinstance(p, tuple):
        if isinstance(p, int) and p > 1:
            return [177] + [INC] * (p-1)
        return tbe.emit(p)
    if p[0] == "imp" and p[2] == 1:
        inner = p[1]
        if (isinstance(inner, tuple) and inner[0] in ("imp", "all")
                and isinstance(inner[2], tuple) and inner[2][0] == "imp"
                and inner[2][2] == 1):
            return emit(inner[1], tbe) + emit(inner[2][1], tbe) + [
                178 if inner[0] == "imp" else 183]
        return emit(inner, tbe) + [218]
    return emit(p[1], tbe) + emit(p[2], tbe) + [{
        "imp": 119, "rel": 181, "all": 180}[p[0]]]


def symbolic(program, tbe):
    stack, b, u, events = ["old_top"], "h", None, []
    constructors = {119: tbe.Imp, 181: tbe.Rel, 180: tbe.All,
                    178: tbe.And, 183: tbe.Ex}
    for macro in program:
        if macro in (166, 121, 168, 171, 177):
            stack.append({166: "a", 121: b, 168: "c", 171: 0, 177: 1}[macro])
        elif macro == INC:
            value = stack.pop()
            if isinstance(value, int):
                stack.append(value + 1)
            elif isinstance(value, tuple) and value[0] == "offset":
                stack.append(("offset", value[1], value[2] + 1))
            else:
                stack.append(("offset", value, 1))
        elif macro in constructors:
            right, left = stack.pop(), stack.pop()
            stack.append(constructors[macro](left, right))
        elif macro == 218:
            stack[-1] = tbe.Not(stack[-1])
        elif macro == 176:
            events.append(("read_b", len(stack)))
            b = "b"
        elif macro == 158:
            u = "u"
        elif macro == 208:
            if stack[-1] != 0 or u != "u":
                raise ValueError("u leaf loads only into a zero top")
            stack[-1], u = u, None
        elif macro in tbe.TAIL:
            events.append((tbe.MACROS[macro], len(stack)))
        else:
            raise ValueError(f"unexpected macro: {macro}")
    return stack, events


def word_for(tbe, variant, order, frontend="strict"):
    spec, _ = tbe.published_spec()
    source_rows = spec["ax_rows"]("a", "h", "b", "c", "u")
    rows = [translate(p) for p in source_rows]
    if frontend in ("symmetry", "combined"):
        # Generic quantifier schemas range over every label, including 0.
        # Only actual Eq/Rel variable roles need shifting for proxy hygiene.
        for i in (0, 1, 3, 5, 7):
            rows[i] = source_rows[i]
        rows[2] = translate(tbe.Imp(tbe.Eq("a", "b"), tbe.Eq("b", "a")))
        if frontend == "combined":
            rows[4] = translate(tbe.Imp(tbe.Eq("a", "b"), tbe.And(
                tbe.Imp(tbe.Rel("c", "a"), tbe.Rel("c", "b")),
                tbe.Imp(tbe.Rel("a", "c"), tbe.Rel("b", "c")))))
            order = tuple(i for i in order if i != 6)
        program = [166, 121, 180, 176]
    else:
        program = [166, INC, 121, 180, 176]
    for i in order:
        program += emit(rows[i], tbe)
    if variant == "cg":
        theory = translate(spec["bundle"]("a", "b", "c"))
        program += emit(theory, tbe)
        expected = ["old_top", rows[0]] + [rows[i] for i in order] + [theory]
    elif variant == "epsc":
        # This source wrapper uses x=0,y=1 and k=c+2. After translating
        # object-variable positions, x=1,y=2,k=c+3; all exceed reserved 0.
        # k is fresh for every decoded payload c, including exceptional 0/1.
        k = ("offset", "c", 2)
        subset = tbe.All(0, tbe.Imp(tbe.Rel(0, 1), tbe.Rel(0, k)))
        bounded = tbe.All(0, tbe.Ex(k, tbe.All(1, tbe.Imp("c", subset))))
        empty = tbe.All(1, tbe.Not(tbe.Rel(1, 0)))
        closed = tbe.All(0, tbe.Imp(tbe.Or(empty, tbe.Rel(0, k)),
                    tbe.All(1, tbe.Imp("c", tbe.Rel(1, k)))))
        support = tbe.All(1, tbe.Imp(tbe.Rel(1, k), tbe.Ex(0, "c")))
        theory = translate(tbe.Imp(bounded, tbe.Ex(k, tbe.And(closed, support))))
        vr = tbe.Imp(tbe.Rel("a", "b"), tbe.All("c", tbe.Rel("a", "b")))
        ve = tbe.Imp(tbe.Eq("a", "b"), tbe.All("c", tbe.Eq("a", "b")))
        vacuity = translate(tbe.And(vr, ve))
        # EPSC is pushed before current-formula vacuity. Only vacuity is gated.
        program += emit(theory, tbe) + emit(vacuity, tbe)
        expected = ["old_top", rows[0]] + [rows[i] for i in order] + [theory, vacuity]
    else:
        raise ValueError(variant)
    program += tbe.TAIL
    actual, events = symbolic(program, tbe)
    if actual != expected:
        raise ValueError("independent symbolic emitted formula check failed")
    if 182 in program:
        raise ValueError("native equality constructor remains")
    return program, expected[1:], events


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    here = Path(__file__).resolve().parent
    parser.add_argument("--snapshot", type=Path, default=here/"vendor/proveit")
    parser.add_argument("--grammar-script", type=Path, default=here/"vendor/old_rho6_grammar_search.py")
    parser.add_argument("--output", type=Path, default=here/"reproduced")
    parser.add_argument("--seeds", type=int, default=32)
    parser.add_argument("--replay", action="store_true", help="reproduce only the eight frozen best recipes")
    args = parser.parse_args()
    if args.replay:
        reference = json.loads((here/"measurement/proxy_measurements.json").read_text())
        pins = json.loads((here/"vendor_source_pins.json").read_text())
        for relative, expected in pins.items():
            if hashlib.sha256((here/relative).read_bytes()).hexdigest() != expected:
                raise ValueError("vendored source changed: "+relative)
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    source = args.snapshot.resolve() / "Computability/BusyBeaver/Research/ZFC"
    sys.path.insert(0, str(source))
    sys.path.insert(0, str(args.grammar_script.resolve().parent))
    import recover_wade_dag as rwd
    import theory_backend_experiment as tbe
    import old_rho6_grammar_search as grammar
    for name in ("TMBuilder.py", "tm.py", "tmdb.py", "LICENSE.wade"):
        (out/name).write_bytes(rwd.git_bytes(None, "ZF/generator/"+name))
    sys.path.insert(0, str(out))
    backend = importlib.import_module("TMBuilder")
    nodes, names = rwd.parse_dag(rwd.git_bytes(None, "ZF/m254/coq/prog/Dag254.v").decode())
    _, _, old_contract = tbe.old_contract(nodes)
    macro_bounds = grammar.closed_macro_checks(nodes, tbe.MACROS)
    records = {}
    cases = [("cg", "strict", (1,2,3,4,5,6,7,8)),
        ("cg", "strict", (1,7,5,3,2,4,6,8)),
        ("epsc", "strict", (1,2,3,4,5,6,7,8)),
        ("epsc", "strict", (1,7,5,3,2,4,6,8))]
    cases += [("epsc", mode, order)
        for mode in ("symmetry", "combined")
        for order in ((1,2,3,4,5,6,7,8), (1,7,5,3,2,4,6,8))]
    for variant, frontend, order in cases:
        program, formulas, events = word_for(tbe, variant, order, frontend)
        key = variant + "-" + frontend + "-" + "".join(map(str, order))
        records[key] = {"order": order, "macro_count": len(program),
            "frontend":frontend,
            "all_eight_original_rows_retained": frontend == "strict",
            "bottom_model": "empty distinguished object" if frontend == "strict" and variant == "epsc" else "ZFC irreflexivity",
            "word_sha256": hashlib.sha256(json.dumps(program,separators=(",",":")).encode()).hexdigest(),
            "symbolic_formulas_exact": True, "native_equality_emitted": False,
            "events": events, "measurements": [], "histogram": {}}
        (out/(key+".word.json")).write_text(json.dumps(program,indent=2)+"\n")
        (out/(key+".formulas.json")).write_text(json.dumps(formulas,indent=2)+"\n")
        costs, best = Counter(), None
        seeds = ([reference["variants"][key]["best"]["seed"]]
                 if args.replay else (None, *range(args.seeds)))
        for seed in seeds:
            builder, recipe = grammar.build(backend,nodes,names,program,seed,4,rwd,tbe)
            measurement = grammar.record(builder, None)
            cost = measurement["working_states"]
            costs[cost] += 1
            if best is None or cost < best["working_states"]:
                path = out/(key+".named.tm")
                builder.tm.save(str(path))
                best = dict(measurement, seed=seed, recipe=recipe,
                    named_table_sha256=hashlib.sha256(path.read_bytes()).hexdigest())
                print(json.dumps({"variant":key,"new_minimum":cost,"seed":seed}),flush=True)
            records[key]["measurements"].append(dict(measurement,seed=seed))
        records[key]["best"] = best
        records[key]["histogram"] = dict(sorted(costs.items()))
        if args.replay:
            expected = reference["variants"][key]["best"]
            for field in ("working_states", "decision_states", "framework_states", "named_table_sha256"):
                if best[field] != expected[field]:
                    raise ValueError(f"frozen replay differs for {key}: {field}")
    evidence = {"status":"compiler measurement; no literal consistency endpoint",
        "proxy":"forall 0 (Rel(a+1,0) -> Rel(b+1,0))",
        "full_equality_frontend":"strict rows, or symmetry plus derived Euclidean law",
        "object_atom_labels_shifted_by":1,
        "strict_quantifier_labels_shifted_by":1,
        "compact_generic_quantifier_labels_shifted_by":0,
        "reserved_proxy_binder":0,
        "primitive_bottom_source_interpretation":"target F=Rel(0,0)",
        "strict_epsc_bottom_soundness":"set v0 to an empty object; no global IR axiom needed",
        "compact_epsc_soundness":"use ZFC IR; generic quantifiers include label 0",
        "epsc_wrapper_fresh_binder":"c+3, distinguished variables 1 and 2",
        "source_commit":rwd.COMMIT, "old_contract":old_contract,
        "closed_original_macro_bounds":macro_bounds,
        "additional_INC_macro_closed":True, "variants":records,
        "source_proof_translation_formalized":False,
        "numerical_schema_bridge_formalized":False,
        "compiler_simulation_proved":False,
        "fixed_recipe_replay":args.replay,
        "new_consistency_machine_state_bound_claimed":False}
    (out/"proxy_measurements.json").write_text(json.dumps(evidence,indent=2)+"\n")
    print(json.dumps({k:v["best"] for k,v in records.items()},indent=2),flush=True)


if __name__ == "__main__":
    main()
