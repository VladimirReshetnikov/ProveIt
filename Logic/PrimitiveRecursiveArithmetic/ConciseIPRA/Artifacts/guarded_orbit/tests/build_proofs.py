"""Untrusted proof builders and finite checks for the combined candidate.

No candidate checker imports this file.  Named derivations are generated
independently from the compact opener, then serialized by the upstream
lexical or global producer.  This is executable evidence, not a Lean proof.
"""
import ast
import collections
import copy
import importlib.util
import itertools
import json
import os
from pathlib import Path
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
PACKAGE = HERE.parent
ROOT = PACKAGE
OUT = HERE / "certificates"
OUT.mkdir(exist_ok=True)
sys.setrecursionlimit(20000)

def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module

P = load_module("native_producer", HERE / "reference/native_producer.py")
N = load_module("normalizer", HERE / "reference/normalizer.py")
GP = load_module("producer", HERE / "reference/legacy_global_producer.py")
G = load_module("guarded_build", HERE / "reference/guarded_build.py")
G.P = P

def cut(proof, assumed, supplied, memo=None):
    """Capture-safe here because all builders use distinct fresh binders."""
    if memo is None:
        memo = {}
    if id(proof) in memo:
        return memo[id(proof)]
    if proof["rule"] == "Hyp" and proof["goal"] == assumed:
        return supplied
    result = dict(proof)
    for field in ("major", "minor", "premise", "continuation"):
        if field in proof:
            result[field] = cut(proof[field], assumed, supplied, memo)
    memo[id(proof)] = result
    return result

G.cut = cut

def safe_wrap(proof, left, right):
    """L=s, s=t, R=t -> L=R, assuming s,L,R are nonliteral-zero."""
    source, target = proof["goal"][1:]
    assert source != 0
    assert left["goal"][2] == source and right["goal"][2] == target
    assert left["goal"][1] != 0 and right["goal"][1] != 0
    first = N.chain(left, proof)
    return (N.chain(first, N.sym(right)) if target != 0
            else N.join_zero(first, right))

def safe_unwrap(proof, left, right):
    """L=s, L=R, R=t -> s=t by contracting nonzero L and R."""
    L, source = left["goal"][1:]
    R, target = right["goal"][1:]
    assert proof["goal"] == P.Eq(L, R)
    hole = N.fresh("unwrap_left")
    first = N.tr(left, hole, P.Eq(P.V(hole), R), proof)
    hole = N.fresh("unwrap_right")
    return N.tr(right, hole, P.Eq(source, P.V(hole)), first)

def guarded_zero(equation):
    goal = G.guard(0, equation)
    return N.join_zero(P.compute(goal[1]), P.compute(goal[2]))

def restricted_lift_intro(proof, target=None):
    target = target or G.lift_formula(proof["goal"])
    assert proof["goal"][1] != 0
    x, y, body = target[1:]
    z = N.fresh("safe_lift_z")
    following = P.substitute(P.substitute(body, x, 0), y, P.S(P.V(z)))
    premise = safe_wrap(proof, P.compute(following[1]), P.compute(following[2]))
    return P.introduction(target, 0, z, "progress", premise)

def safe_lift_elim(proof):
    _, x, y, matrix = proof["goal"]
    eigen = N.fresh("safe_lift_a")
    opened = P.substitute(matrix, x, P.V(eigen))
    zero = P.substitute(opened, y, 0)
    base = N.join_zero(P.compute(zero[1]), P.compute(zero[2]))
    at_one = P.specialize(P.hyp(P.Q(y, opened)), P.ONE, base)
    result = safe_unwrap(at_one, P.compute(at_one["goal"][1]),
                         P.compute(at_one["goal"][2]))
    return P.elimination(proof, eigen, result)

def compound_numerical_cases(index, body, base, step, target):
    """Numerical cases for equations with a stable I/S-headed left side."""
    assert body[0] == "eq" and body[1][0] in ("i", "s")
    assert base["goal"] == P.substitute(body, index, 0)
    lifted = G.lift_formula(body)
    lifted_zero = P.substitute(lifted, index, 0)
    lifted_base = restricted_lift_intro(base, lifted_zero)
    eigen = N.fresh("safe_cases_z")
    branch = step(P.V(eigen))
    assert branch["goal"] == P.substitute(body, index, P.S(P.V(eigen)))
    # Support contextual cases, although the test helpers need no base IH.
    branch = cut(branch, base["goal"], safe_lift_elim(P.hyp(lifted_zero)))
    lifted_branch = restricted_lift_intro(
        branch, P.substitute(lifted, index, P.S(P.V(eigen))))
    compound = G.compound_cases(index, lifted, lifted_base, eigen,
                                lifted_branch, target)
    return safe_lift_elim(compound)

def reversed_filter(target):
    """Cases on C(Z(v),v,0)=v, then safe symmetry at its I-headed source."""
    n = N.fresh("reversed_filter_n")
    def filtered(value):
        return P.C(N.zero_test(value), value, 0)
    body = P.Eq(filtered(P.V(n)), P.V(n))
    base = N.chain(
        N.cong(P.compute(N.zero_test(0)), lambda z: P.C(z, 0, 0)),
        P.compute(P.C(P.ONE, 0, 0)))
    def step(k):
        value = P.S(k)
        return N.chain(
            N.cong(P.compute(N.zero_test(value)), lambda z: P.C(z, value, 0)),
            P.compute(P.C(0, value, 0)))
    return N.sym(compound_numerical_cases(n, body, base, step, target))

N.numerical_cases = compound_numerical_cases
N.zero_filter = reversed_filter

def full_wrap(proof, left, right):
    if proof["goal"][1] != 0:
        return safe_wrap(proof, left, right)
    if proof["goal"][2] == 0:
        return N.join_zero(left, right)
    reverse = N.zero_symmetry(proof)
    return N.sym(safe_wrap(reverse, right, left))

# Everything below may use the now-constructed uniform zero-source symmetry.
G.join = N.full_chain
G.sym = N.full_symmetry
G.wrap_equation = full_wrap
G.unwrap_equation = safe_unwrap
G.guard_zero = guarded_zero
G.lift_elim = safe_lift_elim

def normalize_equational_zero_transport(proof, memo=None):
    """Never call the old normalizer's compound-Q case construction."""
    if memo is None:
        memo = {}
    if id(proof) in memo:
        return memo[id(proof)]
    result = dict(proof)
    for field in ("major", "minor", "premise", "continuation"):
        if field in proof:
            result[field] = normalize_equational_zero_transport(proof[field], memo)
    if result["rule"] == "Tr" and result["major"]["goal"][1] == 0:
        assert result["motive"][0] == "eq", "compound zero-source transport needs its own lifting"
        result = N.full_transport(result["major"], result["variable"],
                                   result["motive"], result["minor"])
    memo[id(proof)] = result
    return result

def proof_audit(proof):
    seen = set()
    count = collections.Counter()
    defects = []
    orbit_count = 0
    guard_count = 0
    used_progress = 0
    def contains_hyp(node, goal, visited=None):
        if visited is None:
            visited = set()
        if id(node) in visited:
            return False
        visited.add(id(node))
        if node["rule"] == "Hyp" and node["goal"] == goal:
            return True
        return any(contains_hyp(node[f], goal, visited)
                   for f in ("major", "minor", "premise", "continuation") if f in node)
    def visit(node):
        nonlocal orbit_count, guard_count, used_progress
        if id(node) in seen:
            return
        seen.add(id(node))
        count[node["rule"]] += 1
        if node["rule"] == "Tr":
            if node["major"]["goal"][1] == 0:
                defects.append("literal-zero transport source")
        if node["rule"] == "DI":
            _, x, y, body = node["goal"]
            wanted = "progress" if body[0] == "eq" else "case"
            if node["mode"] != wanted:
                defects.append("introduction mode disagrees with matrix root")
            if body[0] == "eq":
                left, right = body[1:]
                guarded = all(t != 0 and t[0] == "i" and t[1] == P.V(y)
                              and t[2] == 0 for t in (left, right))
                orbit = (left == P.V(y) and right != 0 and right[0] == "i"
                         and right[1] == P.V(y) and right[4] == P.S(P.V(right[3])))
                guard_count += int(guarded)
                orbit_count += int(orbit)
                local = P.substitute(P.substitute(body, x, node["witness"]),
                                     y, P.V(node["eigen"]))
                used_progress += int(contains_hyp(node["premise"], local))
        for field in ("major", "minor", "premise", "continuation"):
            if field in node:
                visit(node[field])
    visit(proof)
    return {"distinct_proof_nodes": len(seen), "rules": dict(count),
            "guarded_atomic_introductions": guard_count,
            "orbit_atomic_introductions": orbit_count,
            "progress_introductions_with_used_IH": used_progress,
            "defects": defects}

def subst_proof(proof, variable, value, memo=None):
    if memo is None:
        memo = {}
    if id(proof) in memo:
        return memo[id(proof)]
    result = dict(proof)
    for field in ("goal", "motive", "witness", "target"):
        if field in result:
            result[field] = P.substitute(result[field], variable, value)
    for field in ("major", "minor", "premise", "continuation"):
        if field in result:
            result[field] = subst_proof(result[field], variable, value, memo)
    memo[id(proof)] = result
    return result

def ordinary_proofs():
    cases = []
    def add(name, proof, description, expected=True, canonical=True):
        proof = normalize_equational_zero_transport(proof)
        cases.append({"name": name, "proof": proof, "expected": expected,
                      "canonical_goal": canonical, "description": description})
    add("computation_zero", P.compute(P.I(0, P.TWO, "base_state", P.ONE)),
        "Unconditional zero computation.")
    add("computation_successor", P.compute(P.I(P.TWO, P.ONE, "step_state", P.S(P.V("step_state")))),
        "Successor computation with state dependence.")
    add("reflexivity", P.reflexivity(P.TWO, "direct_refl"),
        "Reflexivity derived from a computation equation.")
    eq = P.compute(P.I(0, P.ONE, "lifted_state", P.TWO))
    lift = G.lift_intro(eq)
    add("guarded_lift_intro", lift, "Guarded atomic introduction.")
    add("guarded_lift_elim", G.lift_elim(lift), "Guarded D elimination and Q use.")
    equation = P.Eq(P.TWO, P.TWO)
    imp = G.implication_intro(equation, equation, P.hyp(equation))
    add("compound_implication_intro", imp, "Compound case introduction for A -> A.")
    add("compound_implication_elim", G.implication_elim(
        imp, equation, equation, P.reflexivity(P.TWO, "imp_refl")),
        "Compound implication elimination.")

    n, u = N.fresh("induction_n"), N.fresh("induction_u")
    invariant = P.Eq(P.I(P.V(n), 0, u, P.V(u)), 0)
    base = P.compute(P.I(0, 0, u, P.V(u)))
    def step(k):
        current = P.I(k, 0, u, P.V(u))
        return N.chain(P.compute(P.I(P.S(k), 0, u, P.V(u))),
                       P.hyp(P.Eq(current, 0)))
    induction = G.guarded_induction(n, invariant, base, step)
    add("guarded_equation_induction", induction,
        "Derived equation induction; the step uses the IH, mediated by compound cases.")

    source = P.I(0, P.ONE, N.fresh("transport_state"), 0)
    hole = N.fresh("transport_hole")
    motive = G.lift_formula(P.Eq(P.V(hole), P.V(hole)))
    source_goal = P.substitute(motive, hole, source)
    source_lift = G.lift_intro(P.reflexivity(source, N.fresh("transport_refl")), source_goal)
    compound = P.transport(P.compute(source), hole, motive, source_lift)
    add("transport_under_guarded_D", compound,
        "Permitted nonzero-source transport crosses a guarded D binder.")

    t = P.V("generic_zero_symmetry_parameter")
    open_proof = N.zero_symmetry(P.hyp(P.Eq(0, t)))
    open_audit = proof_audit(open_proof)
    assert not open_audit["defects"]
    (ROOT / "evidence/contextual_zero_symmetry_audit.json").write_text(json.dumps({
        "sequent": "0 = t |- t = 0; t is a fresh numerical parameter",
        "audit": open_audit,
        "closed_realizations": [
            "zero_symmetry_one_implication",
            "zero_symmetry_closed_iterator_implication",
            "zero_symmetry_universal_closure"],
        "status": "Named derivation audit; separate closed CLI realizations are tested."
    }, indent=2) + "\n")

    for name, value in [
        ("zero_symmetry_one_implication", P.ONE),
        ("zero_symmetry_closed_iterator_implication",
         P.I(P.ONE, 0, "closed_target_state", P.S(P.V("closed_target_state")))),
    ]:
        instance = subst_proof(open_proof, t[1], value)
        left, right = P.Eq(0, value), P.Eq(value, 0)
        add(name, G.implication_intro(left, right, instance),
            "Closed guarded implication realizing contextual zero-source symmetry.")

    y, x, z = N.fresh("universal_y"), N.fresh("universal_x"), N.fresh("universal_z")
    body = G.implication(P.Eq(0, P.V(y)), P.Eq(P.V(y), 0))
    at_succ = P.S(P.V(z))
    instance = subst_proof(open_proof, t[1], at_succ)
    branch = G.implication_intro(P.Eq(0, at_succ), P.Eq(at_succ, 0), instance,
                                P.substitute(body, y, at_succ))
    universal = P.introduction(P.D(x, y, body), 0, z, "case", branch)
    add("zero_symmetry_universal_closure", universal,
        "Canonical D closure of (0=t)->(t=0); its zero instance is a theorem, so its ordinary reading yields the universal statement.")

    # A nonvacuous witness, used for a scope-corruption negative control.
    x, y, z = N.fresh("witness_x"), N.fresh("witness_y"), N.fresh("witness_z")
    matrix = G.guard(P.V(y), P.Eq(P.V(x), P.ONE))
    next_matrix = P.substitute(P.substitute(matrix, x, P.ONE), y, P.S(P.V(z)))
    premise = full_wrap(P.reflexivity(P.ONE, N.fresh("witness_refl")),
                        P.compute(next_matrix[1]), P.compute(next_matrix[2]))
    witness_proof = P.introduction(P.D(x, y, matrix), P.ONE, z, "progress", premise)
    add("guarded_nonvacuous_witness", witness_proof,
        "The introduced witness occurs in the guarded matrix.")

    # This administrative theorem demonstrates the orbit class itself.
    orbit = P.make_closure("orbit_n",
        P.Eq(P.V("orbit_n"), P.I(P.V("orbit_n"), P.ONE, "orbit_u", P.S(P.V("orbit_u")))),
        lambda k: N.chain(N.cong(P.hyp(P.Eq(k, P.I(k, P.ONE, "orbit_u", P.S(P.V("orbit_u"))))), P.S),
                          N.sym(P.compute(P.I(P.S(k), P.ONE, "orbit_u", P.S(P.V("orbit_u")))))),
        prefix=N.fresh("explicit_orbit"))
    add("administrative_orbit_closure", orbit,
        "Administrative Q closure with an unguarded orbit D and a used variable-source IH.",
        canonical=False)

    add("old_atomic_case_rejected", G.old_atomic_case(),
        "The old unguarded atomic case rule is unavailable after root-determined introduction.",
        expected=False, canonical=False)
    return cases

def emit(proof, global_scope=False):
    emitter = (GP.Emitter if global_scope else P.Emitter)()
    packet = emitter.packet(proof)
    return packet, emitter.trace

def canonical_validator():
    tree = ast.parse((ROOT / "code/strict_checker.py").read_text())
    nodes = [node for node in tree.body
             if isinstance(node, ast.FunctionDef) and node.name in {"term", "formula"}]
    env = {}
    exec(compile(ast.Module(body=nodes, type_ignores=[]), "<validator>", "exec"), env)
    return env["formula"]

def main():
    cases = ordinary_proofs()
    validate_goal = canonical_validator()
    manifest = []
    stored = {}
    for case in cases:
        row = {key: value for key, value in case.items() if key != "proof"}
        row["audit"] = proof_audit(case["proof"])
        if case["expected"]:
            assert not row["audit"]["defects"], row
        row["packets"] = {}
        for global_scope, label in [(False, "local"), (True, "global")]:
            packet, trace = emit(case["proof"], global_scope)
            if case["canonical_goal"]:
                assert validate_goal(packet[-1]), case["name"]
            filename = case["name"] + "_" + label + ".json"
            path = OUT / filename
            path.write_text(json.dumps(packet, separators=(",", ":")) + "\n")
            row["packets"][label] = {
                "path": str(path.relative_to(HERE)),
                "instructions": len(packet) - 1,
                "json_bytes": path.stat().st_size,
            }
            stored[(case["name"], label)] = (packet, trace)
        manifest.append(row)
        print(json.dumps({"generated": case["name"],
                          "instructions": row["packets"]["local"]["instructions"]}), flush=True)

    def add_raw(name, local, global_packet=None, expected=False, canonical=False, description=""):
        paths = {}
        for label, packet in [("local", local), ("global", global_packet or local)]:
            path = OUT / (name + "_" + label + ".json")
            path.write_text(json.dumps(packet, separators=(",", ":")) + "\n")
            paths[label] = {"path": str(path.relative_to(HERE)),
                            "instructions": max(0, len(packet) - 1),
                            "json_bytes": path.stat().st_size}
        manifest.append({"name": name, "expected": expected, "canonical_goal": canonical,
                         "description": description, "packets": paths})

    add_raw("false_equation", [[0, [0]]], canonical=True,
            description="No proof of the designated contradiction.")
    add_raw("unallocated_closed_parameter", [[-1, -1]],
            description="A free negative parameter cannot be introduced in a closed theorem.")
    add_raw("empty_input", [], description="Malformed empty certificate.")
    add_raw("malformed_instruction", [[0, 0, 0], [0, [0]]], canonical=True,
            description="An instruction must contain exactly four fields.")
    add_raw("null_goal", [None], description="Null is not a canonical formula.")
    mutations = {}
    for label in ("local", "global"):
        packet, trace = stored[("guarded_nonvacuous_witness", label)]
        packet = copy.deepcopy(packet)
        event = next(t for t in trace if t["rule"] == "DI")
        packet[event["packet_index"]][3] = -999999
        mutations[label] = packet
    add_raw("unallocated_DI_witness", mutations["local"], mutations["global"],
            canonical=True, description="The used witness is corrupted to an unavailable scope label.")
    mutations = {}
    for label in ("local", "global"):
        packet, trace = stored[("guarded_equation_induction", label)]
        packet = copy.deepcopy(packet)
        event = next(t for t in trace if t["rule"] == "DI" and t["mode"] == "progress")
        if label == "local":
            packet[event["packet_index"]][2] = []
        else:
            packet[event["packet_index"]][0] = []
        mutations[label] = packet
    add_raw("retired_mode_toggle", mutations["local"], mutations["global"], expected=True,
            canonical=True, description="Changing the retired mode field leaves root-selected atomic progress unchanged.")

    (ROOT / "evidence/manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    profiles = [
        ("byte", "checker_bytes.py", "local", False),
        ("AST", "checker.py", "local", False),
        ("readable", "readable_checker.py", "local", False),
        ("strict", "strict_checker.py", "local", True),
        ("token", "checker_tokens.py", "global", False),
    ]
    results = []
    for case in manifest:
        for label, filename, packet_kind, strict in profiles:
            expected = case["expected"] and (case["canonical_goal"] or not strict)
            packet_path = HERE / case["packets"][packet_kind]["path"]
            for optimized in (False, True):
                command = [sys.executable] + (["-O"] if optimized else []) + [str(ROOT / "code" / filename)]
                started = time.monotonic()
                try:
                    run = subprocess.run(command, input=packet_path.read_bytes(),
                                         capture_output=True, timeout=20)
                    accepted = run.returncode == 0 and run.stdout == b"ACCEPT\n"
                    result = {"case": case["name"], "profile": label,
                              "optimized": optimized, "expected": expected,
                              "accepted": accepted, "returncode": run.returncode,
                              "seconds": round(time.monotonic() - started, 3)}
                    if accepted != expected:
                        result["stderr_tail"] = run.stderr.decode(errors="replace")[-2500:]
                        result["stdout"] = run.stdout.decode(errors="replace")
                except subprocess.TimeoutExpired:
                    result = {"case": case["name"], "profile": label, "optimized": optimized,
                              "expected": expected, "accepted": False, "timeout": True,
                              "seconds": round(time.monotonic() - started, 3)}
                result["matched"] = result["accepted"] == expected and not result.get("timeout")
                results.append(result)
                if not result["matched"]:
                    print(json.dumps({"MISMATCH": result}), flush=True)
    summary = {
        "status": "finite executable validation, not proof-assistant verification",
        "cases": len(manifest), "runs": len(results),
        "matches": sum(row["matched"] for row in results),
        "mismatches": [row for row in results if not row["matched"]],
        "canonical_positive_cases": sum(c["expected"] and c["canonical_goal"] for c in manifest),
        "administrative_positive_cases": sum(c["expected"] and not c["canonical_goal"] for c in manifest),
        "negative_cases": sum(not c["expected"] for c in manifest),
        "results": results,
    }
    (ROOT / "evidence/validation.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({k: v for k, v in summary.items() if k != "results"}, indent=2))
    if summary["mismatches"]:
        raise SystemExit(1)

if __name__ == "__main__":
    main()
