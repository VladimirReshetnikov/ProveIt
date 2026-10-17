"""Recover editable AX emission and measure an uncalibrated PSC experiment.

The published program and the public MIT-0 backend remain unchanged.  Macro
expansion of AX is independently compared with the published symbolic spec
before a new theory row is compiled.  All generated machines go to an external
scratch directory.  This is NOT a verified consistency machine or a state bound.
"""
from __future__ import annotations

import argparse
import ast
import hashlib
import importlib
import itertools
import json
from pathlib import Path
import sys

from recover_wade_dag import (COMMIT, ROOT, SNAPSHOT, REGISTERS, SOURCE_SHA256,
                             builder_from_dag, git_bytes, parse_dag)
from pairing_backend_experiment import execute_helper


MACROS = {166: "a", 121: "b", 168: "c", 171: "zero", 177: "one",
          119: "imp", 181: "rel", 182: "eq", 180: "all",
          218: "not", 178: "and", 183: "exists", 176: "read_b",
          158: "read_u", 208: "move_u", 192: "copy_c",
          131: "gate", 211: "restore_c_copy", 197: "a_to_b"}
TAIL = [192, 131, 211, 197, 131]


def Imp(a, b): return ("imp", a, b)
def Rel(a, b): return ("rel", a, b)
def Eq(a, b): return ("eq", a, b)
def All(a, b): return ("all", a, b)
def Not(a): return Imp(a, 1)
def And(a, b): return Not(Imp(a, Not(b)))
def Ex(a, b): return Not(All(a, Not(b)))
def Or(a, b): return Imp(Not(a), b)
def Iff(a, b): return And(Imp(a, b), Imp(b, a))


def expand(nodes, root):
    if root in MACROS:
        return [root]
    result = []
    for edge in nodes[root]:
        kind, value = edge.split()
        if kind != "ENode":
            raise ValueError(f"nonformula leaf at {root}: {edge}")
        result += expand(nodes, int(value))
    return result


def symbolic(program, initial_b="h"):
    """Execute stack constructors independently of the register implementation."""
    stack, b, u, events = ["old_top"], initial_b, None, []
    constructors = {119: Imp, 181: Rel, 182: Eq, 180: All,
                    178: And, 183: Ex}
    for macro in program:
        if macro in (166, 121, 168, 171, 177):
            stack.append({166: "a", 121: b, 168: "c", 171: 0, 177: 1}[macro])
        elif macro in constructors:
            right, left = stack.pop(), stack.pop()
            stack.append(constructors[macro](left, right))
        elif macro == 218:
            stack[-1] = Not(stack[-1])
        elif macro == 176:
            events.append(("read_b", len(stack)))
            b = "b"
        elif macro == 158:
            u = "u"
        elif macro == 208:
            if stack[-1] != 0 or u != "u":
                raise ValueError("u leaf does not load into a zero top")
            stack[-1], u = u, None
        elif macro in TAIL:
            events.append((MACROS[macro], len(stack)))
        else:
            raise ValueError(f"unknown macro {macro}")
    return stack, events


def published_spec():
    """Load just pure AX formula definitions, with symbolic primitive codes.

    This parses the pinned reference as data; no import, IO or enumerator body
    from that file is run.  The independent AX stack executor supplies the other
    side of the comparison.
    """
    path = SNAPSHOT / "ZF/m254/tools/logic/spec.py"
    source = path.read_bytes()
    digest = hashlib.sha256(source).hexdigest()
    if digest != "7d96deff6994315b714579c74d10efeb65374694d476c802c727356e258578e9":
        raise ValueError("published symbolic spec differs from the pinned version")
    tree = ast.parse(source)
    functions = [n for n in tree.body if isinstance(n, ast.FunctionDef)
                 and n.name not in ("_code", "enum_step")]
    module = ast.Module(body=functions, type_ignores=[])
    namespace = {"F": 1, "_code": lambda tag, a, b:
                 (("imp", "rel", "all", "eq")[tag], a, b)}
    exec(compile(module, str(path), "exec"), namespace)
    return namespace, digest


def old_contract(nodes):
    program = expand(nodes, 1)
    if program[:4] != [166, 121, 180, 176] or program[-5:] != TAIL:
        raise ValueError("published AX prefix/tail changed")
    stack, events = symbolic(program)
    spec, digest = published_spec()
    expected = ["old_top"] + spec["ax_rows"]("a", "h", "b", "c", "u")
    expected.append(spec["bundle"]("a", "b", "c"))
    if stack != expected:
        for i, (actual, wanted) in enumerate(zip(stack, expected)):
            if actual != wanted:
                raise ValueError(f"published AX symbolic row {i} differs")
        raise ValueError("published AX symbolic row count differs")
    # Each completed pushed formula starts with a scalar push; find exactly the
    # prefix leaving the nine logical rows and no part of the theory bundle.
    logical = expected[:-1]
    cuts = [i for i in range(1, len(program) - 4)
            if symbolic(program[:i])[0] == logical]
    if len(cuts) != 1:
        raise ValueError(f"ambiguous logical/theory AX boundary: {cuts}")
    return program, program[:cuts[0]], {
        "macro_count": len(program), "logical_prefix_macros": cuts[0],
        "published_spec_sha256": digest,
        "GEN_and_eight_logical_rows_exact": True,
        "old_CP_GIC_vacuity_bundle_exact": True,
        "old_cleanup_gate_macros_exact": program[-5:] == TAIL,
        "rows_above_old_top": len(stack) - 1,
        "events": events}


def emit(formula):
    if formula == "a": return [166]
    if formula == "b": return [121]
    if formula == "c": return [168]
    if formula == "u": return [171, 158, 208]
    if formula == 0: return [171]
    if formula == 1: return [177]
    # Recognize the published derived constructors before ordinary implication.
    if (isinstance(formula, tuple) and formula[0] == "imp"
            and formula[2] == 1):
        inner = formula[1]
        if (isinstance(inner, tuple) and inner[0] in ("imp", "all")
                and isinstance(inner[2], tuple) and inner[2][0] == "imp"
                and inner[2][2] == 1):
            macro = 178 if inner[0] == "imp" else 183
            return emit(inner[1]) + emit(inner[2][1]) + [macro]
        return emit(inner) + [218]
    kind, left, right = formula
    macro = {"imp": 119, "rel": 181, "eq": 182, "all": 180}[kind]
    return emit(left) + emit(right) + [macro]


def theory_rows():
    phi, c = "c", "c"
    subset = All(0, Imp(Rel(0, 1), Rel(0, c)))
    bounded = All(0, Ex(c, All(1, Imp(phi, subset))))
    closed = All(0, Imp(Or(Eq(0, 1), Rel(0, c)),
                        All(1, Imp(phi, Rel(1, c)))))
    supported = All(1, Imp(Rel(1, c), Ex(0, phi)))
    psc = Imp(bounded, All(1, Ex(c, And(closed, supported))))
    ext = All(0, All(1, Imp(All(c, Iff(Rel(c, 0), Rel(c, 1))), Eq(0, 1))))
    vr = Imp(Rel("a", "b"), All(c, Rel("a", "b")))
    ve = Imp(Eq("a", "b"), All(c, Eq("a", "b")))
    return And(ext, psc), And(vr, ve)


def equality_free_rows(profile_control=False, reordered=False, dual=False,
                       order=None, components=None, grouping=None):
    spec, _ = published_spec()
    old_rows = spec["ax_rows"]("a", "h", "b", "c", "u")
    if dual:
        old_rows[3] = Imp("b", All("a", Ex("a", "b")))
    # GEN must read the old cache; the other retained schemas read the new one.
    logical = [166, 121, 180, 176]
    selected = order or ((1, 7, 5, 3) if reordered else (1, 3, 5, 7))
    for index in selected:
        logical += emit(old_rows[index])
    C = spec["bundle_C"]("a", "b", "c")
    G = spec["bundle_G"]("a", "b", "c")
    vr = Imp(Rel("a", "b"), All("c", Rel("a", "b")))
    if profile_control:
        profile = Imp(All("c", Iff(Rel("c", "a"), Rel("c", "b"))),
                      All("c", Iff(Rel("a", "c"), Rel("b", "c"))))
        bundle = And(And(C, G), And(vr, profile))
    else:
        bundle = And(vr, And(C, G)) if reordered else And(And(C, G), vr)
    if components is not None:
        x, y, z = [{"C": C, "G": G, "V": vr}[name] for name in components]
        bundle = And(And(x, y), z) if grouping == 0 else And(x, And(y, z))
    program = logical + emit(bundle) + TAIL
    actual, _ = symbolic(program)
    expected = ["old_top"] + [old_rows[i] for i in (0, *selected)] + [bundle]
    if actual != expected:
        raise ValueError("equality-free row reconstruction differs")
    if 182 in program or any(row[0] == "eq" for row in (C, G, bundle)):
        raise ValueError("equality constructor unexpectedly retained")
    return program


def lower_program(builder, nodes, program, mode, shared=False, base3=False):
    program = reuse_published_subsequences(nodes, program)
    newroot = scalar_reify(builder, program, f"AX_{mode}().0")
    for i, sequence in enumerate(builder.sequences):
        if i != 1:
            sequence.seq = tuple(newroot if x == 1 else x for x in sequence.seq)

    def reexpand(q):
        if not isinstance(q, int) or q in MACROS:
            return [q]
        return [leaf for child in builder.sequences[q].seq for leaf in reexpand(child)]

    before = reexpand(newroot)
    if shared:
        builder.breakout_common_subsequences()
    builder.reduce_to_cons()
    builder.name_sequences()
    if reexpand(newroot) != before:
        raise ValueError("common-subsequence sharing changed macro expansion")
    if base3:
        if builder.sequences[118].seq[0] != 156:
            raise ValueError("unexpected old multiply-four helper")
        # Only the formula pair scaler changes.  The proof/stack Cantor
        # pairing helper162 and list representation remain unchanged.
        builder.sequences[118].seq = (157, builder.sequences[118].seq[1])
    return builder


def scalar_reify(builder, program, name):
    """Give the emitter its own editable source while retaining helper DAGs."""
    root = builder.add_sequence(program)
    builder.sequences[root].name = name
    return root


def reuse_published_subsequences(nodes, program):
    """Minimum-token parse using unchanged, symbolically expanded AX helpers.

    This only shares exact contiguous macro lists.  It cannot move gates or
    variable reads, and the full expansion is checked after reconstruction.
    Nested new register programs act as barriers to sharing.
    """
    patterns = [(expand(nodes, q), q) for q in range(1, 115)
                if q not in MACROS]
    best = [None] * (len(program) + 1)
    best[-1] = []
    for i in reversed(range(len(program))):
        choices = [[program[i]] + best[i + 1]]
        for pattern, q in patterns:
            j = i + len(pattern)
            if program[i:j] == pattern:
                choices.append([q] + best[j])
        best[i] = min(choices, key=lambda xs: (len(xs), repr(xs)))
    reconstructed = []
    for token in best[0]:
        reconstructed += (expand(nodes, token) if isinstance(token, int)
                          and token not in MACROS and token in nodes else [token])
    if reconstructed != program:
        raise ValueError("subsequence reuse changed the expanded program")
    return best[0]


def build_variant(backend, nodes, names, logical, mode):
    builder = builder_from_dag(backend, nodes, names)
    builder.sequence_lookup = {s.seq: i for i, s in enumerate(builder.sequences)}
    regs = [builder.reg(name) for name in REGISTERS]
    if mode == "reemit_old":
        program = expand(nodes, 1)
    elif mode == "fixed_PSC_separate_vacuity":
        theory, vacuity = theory_rows()
        # A local c>=2 check preserves c in register3.  Registers6/7 start0;
        # macro192 duplicates c there, a loop restores register3 from7.
        copy_restore = [192, builder.while_decnz(regs[7], regs[3].inc)]
        clear_top = builder.while_decnz(regs[1], ())
        local_gate = [copy_restore,
                      builder.if_not_decnz(regs[6], clear_top),
                      builder.if_not_decnz(regs[6], clear_top),
                      builder.while_decnz(regs[6], ())]
        program = logical + emit(theory) + local_gate + emit(vacuity) + TAIL
    elif mode in ("raw_equality_free_C_G", "profile_equality_free_C_G",
                  "raw_equality_free_C_G_reordered_shared",
                  "raw_equality_free_C_G_shared_base3",
                  "raw_equality_free_C_G_shared_dual_base3"):
        program = equality_free_rows(mode.startswith("profile"),
                                     "shared" in mode, "dual" in mode)
    else:
        raise ValueError(mode)
    return lower_program(builder, nodes, program, mode,
                         "shared" in mode, "base3" in mode)


def local_gate_contract(backend, nodes, names):
    """Exercise the exact emitted register operations on both sides of c>=2."""
    builder = builder_from_dag(backend, nodes, names)
    builder.sequence_lookup = {s.seq: i for i, s in enumerate(builder.sequences)}
    r = [builder.reg(name) for name in REGISTERS]
    clear = builder.while_decnz(r[1], ())
    root = builder.add_sequence([
        192, builder.while_decnz(r[7], r[3].inc),
        builder.if_not_decnz(r[6], clear), builder.if_not_decnz(r[6], clear),
        builder.while_decnz(r[6], ())])
    builder.reduce_to_cons()
    count = 0
    for c in range(24):
        for top in (0, 1, 3, 17):
            v = [5, top, 7, c, 11, 13, 0, 0, 19]
            wanted = v.copy()
            if c < 2: wanted[1] = 0
            result = execute_helper(builder, root, v)
            if result != ("normal",) or v != wanted:
                raise ValueError(f"local gate contract failed for {c}, {top}: {v}")
            count += 1
    return count


def finite_model_contract():
    """Compare fixed-binder AST to direct PSC in all irreflexive 1/2 models.

    The irreflexivity assumption is essential here: the runtime's code1 is
    Rel(0,0), used as falsity by the old calculus. This regression does not
    discharge the required proof-search/comparison-theory calibration.
    """
    theory, _ = theory_rows()
    cases = 0
    for n in (1, 2):
        domain = range(n)
        edges = [(x, y) for x in domain for y in domain if x != y]
        for relation_bits in range(1 << len(edges)):
            relation = {edge for i, edge in enumerate(edges) if relation_bits >> i & 1}
            member = lambda x, y: (x, y) in relation
            subset = lambda x, y: all(not member(z, x) or member(z, y) for z in domain)
            ext = all(not all(member(z, x) == member(z, y) for z in domain) or x == y
                      for x in domain for y in domain)
            for phi_bits in range(1 << (n * n)):
                phi = lambda x, y: bool(phi_bits >> (x*n+y) & 1)
                bounded = all(any(all(not phi(x, y) or subset(y, b) for y in domain)
                                  for b in domain) for x in domain)
                closed = lambda r, c: all(
                    not (x == r or member(x, c)) or all(
                        not phi(x, y) or member(y, c) for y in domain) for x in domain)
                supported = lambda c: all(not member(y, c) or any(phi(x, y) for x in domain)
                                          for y in domain)
                direct = ext and (not bounded or all(any(closed(r, c) and supported(c)
                                                        for c in domain) for r in domain))

                def evaluate(formula, env):
                    if formula == "c": return phi(env[0], env[1])
                    if formula == 1: return member(env[0], env[0])
                    kind, a, b = formula
                    if kind == "imp": return not evaluate(a, env) or evaluate(b, env)
                    if kind == "rel": return member(env[a], env[b])
                    if kind == "eq": return env[a] == env[b]
                    if kind == "all":
                        return all(evaluate(b, env | {a: x}) for x in domain)
                    raise ValueError(kind)

                if evaluate(theory, {0: 0, 1: 0, "c": 0}) != direct:
                    raise ValueError(f"fixed-binder semantics differ in model {n}, {relation_bits}, {phi_bits}")
                cases += 1
    return cases


def base3_helper_contract(backend, nodes, names, logical):
    builder = build_variant(backend, nodes, names, logical,
                            "raw_equality_free_C_G_shared_dual_base3")
    pair = lambda a, b: (a+b)*(a+b+1)//2+b
    cases = 0
    for a in range(5):
        for b in range(5):
            for rest in (0, 1, 5):
                for root, tag in ((119, 0), (181, 1), (180, 2)):
                    v = [7, b, pair(a, rest), 0, 11, 13, 0, 0, 19]
                    wanted = [7, 3*pair(a, b)+tag, rest, 0, 11, 13, 0, 0, 19]
                    result = execute_helper(builder, root, v)
                    if result != ("normal",) or v != wanted:
                        raise ValueError(f"base3 helper contract failed: {a}, {b}, {rest}, {root}, {v}")
                    cases += 1
    return cases


def dual_scheme_contract():
    """Check contraposition identity in every Boolean matrix through size4.

    With ordinary false, old(not p) is literally equivalent to dual(p), without
    assuming the old scheme valid. The runtime's relative-falsity atom and
    quantifier capture still require a separate calculus/comparison bridge;
    this Boolean regression does not supply that proof.
    """
    cases = 0
    for n in range(1, 5):
        for bits in range(1 << n):
            p = [bool(bits >> i & 1) for i in range(n)]
            # A one-variable matrix here may have other parameters fixed.
            for current in p:
                old_not_p = not (any([all(not x for x in p)] * n)) or not current
                dual_p = not current or all([any(p)] * n)
                if old_not_p != dual_p:
                    raise ValueError("dual rho6 Boolean identity failed")
                cases += 1
    return cases


def search_orders(backend, nodes, names):
    distribution, best, minimizers = {}, None, []
    for order in itertools.permutations((1, 3, 5, 7)):
        for components in itertools.permutations(("C", "G", "V")):
            for grouping in (0, 1):
                program = equality_free_rows(dual=True, order=order,
                                             components=components, grouping=grouping)
                builder = builder_from_dag(backend, nodes, names)
                builder.sequence_lookup = {s.seq: i for i, s in enumerate(builder.sequences)}
                lower_program(builder, nodes, program, "search", shared=True, base3=True)
                builder.generate()
                builder.tm.gc()
                cost = len({q for q, _ in builder.tm.states})
                distribution[cost] = distribution.get(cost, 0) + 1
                descriptor = {"rho_order": [9-i for i in order],
                              "components": components,
                              "right_associated": bool(grouping)}
                if best is None or cost < best:
                    best, minimizers = cost, [descriptor]
                elif cost == best:
                    minimizers.append(descriptor)
    return {"cases": sum(distribution.values()), "minimum_working_states": best,
            "cost_distribution": distribution, "minimizers": minimizers}


def measure(backend, nodes, names, scratch, search=False):
    program, logical, contract = old_contract(nodes)
    theory, vacuity = theory_rows()
    if symbolic(emit(theory))[0] != ["old_top", theory]:
        raise ValueError("new theory RPN emitter failed symbolic comparison")
    if symbolic(emit(vacuity), "b")[0] != ["old_top", vacuity]:
        raise ValueError("preserved vacuity emitter failed symbolic comparison")
    results = []
    for mode in ("original", "reemit_old", "fixed_PSC_separate_vacuity",
                 "raw_equality_free_C_G", "profile_equality_free_C_G",
                 "raw_equality_free_C_G_reordered_shared",
                 "raw_equality_free_C_G_shared_base3",
                 "raw_equality_free_C_G_shared_dual_base3"):
        builder = (builder_from_dag(backend, nodes, names) if mode == "original"
                   else build_variant(backend, nodes, names, logical, mode))
        builder.generate()
        builder.tm.gc()
        states = {q for q, _ in builder.tm.states}
        output = scratch / f"AX-{mode}.tm"
        builder.tm.save(str(output))
        results.append({"variant": mode, "working_states": len(states),
                        "framework_states": sum(q[0].isdigit() for q in states),
                        "decision_states": sum(not q[0].isdigit() for q in states),
                        "transition_rows": len(builder.tm.states),
                        "missing_transition_rows": [[q, bit] for q in sorted(states)
                            for bit in ("0", "1") if (q, bit) not in builder.tm.states],
                        "equality_helper_reachable": any(q.startswith("weq(") for q in states),
                        "table_sha256": hashlib.sha256(output.read_bytes()).hexdigest()})
    result = {"upstream_commit": COMMIT, "old_AX_symbolic_contract": contract,
            "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "pinned_backend_and_DAG_sha256": SOURCE_SHA256,
            "candidate252_recipe": {
                "logical_rows_after_GEN": ["rho8", "rho2", "rho4", "dual_rho6"],
                "theory_bundle": "membership_vacuity AND (C AND G)",
                "dual_rho6": "b -> All(a, Exists(a, b))",
                "formula_tags": {"Imp": "3P", "Rel": "3P+1", "All": "3P+2"},
                "proof_and_stack_Cantor_pairing_unchanged": True,
                "original_freshness_gate_c_ne_a_b_retained": True,
                "common_subsequence_extraction_before_binary_lowering": True},
            "local_c_ge_2_gate_register_contract_cases": local_gate_contract(backend, nodes, names),
            "fixed_binder_irreflexive_finite_model_cases": finite_model_contract(),
            "base3_constructor_register_contract_cases": base3_helper_contract(backend, nodes, names, logical),
            "dual_rho6_boolean_identity_cases": dual_scheme_contract(),
            "new_theory_constructor_macros": len(emit(theory)),
            "preserved_vacuity_constructor_macros": len(emit(vacuity)),
            "new_theory_symbolic_RPN_roundtrip_exact": True,
            "vacuity_original_freshness_gate_retained": True,
            "variants": results,
            "Lean_theory_calibration_proved": False,
            "Lean_compiler_simulation_proved": False,
            "new_ZFC_machine_or_state_bound_claimed": False}
    if search:
        result["dual_base3_order_search"] = search_orders(backend, nodes, names)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scratch", type=Path, required=True)
    parser.add_argument("--output-evidence", type=Path)
    parser.add_argument("--search-orders", action="store_true")
    args = parser.parse_args()
    scratch = args.scratch.resolve()
    if scratch == ROOT or ROOT in scratch.parents or scratch == Path("/"):
        parser.error("scratch must be outside the repository and not filesystem root")
    scratch.mkdir(parents=True, exist_ok=True)
    for name in ("TMBuilder.py", "tm.py", "tmdb.py", "LICENSE.wade"):
        (scratch / name).write_bytes(git_bytes(None, "ZF/generator/" + name))
    nodes, names = parse_dag(git_bytes(None, "ZF/m254/coq/prog/Dag254.v").decode())
    sys.path.insert(0, str(scratch))
    backend = importlib.import_module("TMBuilder")
    encoded = json.dumps(measure(backend, nodes, names, scratch, args.search_orders), indent=2, sort_keys=True) + "\n"
    if args.output_evidence:
        args.output_evidence.write_text(encoded)
    print(encoded, end="")


if __name__ == "__main__":
    main()
