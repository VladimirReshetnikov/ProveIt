"""Finite process tests for the forward global-replacement prototype."""
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import tokenize
import zlib

HERE = Path(__file__).resolve().parent
ONE = [0]
SUCC = [7]


def base(seed, body=0):
    return [0, [0, seed, body]], [[0, seed, body], seed]


def refl(term):
    p, _ = constant_step(term)
    return [p, p], [term, term]


def constant_step(term):
    """C_term=term by one allowed successor computation, also at term=0."""
    numeral_two = [ONE]
    wrapper = [numeral_two, ONE, term]
    return [0, [ONE, ONE, term]], wrapper


def symmetry(proof, source):
    rp, _ = refl(source)
    return [rp, proof]


def transitive(first, second, source):
    """From source=middle and middle=target derive source=target."""
    return [second, symmetry(first, source)]


def tree_size(tree):
    return 1 + sum(map(tree_size, tree)) if type(tree) is list else 1


def congruence(proof, source, target, context):
    """Selective congruence from a fresh oversized computation term.

    context is an untrusted Python producer, never an input to the checker.
    Its hole is represented by a sentinel only while computing the bound.
    """
    numeral = 0
    for _ in range(tree_size(context("HOLE")) + 1):
        numeral = [numeral]
    p_c, c_source = constant_step(source)
    p_kc, equation_kc = base(c_source, numeral)
    alias = equation_kc[0]
    p_ks = transitive(p_kc, p_c, alias)
    p_kt = transitive(p_ks, proof, alias)
    shared = context(alias)
    p_shared, _ = refl(shared)
    left = [p_ks, p_shared]
    right = [p_kt, p_shared]
    return [right, left], [context(source), context(target)]


def transport(major, source, target, minor, left_context, right_context):
    left, _ = congruence(major, source, target, left_context)
    right, _ = congruence(major, source, target, right_context)
    return [right, [left, minor]], [left_context(target), right_context(target)]


def escaping_name(term):
    """Intentionally invalid DE: return term=b with the witness b escaping."""
    goal = [[[5, term, 7], term]]
    step = [0, [-1, term, term]]
    introduction = [0, [goal, 0, [term, step]]]
    base_at_witness = [0, [0, term, -1]]
    specialize = [1, [base_at_witness, [ONE]]]
    computation = [0, [ONE, term, -1]]
    return [introduction, [computation, specialize]]


def used_and_discharged_name(term):
    introduction, equation = escaping_name(term)
    reverse = symmetry(equation, term)
    return [introduction, [reverse, reverse]]


cases = []


def add(name, p, a, accept=True):
    cases.append({"name": name, "certificate": [p, a], "accept": accept})


p, equation = base(ONE)
s, t = equation
add("I0", p, equation)
rp, ra = refl(ONE)
add("reflexivity", rp, ra)
add("symmetry_from_common_left", symmetry(p, s), [t, s])
add("root_common_left_join", [p, p], [t, t])

# Every source occurrence is replaced, including those in passive positions.
u = [s, s, s]
u_refl, _ = refl(u)
rewrite = [p, u_refl]
add("all_three_occurrences_replaced", rewrite, [u, [t, t, t]])
add("selective_replacement_is_not_primitive", rewrite,
    [u, [t, s, s]], False)

# A fresh oversized computation term makes this SELECTIVE congruence possible
# without any primitive template, path, mask, or existential witness rule.
selective, selective_goal = congruence(p, s, t, lambda z: [z, s, s])
add("oversized_alias_preserves_passive_occurrences", selective, selective_goal)

# Both endpoints depend on z, and the left endpoint also has a passive source
# occurrence in the update body. Direct replacement would change that body.
minor_both, _ = base(s, s)
both, both_goal = transport(p, s, t, minor_both,
                           lambda z: [0, z, s], lambda z: z)
add("transport_both_endpoints_and_passive_overlap", both, both_goal)

# Literal-zero sources are supported without any forbidden zero initializer:
# C_0=0 is computed at successor counter 2, and its symmetry gives 0=C_0.
p_zero, c_zero = constant_step(0)
zero_major = symmetry(p_zero, c_zero)
zero_congruence, zero_goal = congruence(zero_major, 0, c_zero,
                                      lambda z: [z, 0, 0])
add("oversized_alias_at_literal_zero_source", zero_congruence, zero_goal)

# The matched closed source and target have their own bound state. The
# occurrence sits beneath two genuine iterator binders. The surrounding
# coordinate 5 denotes the outer state, not part of the matched source.
inner = [ONE, ONE, 3]
p_inner, inner_equation = base(inner)
s_inner, t_inner = inner_equation
u_inner = [ONE, ONE, [0, 5, s_inner]]
u_inner_refl, _ = refl(u_inner)
capture_proof = [p_inner, u_inner_refl]
capture_rhs = [ONE, ONE, [0, 5, t_inner]]
add("closed_replacement_under_two_binders", capture_proof,
    [u_inner, capture_rhs])
add("surrounding_bound_state_must_not_change", capture_proof,
    [u_inner, [ONE, ONE, [0, 3, t_inner]]], False)
bound_congruence, bound_goal = congruence(
    p_inner, s_inner, t_inner, lambda z: [ONE, ONE, [0, 5, z]])
add("oversized_alias_congruence_under_two_binders", bound_congruence, bound_goal)

# Replacing a root does not descend into the replacement. If it did, this
# source/target pair would expand forever: target contains source.
loop_source = ONE
loop_target = [0, ONE, 0]
backwards = symmetry(p, s)
one_refl, _ = refl(ONE)
add("replacement_target_is_not_rewritten", [backwards, one_refl],
    [ONE, loop_target])

step = [0, [ONE, ONE, SUCC]]
step_goal = [[[ONE], ONE, SUCC], [[ONE, ONE, SUCC]]]
add("IS", step, step_goal)
d_goal = [[ONE, ONE]]
d_progress = [0, [d_goal, 0, [0, 1]]]
d_cases = [0, [d_goal, 0, [ONE, 1]]]
add("DI_progress", d_progress, d_goal)
add("DI_cases", d_cases, d_goal)
closure = [d_progress, 1]
closure_goal = [[ONE, ONE]] * 3
add("DE_unused_witness", closure, closure_goal)
add("DE_uses_then_discharges_witness", used_and_discharged_name(ONE),
    [ONE, ONE])
add("QE", [closure, [rp, [ONE]]], [ONE, ONE])
dx_goal = [[5, 5]]
dx = [0, [dx_goal, 0, [ONE, 1]]]
add("DI_named_witness", dx, dx_goal)
add("DE_eigenparameter_escape", [dx, 1], [[-1, -1]] * 3, False)
add("DI_future_witness", [0, [dx_goal, 0, [-1, 1]]], dx_goal, False)
add("DI_non_unary_goal", [0, [[ONE, ONE], 0, [0, 1]]],
    [ONE, ONE], False)
add("false_closed_goal", rp, [0, ONE], False)

# A shared missing-image/replacement-source sentinel collapses two escaped
# existential witnesses to the SAME Python function object. This complete
# false-proof attack is rejected by the corrected opener, not merely blocked
# by a final JSON mismatch. No function object is present in the input.
p_zero_for_attack, zero_term_for_attack = constant_step(0)
one_name = symmetry(escaping_name(ONE), ONE)
zero_name = symmetry(escaping_name(zero_term_for_attack), zero_term_for_attack)
zero_equals_one = [one_name, zero_name]
one_equals_zero = [p_zero_for_attack, zero_equals_one]
sentinel_attack = symmetry(one_equals_zero, ONE)
add("distinct_sentinels_block_closed_false_proof", sentinel_attack,
    [0, ONE], False)

rows = []
for case in cases:
    for optimized in (False, True):
        command = [sys.executable] + (["-O"] if optimized else [])
        command += [str(HERE / "checker.py")]
        run = subprocess.run(command, input=json.dumps(case["certificate"]),
                             text=True, capture_output=True, timeout=10)
        observed = run.returncode == 0 and run.stdout == "ACCEPT\n"
        row = {"name": case["name"], "optimized": optimized,
               "expected": case["accept"], "observed": observed,
               "match": observed == case["accept"]}
        rows.append(row)
        if not row["match"]:
            print(row, run.stderr)

normalized = ast.unparse(ast.parse((HERE / "checker.py").read_text())) + "\n"
metrics = {
    "bytes": len(normalized.encode()),
    "tokens": sum(t.type not in (
        tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
        tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT)
        for t in tokenize.generate_tokens(io.StringIO(normalized).readline)),
    "ast": sum(1 for _ in ast.walk(ast.parse(normalized))),
    "gzip9": len(gzip.compress(normalized.encode(), compresslevel=9, mtime=0)),
}
report = {"status": "prototype; inherited raw codec; finite tests only",
          "passed": all(r["match"] for r in rows),
          "metrics": metrics, "expectations": rows}
mutations = []
mutant = (HERE / "checker.py").read_text().replace('t=None, d=0', 't=c, d=0')
with tempfile.TemporaryDirectory() as temporary:
    mutant_path = Path(temporary) / "sentinel_collision.py"
    mutant_path.write_text(mutant)
    for optimized in (False, True):
        command = [sys.executable] + (["-O"] if optimized else [])
        command += [str(mutant_path)]
        run = subprocess.run(command, input=json.dumps([sentinel_attack, [0, ONE]]),
                             text=True, capture_output=True, timeout=10)
        accepted = run.returncode == 0 and run.stdout == "ACCEPT\n"
        mutations.append({"name": "shared_sentinel_accepts_closed_false_proof",
                          "optimized": optimized, "expected_accept": True,
                          "observed_accept": accepted, "match": accepted})
report["mutation_controls"] = mutations
report["passed"] = report["passed"] and all(m["match"] for m in mutations)
control = subprocess.run([sys.executable, str(HERE / "control" / "test_forward_x.py")],
                         text=True, capture_output=True, timeout=60)
if control.returncode:
    raise RuntimeError(control.stdout + control.stderr)
report["forward_x_control"] = json.loads(control.stdout)
report["passed"] = report["passed"] and report["forward_x_control"]["passed"]
provenance = {
    "python": sys.version,
    "zlib_build": zlib.ZLIB_VERSION,
    "zlib_runtime": zlib.ZLIB_RUNTIME_VERSION,
    "normalization": "ast.unparse(ast.parse(source)) + one newline",
    "gzip": "gzip.compress(bytes, compresslevel=9, mtime=0)",
    "interpretation": "same-session forward implementations; not a matched ablation",
    "programs": [],
}
for relative in ("checker.py", "control/forward_x.py"):
    path = HERE / relative
    raw = path.read_bytes()
    normalized_program = ast.unparse(ast.parse(raw)) + "\n"
    encoded = normalized_program.encode()
    compressed = gzip.compress(raw, compresslevel=9, mtime=0)
    path.with_suffix(path.suffix + ".gz").write_bytes(compressed)
    provenance["programs"].append({
        "path": relative,
        "raw_sha256": hashlib.sha256(raw).hexdigest(),
        "normalized_sha256": hashlib.sha256(encoded).hexdigest(),
        "raw_bytes": len(raw),
        "normalized_bytes": len(encoded),
        "tokens": sum(t.type not in (
            tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
            tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT)
            for t in tokenize.generate_tokens(io.StringIO(normalized_program).readline)),
        "ast_nodes": sum(1 for _ in ast.walk(ast.parse(normalized_program))),
        "raw_gzip9_bytes": len(compressed),
        "normalized_gzip9_bytes": len(gzip.compress(encoded, compresslevel=9, mtime=0)),
    })
(HERE / "metrics.json").write_text(json.dumps(provenance, indent=2) + "\n")
(HERE / "cases.json").write_text(json.dumps(cases, indent=2) + "\n")
(HERE / "results.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({"passed": report["passed"], "count": len(rows),
                  "metrics": metrics}, indent=2))
if not report["passed"]:
    raise SystemExit(1)
