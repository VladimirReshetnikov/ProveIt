"""Independent named certificates for the provisional forward-X kernel.

This producer is not imported by the checker. Every verdict is observed in a
fresh interpreter process, with and without Python optimization.
"""
import ast
import copy
import gzip
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

HERE = Path(__file__).resolve().parent
ONE = [0]
IDENTITY = 3
SUCC_UPDATE = [7]  # Two dummy slots below S; the actual state is slot 2.


def i0(seed, body=0):
    return [0, 0, seed, body], [[0, seed, body], seed]


def refl(term):
    p, equation = i0(term)
    return [p, p, 0, IDENTITY], [term, term]


def x(major, minor, template):
    return [major, minor, 0, template]


def decode_term(term, slots=(), parameters=None):
    """Standard-model decoder, independent of the checker's opener."""
    parameters = parameters or {}
    if isinstance(term, int):
        if term < 0:
            return parameters[term]
        if term < 3:
            return 0
        return slots[(term - 3) // 2]
    if len(term) == 1:
        return 1 + decode_term(term[0], (0, 0) + slots, parameters)
    if len(term) == 3:
        n = decode_term(term[0], (0,) + slots, parameters)
        value = decode_term(term[1], (0,) + slots, parameters)
        for _ in range(n):
            value = decode_term(term[2], (value,) + slots, parameters)
        return value
    return 0


cases = []


def add(name, proof, goal, accepted=True):
    cases.append({"name": name, "certificate": [proof, goal],
                  "expected_accept": accepted})


base, major_equation = i0(ONE)
source, target = major_equation
add("base_computation", base, major_equation)
rp, rg = refl(ONE)
add("derived_reflexivity", rp, rg)
add("reversed_replacement_symmetry", x(base, base, source),
    [target, source])

# Both a(z)=I(0,z;u.Su) and b(z)=z depend on the replaced input.
# Source minor: a(source)=b(source), obtained by I0.
# First X: b(source)=a(target). Second X: a(target)=b(target).
template_a = [0, 5, SUCC_UPDATE]
minor, minor_equation = i0(source, SUCC_UPDATE)
first = x(base, minor, template_a)
final = x(base, first, IDENTITY)
target_equation = [[0, target, SUCC_UPDATE], target]
add("transport_both_endpoints_dependent", final, target_equation)

# The substituted target itself has a genuine iterator-bound state.
inner = [ONE, ONE, 3]
base_inner, inner_equation = i0(inner)
inner_source, inner_target = inner_equation
minor_inner, _ = i0(inner_source, SUCC_UPDATE)
first_inner = x(base_inner, minor_inner, template_a)
final_inner = x(base_inner, first_inner, IDENTITY)
capture_goal = [[0, inner_target, SUCC_UPDATE], inner_target]
add("nested_iterator_capture_free", final_inner, capture_goal)

# Changing a protected state to the external hole changes H. Matching the
# old minor must now fail, even though both equations are true in N.
bad_template = [0, 5, [9]]
add("changed_bound_state_rejected", x(base, minor, bad_template),
    [source, [0, target, [9]]], False)
add("wrong_replacement_endpoint_rejected", final,
    [[0, target, SUCC_UPDATE], [target]], False)

step = [0, ONE, ONE, SUCC_UPDATE]
step_goal = [[[ONE], ONE, SUCC_UPDATE], [[ONE, ONE, SUCC_UPDATE]]]
add("successor_computation", step, step_goal)

# One witness-sensitive DI, its DE continuation, and ordinary QE.
d_goal = [[ONE, ONE]]
d_progress = [0, d_goal, 0, [0, 1]]
d_case = [0, d_goal, 0, [ONE, 1]]
add("equation_progress_intro", d_progress, d_goal)
add("equation_case_nonzero_witness", d_case, d_goal)
closure = [d_progress, 1, 0, 0]
closure_goal = [[ONE, ONE]] * 3
add("D_elimination_with_unused_witness", closure, closure_goal)
# The existential witness is actually used in QE and a computation, then
# removed from the conclusion. This catches export-before-floor-change bugs.
name_goal = [[[5, ONE, 7], ONE]]
name_intro = [0, name_goal, 0, [ONE, [0, -1, ONE, ONE]]]
name_base = [0, 0, ONE, -1]
name_qe = [1, name_base, [ONE], 0]
name_compute = [0, ONE, ONE, -1]
name_equation = x(name_compute, name_qe, IDENTITY)
name_reverse = x(name_equation, name_equation, ONE)
name_closed = x(name_reverse, name_reverse, IDENTITY)
add("D_elimination_uses_then_discharges_witness",
    [name_intro, name_closed, 0, 0], [ONE, ONE])
specialization = [closure, rp, [ONE], 0]
add("Q_elimination", specialization, [ONE, ONE])

# D binds the existential x in coordinate 5. A continuation may use its
# witness, but may not return a formula that still mentions it.
dx_goal = [[5, 5]]
dx_proof = [0, dx_goal, 0, [ONE, 1]]
add("existential_witness_intro", dx_proof, dx_goal)
add("escaping_DE_eigenparameter_rejected", [dx_proof, 1, 0, 0],
    [[-1, -1]] * 3, False)
add("future_DI_witness_rejected", [0, dx_goal, 0, [-1, 1]],
    dx_goal, False)
add("closed_false_goal_rejected", rp, [0, ONE], False)

rows = []
for case in cases:
    for optimized in (False, True):
        command = [sys.executable] + (["-O"] if optimized else [])
        command += [str(HERE / "forward_x.py")]
        result = subprocess.run(command, input=json.dumps(case["certificate"]),
                                text=True, capture_output=True, timeout=10)
        accepted = result.returncode == 0 and result.stdout == "ACCEPT\n"
        rows.append({"name": case["name"], "optimized": optimized,
                     "expected_accept": case["expected_accept"],
                     "observed_accept": accepted,
                     "match": accepted == case["expected_accept"]})
        if accepted != case["expected_accept"]:
            print(case["name"], optimized, result.returncode,
                  result.stdout, result.stderr)

equations_checked = 0
for case in cases:
    goal = case["certificate"][1]
    if case["expected_accept"] and len(goal) == 2:
        left, right = map(decode_term, goal)
        if left != right:
            raise AssertionError((case["name"], left, right))
        equations_checked += 1

source_text = (HERE / "forward_x.py").read_text()
normalized = ast.unparse(ast.parse(source_text)) + "\n"
metrics = {
    "normalized_bytes": len(normalized.encode()),
    "tokens": sum(t.type not in (
        tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
        tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT)
        for t in tokenize.generate_tokens(io.StringIO(normalized).readline)),
    "ast_nodes": sum(1 for _ in ast.walk(ast.parse(normalized))),
    "normalized_gzip9": len(gzip.compress(normalized.encode(),
                                          compresslevel=9, mtime=0)),
}
report = {"prototype_status": "finite-tested; requires metatheory audit",
          "cases": rows, "metrics": metrics,
          "standard_model_equations_checked": equations_checked,
          "passed": all(row["match"] for row in rows)}
(HERE / "forward_x_cases.json").write_text(json.dumps(cases, indent=2) + "\n")
(HERE / "forward_x_results.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({"passed": report["passed"], "expectations": len(rows),
                  "metrics": metrics}, indent=2))
if not report["passed"]:
    raise SystemExit(1)
