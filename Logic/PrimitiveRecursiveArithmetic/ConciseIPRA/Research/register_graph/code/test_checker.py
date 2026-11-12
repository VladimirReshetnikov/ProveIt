"""Build and run closed theorem certificates and adversarial controls.

Only checker.py belongs to the trusted checker.  This file is an untrusted
certificate producer and regression harness.  Each fixture is run through
the public JSON/stdin interface, both normally and with Python -O.
"""

import ast
import copy
import gzip
import hashlib
import io
import json
import pathlib
import subprocess
import sys
import tokenize

import checker


HERE = pathlib.Path(__file__).resolve().parent
FIXTURES = HERE / "certificates"
FIXTURES.mkdir(exist_ok=True)


def V(x):
    return ["v", x]


def Z():
    return ["0"]


def J(n, body, i="i", r="r"):
    return ["j", n, i, r, body]


def S(x):
    return J(x, Z())


def One():
    return S(Z())


def Eq(a, b):
    return ["=", a, b]


def Imp(a, b):
    return ["imp", a, b]


def And(a, b):
    return ["and", a, b]


def Or(a, b):
    return ["or", a, b]


def All(x, a):
    return ["all", x, a]


def Ex(x, a):
    return ["ex", x, a]


def Bot():
    return ["bot"]


def Iff(a, b):
    return And(Imp(a, b), Imp(b, a))


def N(rule, conclusion, **fields):
    return dict(rule=rule, conclusion=conclusion, **fields)


def Hyp(index, goal):
    return N("hyp", goal, index=index)


def Refl(t):
    return N("refl", Eq(t, t))


def theorem(parameters, assumptions, conclusion, proof):
    for assumption in reversed(assumptions):
        conclusion = Imp(assumption, conclusion)
        proof = N("imp_intro", conclusion, proof=proof)
    for parameter in reversed(parameters):
        conclusion = All(parameter, conclusion)
        proof = N("all_intro", conclusion, eigen=parameter, proof=proof)
    return {"goal": conclusion, "proof": proof}


positive = {}
negative = {}


def add(label, parameters, assumptions, goal, proof):
    positive[label] = theorem(parameters, assumptions, goal, proof)


truth = Eq(Z(), Z())
false_equation = Eq(Z(), One())
a, b, c = V("a"), V("b"), V("c")

add("identity", [], [truth], truth, Hyp(0, truth))
add("reflexivity", ["a"], [], Eq(a, a), Refl(a))
add("j_zero", ["a"], [], Eq(J(Z(), a), One()), N("j_zero", Eq(J(Z(), a), One())))

# A nonconstant body uses both bound coordinates; the two replacements in
# the step instruction must be simultaneous.
n = V("n")
body = J(V("i"), V("r"), "p", "q")
previous = J(n, body)
instruction = J(n, previous, "p", "q")
left = Eq(J(S(n), body), b)
right = Or(And(Eq(instruction, Z()), Eq(b, S(previous))), Eq(instruction, S(b)))
graph = Iff(left, right)
add("step_both_coordinates", ["n", "b"], [], graph,
    N("j_step", graph, counter=n, index="i", state="r", body=body, output=b))

# Here r is a free counter parameter and also the name of the state binder.
# Substituting i -> r must not subsequently replace the newly inserted r.
previous = J(V("r"), V("i"))
left = Eq(J(S(V("r")), V("i")), Z())
right = Or(And(Eq(V("r"), Z()), Eq(Z(), S(previous))), Eq(V("r"), One()))
graph = Iff(left, right)
add("step_simultaneous", ["r"], [], graph,
    N("j_step", graph, counter=V("r"), index="i", state="r", body=V("i"), output=Z()))

sep = Imp(false_equation, Bot())
add("separation", [], [], sep, N("separation", sep))
add("ex_falso", [], [Bot()], false_equation, N("absurd", false_equation, proof=Hyp(0, Bot())))
add("implication_application", [], [Imp(truth, truth), truth], truth,
    N("imp_elim", truth, implication=Hyp(0, Imp(truth, truth)), argument=Hyp(1, truth)))

conjunction = And(truth, Eq(One(), One()))
add("conjunction_intro", [], [], conjunction,
    N("and_intro", conjunction, left=Refl(Z()), right=Refl(One())))
add("conjunction_left", [], [conjunction], truth,
    N("and_left", truth, proof=Hyp(0, conjunction)))
add("conjunction_right", [], [conjunction], Eq(One(), One()),
    N("and_right", Eq(One(), One()), proof=Hyp(0, conjunction)))
disjunction = Or(truth, Eq(One(), One()))
add("disjunction_left", [], [], disjunction, N("or_left", disjunction, proof=Refl(Z())))
add("disjunction_right", [], [], disjunction, N("or_right", disjunction, proof=Refl(One())))
add("disjunction_elim", [], [disjunction], truth,
    N("or_elim", truth, disjunction=Hyp(0, disjunction),
      left=Hyp(1, truth), right=Refl(Z())))

universal = All("x", Eq(V("x"), V("x")))
universal_proof = N("all_intro", universal, eigen="e", proof=Refl(V("e")))
add("universal_elim", [], [], truth,
    N("all_elim", truth, universal=universal_proof, term=Z()))
existential = Ex("x", Eq(V("x"), V("x")))
add("existential_intro", [], [], existential,
    N("ex_intro", existential, witness=Z(), proof=Refl(Z())))
add("existential_elim", [], [existential], truth,
    N("ex_elim", truth, existential=Hyp(0, existential), eigen="e", proof=Refl(Z())))

equation = Eq(a, b)
symmetry = Eq(b, a)
add("equality_transport", ["a", "b"], [equation], symmetry,
    N("eq_elim", symmetry, equality=Hyp(0, equation), premise=Refl(a),
      variable="hole", motive=Eq(V("hole"), a)))

# Genuine induction: arbitrary retained step information is used to derive
# an equation at an arbitrary target, including the induction hypothesis.
invariant = Eq(J(V("x"), V("a")), J(V("x"), V("b")))
base_equation = Eq(J(Z(), a), J(Z(), b))
progression = All("y", Imp(Eq(J(V("y"), a), J(V("y"), b)),
                            Eq(J(S(V("y")), a), J(S(V("y")), b))))
current = Eq(J(V("e"), a), J(V("e"), b))
following = Eq(J(S(V("e")), a), J(S(V("e")), b))
specialized = Imp(current, following)
step_proof = N("imp_elim", following,
               implication=N("all_elim", specialized,
                             universal=Hyp(1, progression), term=V("e")),
               argument=Hyp(2, current))
target = Eq(J(c, a), J(c, b))
add("contextual_equation_induction", ["a", "b", "c"], [base_equation, progression], target,
    N("induction", target, variable="x", equation=invariant, term=c, eigen="e",
      base=Hyp(0, base_equation), step=step_proof))

# Capture avoidance for ordinary quantifiers.  The fresh spelling is
# intentionally different from the checker's chosen alpha-renaming.
source = All("x", Ex("y", Eq(V("x"), V("y"))))
instance = Ex("renamed", Eq(V("y"), V("renamed")))
add("capture_avoiding_quantifier", ["y"], [source], instance,
    N("all_elim", instance, universal=Hyp(0, source), term=V("y")))

# Capture avoidance in the two-binder numerical operator, not just formulas.
source = All("x", Eq(J(Z(), V("x")), J(Z(), V("x"))))
renamed = J(Z(), V("i"), "counter", "state")
instance = Eq(renamed, renamed)
add("capture_avoiding_j", ["i"], [source], instance,
    N("all_elim", instance, universal=Hyp(0, source), term=V("i")))

# A real arithmetic theorem: a positive command loads its predecessor.
body = S(a)
result = J(S(n), body)
previous = J(n, body)
left = Eq(result, a)
right = Or(And(Eq(S(a), Z()), Eq(a, S(previous))), Eq(S(a), S(a)))
graph = Iff(left, right)
axiom = N("j_step", graph, counter=n, index="i", state="r", body=body, output=a)
load = N("imp_elim", left,
         implication=N("and_right", Imp(right, left), proof=axiom),
         argument=N("or_right", right, proof=Refl(S(a))))
add("constant_positive_load", ["a", "n"], [], left, load)

# Increment under its actual command premise, directly from the graph.
body = V("r")
previous = J(n, body)
output = S(previous)
left = Eq(J(S(n), body), output)
zero_command = Eq(previous, Z())
right = Or(And(zero_command, Eq(output, output)), Eq(previous, S(output)))
graph = Iff(left, right)
axiom = N("j_step", graph, counter=n, index="i", state="r", body=body, output=output)
increment = N("imp_elim", left,
              implication=N("and_right", Imp(right, left), proof=axiom),
              argument=N("or_left", right,
                         proof=N("and_intro", right[1],
                                 left=Hyp(0, zero_command), right=Refl(output))))
add("conditional_increment", ["n"], [zero_command], left, increment)

# A nontrivial closed consequence: the graph supplies numerical coverage.
w = J(One(), a)
previous = J(Z(), a)
left = Eq(w, w)
right = Or(And(Eq(a, Z()), Eq(w, S(previous))), Eq(a, S(w)))
graph = Iff(left, right)
axiom = N("j_step", graph, counter=Z(), index="i", state="r", body=a, output=w)
cases = N("imp_elim", right,
          implication=N("and_left", Imp(left, right), proof=axiom), argument=Refl(w))
coverage = Or(Eq(a, Z()), Eq(a, S(w)))
cover = N("or_elim", coverage, disjunction=cases,
          left=N("or_left", coverage,
                 proof=N("and_left", Eq(a, Z()), proof=Hyp(0, right[1]))),
          right=N("or_right", coverage, proof=Hyp(0, right[2])))
add("functional_coverage", ["a"], [], coverage, cover)

# Rejection controls. Some target formulas are themselves theorems, but
# their submitted derivations violate the exact intended proof system.
bad = copy.deepcopy(positive["contextual_equation_induction"])
node = bad["proof"]
while node["rule"] in ("all_intro", "imp_intro"):
    node = node["proof"]
node["equation"] = And(node["equation"], truth)
negative["compound_induction"] = bad

bad = copy.deepcopy(positive["reflexivity"])
bad["proof"]["proof"]["conclusion"] = false_equation
negative["nonreflexive_refl"] = bad
negative["bare_false_hyp"] = {"goal": false_equation, "proof": Hyp(0, false_equation)}

# Unsound universal introduction if an eigenvariable is allowed in context.
goal = All("a", Imp(Eq(a, Z()), All("x", Eq(V("x"), Z()))))
proof = N("all_intro", goal, eigen="a",
          proof=N("imp_intro", goal[2],
                  proof=N("all_intro", goal[2][2], eigen="a", proof=Hyp(0, Eq(a, Z())))))
negative["universal_eigen_escape"] = {"goal": goal, "proof": proof}

# Existential elimination must not identify its witness with a free parameter.
some_zero = Ex("x", Eq(V("x"), Z()))
goal = All("a", Imp(some_zero, Eq(a, Z())))
proof = N("all_intro", goal, eigen="a",
          proof=N("imp_intro", goal[2],
                  proof=N("ex_elim", Eq(a, Z()), existential=Hyp(0, some_zero),
                          eigen="a", proof=Hyp(1, Eq(a, Z())))))
negative["existential_eigen_escape"] = {"goal": goal, "proof": proof}

# A newly opened existential witness must not be universally generalized.
goal = Imp(some_zero, All("x", Eq(V("x"), Z())))
proof = N("imp_intro", goal,
          proof=N("ex_elim", goal[2], existential=Hyp(0, some_zero), eigen="a",
                  proof=N("all_intro", goal[2], eigen="a", proof=Hyp(1, Eq(a, Z())))))
negative["existential_then_false_generalization"] = {"goal": goal, "proof": proof}

# Naive textual substitution would capture the free a, producing a false
# self-disequality existential from a true inequality-existence premise.
source = All("x", Ex("a", Imp(Eq(V("x"), a), Bot())))
captured = Ex("a", Imp(Eq(a, a), Bot()))
goal = Imp(source, All("a", captured))
proof = N("imp_intro", goal,
          proof=N("all_intro", goal[2], eigen="a",
                  proof=N("all_elim", captured, universal=Hyp(0, source), term=a)))
negative["quantifier_capture"] = {"goal": goal, "proof": proof}

bad = copy.deepcopy(positive["capture_avoiding_j"])
node = bad["proof"]["proof"]["proof"]
node["conclusion"] = Eq(J(Z(), V("i")), J(Z(), V("i")))
negative["j_binder_capture"] = bad

bad = copy.deepcopy(positive["step_both_coordinates"])
node = bad["proof"]["proof"]["proof"]
node["conclusion"][1][1][2] = One()
negative["wrong_step_graph"] = bad

bad = copy.deepcopy(positive["j_zero"])
bad["proof"]["proof"]["conclusion"][1][1] = One()
negative["wrong_base_counter"] = bad

negative["undeclared_free_variable"] = {"goal": Eq(a, a), "proof": Refl(a)}
negative["malformed_formula"] = {"goal": ["=", Z()], "proof": Refl(Z())}
negative["malformed_term"] = {"goal": Eq(["0", 5], Z()), "proof": Refl(Z())}
negative["repeated_j_binders"] = {"goal": Eq(J(Z(), Z(), "u", "u"), One()),
                                     "proof": N("j_zero", Eq(J(Z(), Z(), "u", "u"), One()))}
negative["unknown_rule"] = {"goal": truth, "proof": N("oracle", truth)}
negative["extra_rule_field"] = {"goal": truth, "proof": N("refl", truth, bypass=True)}
negative["boolean_hyp_index"] = theorem([], [truth], truth, Hyp(False, truth))
negative["negative_hyp_index"] = theorem([], [truth], truth, Hyp(-1, truth))
negative["float_hyp_index"] = theorem([], [truth], truth, Hyp(0.0, truth))

bad = copy.deepcopy(positive["equality_transport"])
node = bad["proof"]
while node["rule"] in ("all_intro", "imp_intro"):
    node = node["proof"]
node["variable"] = "a"
negative["motive_variable_not_fresh"] = bad

bad = copy.deepcopy(positive["reflexivity"])
bad["goal"] = false_equation
negative["advertised_goal_changed"] = bad

raw_negative = {
    "invalid_json": "{\"goal\":",
    "trailing_json": json.dumps(positive["identity"]) + " {}",
    "duplicate_json_key": '{"goal":["bot"],"goal":["bot"],"proof":{}}',
    "nonstandard_nan": '{"goal":NaN,"proof":{}}',
    "nonstandard_infinity": '{"goal":Infinity,"proof":{}}',
    "huge_integer": '{"goal":' + "1" * 5000 + ',"proof":{}}',
    "nonobject_certificate": "[]",
}


def rules_used(value):
    result = set()
    if isinstance(value, dict):
        if "rule" in value:
            result.add(value["rule"])
        for child in value.values():
            result |= rules_used(child)
    elif isinstance(value, list):
        for child in value:
            result |= rules_used(child)
    return result


def main():
    expected_rules = {"hyp", "refl", "j_zero", "j_step", "separation", "eq_elim",
                      "imp_intro", "imp_elim", "and_intro", "and_left", "and_right",
                      "or_left", "or_right", "or_elim", "all_intro", "all_elim",
                      "ex_intro", "ex_elim", "absurd", "induction"}
    observed_rules = set().union(*(rules_used(value) for value in positive.values()))
    if observed_rules != expected_rules:
        raise RuntimeError("positive fixture rule coverage is incomplete")
    records = []
    cases = [(label, json.dumps(value, indent=2) + "\n", True) for label, value in positive.items()]
    cases += [(label, json.dumps(value, indent=2) + "\n", False) for label, value in negative.items()]
    cases += [(label, value, False) for label, value in raw_negative.items()]
    for label, payload, should_accept in cases:
        suffix = ".txt" if label in raw_negative else ".json"
        (FIXTURES / (label + suffix)).write_text(payload)
        for optimize in (False, True):
            command = [sys.executable] + (["-O"] if optimize else []) + [str(HERE / "checker.py")]
            run = subprocess.run(command, input=payload, text=True, capture_output=True, timeout=10)
            accepted = run.returncode == 0 and run.stdout.strip() == "ACCEPT"
            rejected = run.returncode == 1 and run.stdout.startswith("REJECT:") and not run.stderr
            passed = accepted if should_accept else rejected
            records.append({"case": label, "optimized_python": optimize,
                            "expected": "ACCEPT" if should_accept else "REJECT",
                            "passed": passed, "returncode": run.returncode,
                            "stdout": run.stdout.strip(), "stderr": run.stderr.strip()})
    source = (HERE / "checker.py").read_bytes()
    normalized = (ast.unparse(ast.parse(source.decode())) + "\n").encode()
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.INDENT,
               tokenize.DEDENT, tokenize.NEWLINE, tokenize.NL, tokenize.COMMENT}
    significant = sum(token.type not in ignored for token in tokenize.generate_tokens(io.StringIO(normalized.decode()).readline))
    metrics = {"python": sys.version.split()[0], "source_bytes": len(source),
               "source_gzip9_bytes": len(gzip.compress(source, compresslevel=9, mtime=0)),
               "normalized_bytes": len(normalized),
               "normalized_gzip9_bytes": len(gzip.compress(normalized, compresslevel=9, mtime=0)),
               "significant_tokens": significant,
               "ast_nodes": sum(1 for _ in ast.walk(ast.parse(normalized.decode()))),
               "sha256": hashlib.sha256(source).hexdigest(),
               "counting_note": "All checker code, including docstrings, validation, substitution, alpha equivalence, JSON parser, and driver, is counted; tests and certificate producer are excluded."}
    (HERE / "metrics.json").write_text(json.dumps(metrics, indent=2) + "\n")
    (HERE / "validation.json").write_text(json.dumps({"positive_cases": len(positive),
        "negative_cases": len(negative) + len(raw_negative), "executions": len(records),
        "passed": sum(record["passed"] for record in records),
        "rule_families_exercised": sorted(observed_rules), "results": records}, indent=2) + "\n")
    print(json.dumps({"positive_cases": len(positive), "negative_cases": len(negative) + len(raw_negative),
                      "executions": len(records), "passed": sum(r["passed"] for r in records),
                      "metrics": metrics}, indent=2))
    failures = [record for record in records if not record["passed"]]
    if failures:
        print(json.dumps(failures, indent=2))
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
