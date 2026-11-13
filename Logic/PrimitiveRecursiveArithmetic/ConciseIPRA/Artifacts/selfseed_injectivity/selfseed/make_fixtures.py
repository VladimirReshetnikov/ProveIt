"""Untrusted construction of concrete proof/attack fixtures; not a kernel dependency."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DEST = ROOT / "fixtures"
DEST.mkdir(exist_ok=True)
Z = ["0"]
O = ["S", Z]
B = ["b", 0]
F = lambda n, h=B: ["F", n, h]
E = lambda a, b: ["=", a, b]
V = lambda name: ["v", name]
A = lambda name, *args: ["axiom", name, *args]
R = lambda term: ["refl", term]
items = []


def case(name, goal, proof, expected=True, control=None, purpose=""):
    payload = {"goal": goal, "proof": proof}
    (DEST / (name + ".json")).write_text(json.dumps(payload, indent=2) + "\n")
    items.append({"name": name, "expected_without": expected,
                  "expected_with": expected if control is None else control,
                  "purpose": purpose})


case("F_zero_uses_body", E(F(Z, ["S", B]), ["S", O]), A("F0", ["S", B]), purpose="The F zero axiom substitutes zero into a nonconstant update.")
case("F_successor_uses_state", E(F(O), F(Z)), A("FS", Z, B), purpose="The F successor axiom substitutes the recursive value into its state slot.")
reflection = ["and", ["imp", E(["e", Z, O], O), E(Z, O)], ["imp", E(Z, O), E(["e", Z, O], O)]]
case("equality_test_reflection", reflection, A("reflection", Z, O))
case("equality_test_range", ["or", E(["e", Z, O], Z), E(["e", Z, O], O)], A("range", Z, O))
case("equality_test_reflexive", E(["e", Z, Z], O), ["impE", ["andR", A("reflection", Z, Z)], R(Z)])
case("separation", ["imp", E(Z, O), ["false"]], A("separation"))

identity = ["allI", "x", R(V("x"))]
case("universal_introduction", ["all", E(B, B)], identity)
case("universal_elimination", E(O, O), ["allE", identity, O])
case("implication_and_conjunction", ["imp", E(Z, O), ["and", E(Z, O), E(Z, Z)]], ["impI", E(Z, O), ["andI", ["hyp", 0], R(Z)]])
case("disjunction_elimination", E(Z, Z), ["orE", ["orL", R(Z), E(Z, Z)], ["hyp", 0], ["hyp", 0]])
case("right_disjunction_introduction", ["or", E(Z, O), E(Z, Z)], ["orR", E(Z, O), R(Z)])
case("explosion_under_assumption", ["imp", ["false"], E(Z, O)], ["impI", ["false"], ["falseE", E(Z, O), ["hyp", 0]]])

exists_zero = ["exI", E(B, Z), Z, R(Z)]
case("existential_introduction", ["ex", E(B, Z)], exists_zero)
w = V("w")
symmetry = ["replace", ["hyp", 0], E(B, w), R(w)]
exists_elimination = ["exE", exists_zero, "w", ["replace", ["hyp", 0], E(Z, B), symmetry]]
case("existential_elimination_uses_witness", E(Z, Z), exists_elimination, purpose="Both equality substitutions use the existential assumption; the witness is absent from the exported result.")

invariant = E(F(B), O)
step = ["replace", ["hyp", 0], E(F(["S", V("z")]), B), A("FS", V("z"), B)]
induction = ["allI", "n", ["ind", invariant, V("n"), A("F0", B), "z", step]]
case("equation_induction_used_hypothesis", ["all", invariant], induction, purpose="Proves forall n, F(n;v.v)=1. The successor proof uses the actual induction hypothesis as its equality major.")
case("induction_specialization", E(F(["S", O]), O), ["allE", induction, ["S", O]])
side_induction = ["impI", E(Z, O), ["allI", "n", ["ind", invariant, V("n"), A("F0", B), "z", ["replace", ["hyp", 1], E(F(["S", V("z")]), B), A("FS", V("z"), B)]]]]
case("equation_induction_side_assumptions", ["imp", E(Z, O), ["all", invariant]], side_induction, purpose="The fixed side context is retained; the induction hypothesis is index 1.")

# Capture-sensitive F body: its b1 refers to the outer all binder, while b0 is its state.
parametric_body = ["e", ["b", 0], V("p")]
parametric = ["allI", "p", A("F0", parametric_body)]
parametric_goal = ["all", E(F(Z, ["e", ["b", 0], ["b", 1]]), ["S", ["e", Z, B]])]
case("recursor_binder_capture_control", parametric_goal, parametric, purpose="Checks independent state and outer parameter indices under the F binder.")

case("reject_false_equality", E(Z, O), R(Z), False)
case("reject_wrong_F_zero_endpoint", E(F(Z, ["S", B]), O), A("F0", ["S", B]), False)
case("reject_wrong_epsilon_value", E(["e", Z, Z], ["S", O]), ["impE", ["andR", A("reflection", Z, Z)], R(Z)], False)
case("reject_hypothesis_out_of_scope", E(Z, O), ["hyp", 0], False)
case("reject_negative_hypothesis_index", ["imp", E(Z, O), E(Z, O)], ["impI", E(Z, O), ["hyp", -1]], False)
case("reject_boolean_hypothesis_index", ["imp", E(Z, O), E(Z, O)], ["impI", E(Z, O), ["hyp", False]], False)
case("reject_public_free_parameter", E(V("x"), V("x")), R(V("x")), False)
case("reject_unbound_term_index", E(Z, Z), ["refl", B], False)
case("reject_boolean_bound_index", ["all", E(["b", True], ["b", True])], identity, False)
case("reject_compound_induction", ["imp", E(Z, Z), E(Z, Z)], ["ind", ["imp", E(Z, Z), E(Z, Z)], Z, ["impI", E(Z, Z), ["hyp", 0]], "z", ["hyp", 0]], False)
case("reject_induction_missing_step", ["all", invariant], ["allI", "n", ["ind", invariant, V("n"), A("F0", B), "z", A("F0", B)]], False)
case("reject_induction_existing_eigenparameter", ["all", invariant], ["allI", "z", ["ind", invariant, V("z"), A("F0", B), "z", step]], False)
case("reject_unknown_rule", E(Z, O), ["trust", E(Z, O)], False)
case("reject_extra_proof_field", E(Z, Z), ["refl", Z, "ignored"], False)

# If exE omitted its nonescape check, these two independent witnesses could
# both leak under the same name w, and equality replacement would prove 0=1.
leak0 = ["exE", exists_zero, "w", ["hyp", 0]]
leak1 = ["exE", ["exI", E(B, O), O, R(O)], "w", ["hyp", 0]]
case("reject_existential_witness_collision", E(Z, O), ["replace", leak0, E(B, O), leak1], False, purpose="An actual false-equality attack if the exE escape condition is deleted.")
# Omitting allI freshness would generalize a parameter occurring in a side assumption.
bad_universal = ["allI", "x", ["impI", E(V("x"), Z), ["allI", "x", ["hyp", 0]]]]
false_reverse = ["allE", ["impE", ["allE", bad_universal, Z], R(Z)], O]
case("reject_universal_side_assumption_capture", E(Z, O), ["replace", false_reverse, E(B, O), R(O)], False, purpose="An actual false-equality attack if allI freshness is deleted.")

case("control_only_primitive_injectivity", ["imp", E(["S", Z], ["S", O]), E(Z, O)], A("injectivity", Z, O), False, True, purpose="The old primitive certificate is accepted only by the matched control; the new theorem has a derived proof, not this primitive tag.")
(DEST / "index.json").write_text(json.dumps(items, indent=2) + "\n")
print(len(items))
