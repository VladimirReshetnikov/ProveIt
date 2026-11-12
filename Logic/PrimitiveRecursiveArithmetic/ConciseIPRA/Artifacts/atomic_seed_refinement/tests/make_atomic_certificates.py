"""Untrusted certificate producer. The standalone kernel rechecks its output."""
from pathlib import Path
import copy
import json

import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "code"))
import atomic_seed_checker as kernel

ROOT = Path(__file__).resolve().parent
Z = ["z"]


def v(index):
    return ["v", index]


def s(term):
    return ["s", term]


def iterator(counter, seed, update):
    return ["i", counter, seed, update]


def eq(left, right):
    return ["=", left, right]


def refl(term):
    update = kernel.shift(term)
    left = iterator(s(Z), s(Z), update)
    computation = ["step", Z, s(Z), update]
    return ["tr", left, term, v(0), term, computation, computation]


def reflexive_packet():
    matrix = eq(v(0), v(0))
    return ["intro", matrix, Z, refl(s(v(0)))]


def symmetry(source, target, equality):
    return ["tr", source, target, kernel.shift(source), target, equality, equality]


def identity_iterator_packet():
    """An equation induction whose hypothesis is genuinely used."""
    matrix = eq(iterator(v(0), Z, s(v(0))), v(0))
    previous = iterator(v(0), Z, s(v(0)))
    current = iterator(s(v(0)), Z, s(v(0)))
    step = ["step", v(0), Z, s(v(0))]
    backwards = symmetry(current, s(previous), step)
    branch = ["tr", previous, v(0), s(v(0)), current, ["hyp", 0], backwards]
    return ["intro", matrix, Z, branch]


def zero_computation(seed, update):
    """Derive arbitrary I(0,seed;update)=seed with no zero rule."""
    goal = eq(iterator(Z, seed, update), seed)
    matrix = eq(v(0), v(0))
    # Add the fresh witness b, then the Q-bound y, outside update's u.
    seed_b = kernel.shift(seed)
    update_b = kernel.shift(update, 1, 1)
    update_b_y = kernel.shift(update_b, 1, 1)
    body = eq(iterator(Z, v(0), update_b_y), v(0))
    branch = ["qe", body, seed_b, ["hyp", 0], refl(Z)]
    return ["open", matrix, goal, reflexive_packet(), branch]


def document(goal, proof):
    return {"goal": goal, "proof": proof}


def main():
    directory = ROOT / "certificates"
    directory.mkdir(exist_ok=True)
    cases = []

    def add(name, goal, proof, accepted, reason):
        value = document(goal, proof)
        if accepted:
            kernel.check(value)
        path = directory / (name + ".json")
        path.write_text(json.dumps(value, separators=(",", ":")) + "\n")
        cases.append({"file": "certificates/" + path.name,
                      "accepted": accepted, "reason": reason})

    one = s(Z)
    two = s(one)
    atom = eq(Z, Z)
    add("reflexivity_zero", atom, refl(Z), True,
        "Reflexivity derives from successor computation and crossed transport.")
    add("reflexivity_compound", eq(two, two), refl(two), True,
        "The reflexivity derivation does not rely on atomicity of its term.")
    add("reflexive_closure_packet", ["d", eq(v(0), v(0))],
        reflexive_packet(), True, "DI proves the reflexive closure packet.")
    add("nested_logical_binders", ["d", ["d", eq(v(0), v(0))]],
        ["intro", ["d", eq(v(0), v(0))], Z, reflexive_packet()], True,
        "Case introduction under a second paired binder preserves formula structure.")

    induction_matrix = eq(iterator(v(0), Z, s(v(0))), v(0))
    add("induction_used_hypothesis", ["d", induction_matrix],
        identity_iterator_packet(), True,
        "The step transports the actual induction hypothesis I(z,0;S)=z.")
    three = s(two)
    identity_goal = eq(iterator(three, Z, s(v(0))), three)
    identity_branch = ["qe", induction_matrix, three, ["hyp", 0], refl(Z)]
    identity_proof = ["open", induction_matrix, identity_goal,
                      identity_iterator_packet(), identity_branch]
    add("induction_specialized", identity_goal, identity_proof, True,
        "The derived progressive closure is opened and specialized after its zero base.")

    # The raw zero alias selects CASES although its normal form is zero.
    # This branch genuinely uses the case assumption 0=1. Replacing the
    # witness by literal zero changes it to I(z,0;0)=1 and must reject.
    case_matrix = eq(iterator(v(0), Z, Z), one)
    current_case = iterator(s(v(0)), Z, Z)
    case_step = ["step", v(0), Z, Z]
    case_reverse = symmetry(current_case, Z, case_step)
    case_branch = ["tr", Z, one, v(0), current_case, ["hyp", 0], case_reverse]
    case_proof = ["intro", case_matrix, iterator(Z, Z, Z), case_branch]
    add("raw_zero_alias_cases", ["d", case_matrix], case_proof, True,
        "A nonliteral raw zero alias selects cases; its case assumption is used.")
    literal_case_proof = copy.deepcopy(case_proof)
    literal_case_proof[2] = Z
    add("reject_changed_raw_mode", ["d", case_matrix], literal_case_proof, False,
        "Literal-zero witness selects progress and cannot reuse the case-only branch.")

    seed = one
    update = s(v(0))
    goal = eq(iterator(Z, seed, update), seed)
    proof = zero_computation(seed, update)
    add("zero_compound_seed", goal, proof, True,
        "The seed S0 is not atomic, so normalization alone does not erase this iterator.")

    seed = iterator(two, one, s(v(0)))
    update = iterator(s(v(0)), v(0), iterator(v(0), v(1), s(v(0))))
    goal_nested = eq(iterator(Z, seed, update), seed)
    proof_nested = zero_computation(seed, update)
    add("zero_nested_binders", goal_nested, proof_nested, True,
        "The update has nested iterator binders and uses both an inner and an outer variable.")

    # A Q-body with an equation under another D: its normalization must retain
    # the logical constructors while contracting only the indicated iterator.
    nested_body = ["d", eq(iterator(Z, v(0), v(0)), v(0))]
    nested_matrix = ["q", nested_body]
    # This is only a syntax/normalization artifact; its theorem is obtained by
    # reflexive zero computation at a term with a nested iterator body above.
    (ROOT.parent / "evidence/normalization_examples.json").write_text(json.dumps({
        "raw_formula": nested_matrix,
        "normal_formula": kernel.normalize(nested_matrix),
        "compound_zero_goal_raw": goal,
        "compound_zero_goal_normal": kernel.normalize(goal),
        "substitution_noncommutation": {
            "raw_template": iterator(Z, v(0), v(0)),
            "image": one,
            "normalize_after_substitution": kernel.normalize(
                kernel.substitute(iterator(Z, v(0), v(0)), [one])),
            "substitute_after_normalization": kernel.normalize(
                kernel.substitute(kernel.normalize(iterator(Z, v(0), v(0))), [one]))
        }
    }, indent=2) + "\n")

    step = ["step", Z, Z, s(v(0))]
    add("successor_zero_seed", eq(iterator(one, Z, s(v(0))), one), step,
        True, "The primary theory retains successor computation at every seed, including zero.")

    # The crucial raw-body metadata cannot be replaced by its normal form.
    erased = copy.deepcopy(proof)
    erased[4][1] = eq(v(0), v(0))
    add("reject_erased_qe_body", goal, erased, False,
        "Prematurely normalizing QE metadata changes the target to seed=seed.")
    add("reject_zero_equals_one", eq(Z, one), refl(Z), False,
        "A genuine proof of 0=0 cannot certify 0=1.")
    add("reject_wrong_zero_value", eq(iterator(Z, one, s(v(0))), two),
        zero_computation(one, s(v(0))), False,
        "Arbitrary zero computation returns the seed, not a successor of the seed.")

    escape = ["open", eq(v(0), v(0)), eq(v(0), v(0)),
              reflexive_packet(), refl(v(0))]
    add("reject_open_eigenvariable_escape", atom, escape, False,
        "The exported raw formula mentions a variable outside the outer scope.")
    bad_witness = ["intro", eq(v(0), v(0)), v(0), refl(s(v(0)))]
    add("reject_future_intro_witness", ["d", eq(v(0), v(0))],
        bad_witness, False, "The introduction witness is not in the outer scope.")

    negative_hyp = copy.deepcopy(proof)
    negative_hyp[4][3] = ["hyp", -1]
    add("reject_negative_hypothesis_index", goal, negative_hyp, False,
        "Python negative indexing is not a proof rule.")
    boolean_hyp = copy.deepcopy(proof)
    boolean_hyp[4][3] = ["hyp", False]
    add("reject_boolean_hypothesis_index", goal, boolean_hyp, False,
        "Boolean values do not count as numerical indices.")

    bad_bound = ["step", Z, one, v(1)]
    add("reject_update_scope_escape", eq(iterator(one, one, v(0)), one),
        bad_bound, False, "A step update has only its accumulator variable in a closed proof.")

    add("reject_primitive_zero_rule", eq(iterator(Z, one, s(v(0))), one),
        ["zero", one, s(v(0))], False,
        "The candidate has no primitive zero-computation rule.")
    (ROOT / "atomic_cases.json").write_text(json.dumps(cases, indent=2) + "\n")
    print(json.dumps({"certificates": len(cases),
                      "positive": sum(c["accepted"] for c in cases)}))


if __name__ == "__main__":
    main()
