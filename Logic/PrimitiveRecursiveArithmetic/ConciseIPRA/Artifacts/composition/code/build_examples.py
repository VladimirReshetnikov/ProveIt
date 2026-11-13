"""Build small certificates exercising every primitive reference-kernel rule."""
import copy
import json
from pathlib import Path
import pointfree_checker as k


class Builder:
    def __init__(self):
        self.steps = []
        self.history = []

    def add(self, tag, context, goal, args=(), refs=()):
        node = [tag, context, goal, list(args), list(refs)]
        self.history.append(k.check_step(node, self.history))
        self.steps.append(node)
        return len(self.steps) - 1

    def axiom(self, tag, args, context=()):
        return self.add(tag, list(context), k.arithmetic(tag, args), args)

    def reflexive(self, p, context=()):
        i = self.axiom("J0", [p, k.ID, k.ID], context)
        return self.add("Post", list(context), k.eq(p, p), [k.ID], [i, i])


def main():
    out = Path(__file__).resolve().parent.parent / "examples"
    out.mkdir(exist_ok=True)
    b = Builder()
    for tag, args in [
        ("C0", [k.S]), ("CL", [k.S, k.ID]), ("CR", [k.S, k.ID]),
        ("CE", [k.ID]), ("P00", []), ("P0S", [k.ID]),
        ("PS", [k.L, k.R]), ("J0", [k.Z, k.ID, k.L + k.S]),
        ("JS", [k.L, k.Z, k.R, k.L + k.S])
    ]:
        b.axiom(tag, args)

    reflexivity = b.reflexive(k.ID)
    equation = k.eq(k.ID, k.ID)
    assumption = b.add("Hyp", [equation], equation)
    b.add("Sub", [], equation, [k.ID], [assumption, reflexivity])
    b.add("Sub", [], k.down(b.history[0][1], k.S), [k.S], [0])
    pair_result = k.eq(k.fork(k.ID, k.ID), k.fork(k.ID, k.ID))
    b.add("Pair", [], pair_result, [], [reflexivity, reflexivity])
    major = b.axiom("CL", [k.S, k.ID])
    p, q = b.history[major][1][1:]
    minor = b.reflexive(p)
    b.add("Transport", [], k.eq(q, q), [equation], [major, minor])

    e = k.eq(k.L, k.L)
    base = k.down(e, k.fork(k.L, k.R))
    step = k.down(e, k.fork(k.L + k.S, k.R))
    step_proof = b.reflexive(step[1], [base])
    ind_index = b.add("Ind", [], [1, k.ID, e], [], [step_proof])
    zero = k.down(e, k.fork(k.Z, k.ID))
    base_proof = b.reflexive(zero[1])
    b.add("QE", [], k.down(e, k.fork(k.Z + k.S + k.S, k.ID)),
          [k.Z + k.S + k.S], [ind_index, base_proof])

    qi_base = k.down(e, k.fork(k.Z, k.R))
    qi_step = k.down(e, k.fork(k.L + k.S, k.R))
    qi_premise = b.reflexive(qi_step[1], [qi_base])
    b.add("QI", [], [1, k.ID, e], [], [qi_premise])

    d = [2, k.ID, e]
    q = k.fork(k.Z, k.ID)
    di_base = k.down(e, k.fork(k.Z, k.R + q))
    di_step = k.down(e, k.fork(k.L + k.S, k.R + q))
    di_premise = b.reflexive(di_step[1], [di_base])
    d_proof = b.add("DI", [], d, [k.Z], [di_premise])
    opened = [1, k.fork(k.L, k.R), e]
    target = k.eq(k.Z, k.Z)
    de_branch = b.reflexive(k.R + k.Z, [opened])
    b.add("DE", [], target, [], [d_proof, de_branch])
    (out / "all_rules.json").write_text(json.dumps(b.steps, indent=2) + "\n")

    small = Builder()
    small.reflexive(k.Z)
    (out / "zero_reflexivity.json").write_text(json.dumps(small.steps, indent=2) + "\n")

    bad = {}
    x = copy.deepcopy(small.steps)
    x[-1][2] = k.eq(k.Z, k.Z + k.S)
    bad["false_zero_one"] = x
    x = copy.deepcopy(small.steps)
    x[0][4] = [0]
    bad["future_reference"] = x
    x = copy.deepcopy(small.steps)
    x[-1][4] = [-1, 0]
    bad["negative_reference"] = x
    x = copy.deepcopy(small.steps)
    x[0][3][0] = [True]
    bad["boolean_program_tag"] = x
    x = copy.deepcopy(small.steps)
    x[0][2][0] = False
    bad["boolean_formula_tag"] = x
    x = copy.deepcopy(small.steps)
    x[0][3][2] = [[5]]
    bad["malformed_iterator"] = x
    x = copy.deepcopy(small.steps)
    x[-1][1] = [k.eq(k.Z, k.Z + k.S)]
    bad["undischarged_assumption"] = x
    x = copy.deepcopy(b.steps)
    x[ind_index][2][2] = [1, k.ID, e]
    bad["non_equational_induction"] = x
    x = copy.deepcopy(b.steps)
    x[-1][4][1] = reflexivity
    bad["wrong_discharge_context"] = x
    x = copy.deepcopy(b.steps)
    x[8][2][2] += k.S
    bad["wrong_successor_computation"] = x
    x = copy.deepcopy(small.steps)
    x[0][0] = "TrustMe"
    bad["unrecognized_axiom"] = x
    x = copy.deepcopy(b.steps)
    sub = next(i for i, s in enumerate(x) if s[0] == "Sub" and len(s[4]) == 2)
    x[sub][4] = [x[sub][4][0]]
    bad["missing_substitution_premise"] = x
    for name, data in bad.items():
        (out / ("reject_" + name + ".json")).write_text(json.dumps(data) + "\n")
    print(json.dumps({"positive_steps": len(b.steps), "negative_examples": len(bad)}))


if __name__ == "__main__":
    main()
