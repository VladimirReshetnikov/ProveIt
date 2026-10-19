#!/usr/bin/env python3
"""Generate and independently replay finite Hilbert proofs for the KS repairs.

The replay kernel checks only explicit instances of the listed schemas, MP,
and generalization of an already proved theorem. It never trusts deduction
theorem calls made by the generator. Formula/index metavariables are formal
parameters, not object-language variables. These certificates are logical
lemmas, not a verified binary machine or a proof assistant endpoint.

Usage: python3 formalism_proofs.py [--check-only] [--output DIRECTORY]
"""
import argparse
from collections import Counter
from functools import cache
import hashlib
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


F = "F"


def I(a, b): return ("I", a, b)
def Q(i, a): return ("Q", i, a)
def Eq(i, j): return ("Eq", i, j)
def N(a): return I(a, F)
def Conj(a, b): return N(I(a, N(b)))
def K(a, b): return I(a, I(b, a))
def S(a, b, c): return I(I(a, I(b, c)), I(I(a, b), I(a, c)))
def P(a, b): return I(I(I(a, b), a), a)
def DNE(a): return I(N(N(a)), a)
def Q4(i, a): return I(Q(i, a), Q(i, Q(i, a)))
def R1(i, j): return N(Q(i, N(Eq(i, j))))
def R2(i, a, b): return I(Q(i, I(a, b)), I(Q(i, a), Q(i, b)))
def R6(i, a): return I(N(Q(i, N(Q(i, a)))), a)
def L(a, b, c, u): return I(I(I(c, u), a), I(I(a, c), I(b, c)))


SCHEMAS = dict(K=K, S=S, P=P, DNE=DNE, Q4=Q4, R1=R1, R2=R2, R6=R6)


def pretty(f):
    if isinstance(f, str): return f
    if f[0] == "I": return "(" + pretty(f[1]) + " -> " + pretty(f[2]) + ")"
    if f[0] == "Q": return "Q[" + f[1] + "](" + pretty(f[2]) + ")"
    if f[0] == "Eq": return "Eq[" + f[1] + "," + f[2] + "]"
    raise ValueError("Unknown constructor")


class Builder:
    def __init__(self):
        self.nodes, self.lookup = [], {}

    def add(self, rule, parameters=(), premises=(), conclusion=None):
        key = rule, tuple(parameters), tuple(premises), conclusion
        if key not in self.lookup:
            self.lookup[key] = len(self.nodes)
            self.nodes.append(dict(rule=rule, parameters=tuple(parameters),
                                   premises=tuple(premises), conclusion=conclusion))
        return self.lookup[key]

    def ax(self, rule, *parameters):
        return self.add(rule, parameters, conclusion=SCHEMAS[rule](*parameters))

    def given(self, f): return self.add("GIVEN", conclusion=f)
    def assume(self, f): return self.add("ASSUMPTION", conclusion=f)
    def conclusion(self, p): return self.nodes[p]["conclusion"]

    def mp(self, major, minor):
        f, g = self.conclusion(major), self.conclusion(minor)
        require(isinstance(f, tuple) and f[0] == "I" and f[1] == g,
                "Generator MP mismatch")
        return self.add("MP", premises=(major, minor), conclusion=f[2])

    @cache
    def support(self, p):
        node = self.nodes[p]
        if node["rule"] == "ASSUMPTION": return frozenset((node["conclusion"],))
        return frozenset().union(*(self.support(q) for q in node["premises"]))

    def gen(self, i, p):
        require(not self.support(p), "GEN on a formula with an open local assumption")
        return self.add("GEN", parameters=(i,), premises=(p,), conclusion=Q(i, self.conclusion(p)))

    @cache
    def identity(self, a):
        return self.mp(self.mp(self.ax("S", a, I(a, a), a),
                               self.ax("K", a, I(a, a))), self.ax("K", a, a))

    @cache
    def discharge(self, a, p):
        node, f = self.nodes[p], self.conclusion(p)
        if node["rule"] == "ASSUMPTION" and f == a: return self.identity(a)
        if a not in self.support(p): return self.mp(self.ax("K", f, a), p)
        require(node["rule"] == "MP", "Unexpected open-assumption inference")
        major, minor = node["premises"]
        bb = self.conclusion(minor)
        return self.mp(self.mp(self.ax("S", a, bb, f), self.discharge(a, major)),
                       self.discharge(a, minor))

    @cache
    def explosion(self, b, i="i"):
        h = self.assume(F)
        existential = self.mp(self.ax("K", F, Q(i, N(Q(i, b)))), h)
        out = self.mp(self.ax("R6", i, b), existential)
        return self.discharge(F, out)

    @cache
    def serial(self, i="i", j="j"):
        k = self.ax("K", F, Eq(i, j))
        lifted = self.mp(self.ax("R2", i, F, N(Eq(i, j))), self.gen(i, k))
        qf = self.assume(Q(i, F))
        out = self.mp(self.ax("R1", i, j), self.mp(lifted, qf))
        return self.discharge(Q(i, F), out)

    def v_stable(self, a, i, v):
        require(self.conclusion(v) == I(a, Q(i, a)), "Wrong positive vacuity input")
        lift = self.mp(self.ax("R2", i, a, Q(i, a)), self.gen(i, v))
        nn_a = self.assume(N(N(a)))
        modal_neg = self.assume(Q(i, N(Q(i, a))))
        local_a = self.assume(a)
        qa = self.mp(v, local_a)
        qqa = self.mp(lift, qa)
        qf = self.mp(self.mp(self.ax("R2", i, Q(i, a), F), modal_neg), qqa)
        f_under_a = self.mp(self.serial(i), qf)
        na = self.discharge(a, f_under_a)
        contradiction = self.mp(nn_a, na)
        existential = self.discharge(Q(i, N(Q(i, a))), contradiction)
        out = self.mp(self.ax("R6", i, a), existential)
        return self.discharge(N(N(a)), out)

    def imp_stable(self, a, b, db):
        require(self.conclusion(db) == DNE(b), "Wrong consequent stability input")
        h = self.assume(N(N(I(a, b))))
        local_a, nb, ab = self.assume(a), self.assume(N(b)), self.assume(I(a, b))
        contradiction = self.mp(nb, self.mp(ab, local_a))
        not_ab = self.discharge(I(a, b), contradiction)
        nnb = self.discharge(N(b), self.mp(h, not_ab))
        out = self.mp(db, nnb)
        return self.discharge(N(N(I(a, b))), self.discharge(a, out))

    @cache
    def neg_stable(self, a):
        h, local_a, na = self.assume(N(N(N(a)))), self.assume(a), self.assume(N(a))
        nna = self.discharge(N(a), self.mp(na, local_a))
        out = self.mp(h, nna)
        return self.discharge(N(N(N(a))), self.discharge(a, out))

    @cache
    def conj_project(self, a, b, side):
        both = self.assume(Conj(a, b))
        if side == 0:
            na, local_a = self.assume(N(a)), self.assume(a)
            nb = self.mp(self.ax("K", F, b), self.mp(na, local_a))
            test = self.discharge(a, nb)
            out = self.discharge(N(a), self.mp(both, test))
        else:
            require(side == 1, "Projection side")
            nb = self.assume(N(b))
            test = self.mp(self.ax("K", N(b), a), nb)
            out = self.discharge(N(b), self.mp(both, test))
        return self.discharge(Conj(a, b), out)

    def quantified_stable_q4(self, i, a):
        return self.v_stable(Q(i, a), i, self.ax("Q4", i, a))

    def bundle_vacuity(self, c, g, r, e, i, bundle, drq, deq):
        vr, ve = I(r, Q(i, r)), I(e, Q(i, e))
        left, right = Conj(c, g), Conj(vr, ve)
        require(self.conclusion(bundle) == Conj(left, right), "Wrong bundle input")
        nn_right = self.mp(self.conj_project(left, right, 1), bundle)
        d_right = self.neg_stable(I(vr, N(ve)))
        right_proof = self.mp(d_right, nn_right)
        n_vr = self.mp(self.conj_project(vr, ve, 0), right_proof)
        n_ve = self.mp(self.conj_project(vr, ve, 1), right_proof)
        return (self.mp(self.imp_stable(r, Q(i, r), drq), n_vr),
                self.mp(self.imp_stable(e, Q(i, e), deq), n_ve))

    def peirce_from_dne(self, a, b, da):
        h = self.assume(I(I(a, b), a))
        na, local_a = self.assume(N(a)), self.assume(a)
        local_b = self.mp(self.explosion(b), self.mp(na, local_a))
        ab = self.discharge(a, local_b)
        contradiction = self.mp(na, self.mp(h, ab))
        nna = self.discharge(N(a), contradiction)
        return self.discharge(I(I(a, b), a), self.mp(da, nna))

    def dne_from_peirce(self, a):
        h, na = self.assume(N(N(a))), self.assume(N(a))
        a_under_na = self.mp(self.explosion(a), self.mp(h, na))
        na_a = self.discharge(N(a), a_under_na)
        out = self.mp(self.ax("P", a, F), na_a)
        return self.discharge(N(N(a)), out)

    def l_from_peirce(self, a, b, c, u, peirce):
        h, j, cu = I(I(c, u), a), I(a, c), I(c, u)
        local_c = self.mp(self.assume(j), self.mp(self.assume(h), self.assume(cu)))
        c_proof = self.mp(peirce, self.discharge(cu, local_c))
        bc = self.mp(self.ax("K", c, b), c_proof)
        return self.discharge(h, self.discharge(j, bc))

    def export(self, name, spec, outputs):
        active = set()
        def visit(p):
            if p in active: return
            active.add(p)
            for q in self.nodes[p]["premises"]: visit(q)
        for p in outputs:
            require(not self.support(p), "Undischarged final assumption")
            visit(p)
        ordered = sorted(active)
        remap = {old: new for new, old in enumerate(ordered)}
        rows = []
        for p in ordered:
            row = self.nodes[p].copy()
            require(row["rule"] != "ASSUMPTION", "Uneliminated local assumption")
            row["premises"] = [remap[x] for x in row["premises"]]
            rows.append(row)
        return dict(name=name, declared_premises=spec["premises"],
                    outputs=[remap[x] for x in outputs], nodes=rows)


def specifications():
    a, b, c, u, r, e, i = "a", "b", "c", "u", "r", "e", "i"
    core = ["K", "S", "R1", "R2", "R6", "GEN", "MP", "GIVEN"]
    bundle = Conj(Conj(c, "g"), Conj(I(r, Q(i, r)), I(e, Q(i, e))))
    def sp(goals, premises=(), extras=()):
        return dict(goals=list(goals), premises=list(premises), allowed=core + list(extras))
    return {
        "explosion_from_rho6": sp([I(F, a)]),
        "seriality_from_rho1": sp([I(Q(i, F), F)]),
        "positive_vacuity_implies_stability": sp([DNE(a)], [I(a, Q(i, a))]),
        "implication_stability": sp([DNE(I(a, b))], [DNE(b)]),
        "negative_formula_stability": sp([DNE(N(a))]),
        "negative_conjunction_projections": sp([I(Conj(a, b), N(N(a))), I(Conj(a, b), N(N(b)))]),
        "Q4_implies_quantified_stability": sp([DNE(Q(i, a))], extras=["Q4"]),
        "Q4_gated_bundle_atomic_stability": sp([DNE(r), DNE(e)], [bundle], ["Q4"]),
        "QDN_gated_bundle_atomic_stability": sp([DNE(r), DNE(e)],
                                                [bundle, DNE(Q(i, r)), DNE(Q(i, e))]),
        "KS_DNE_to_Peirce": sp([P(a, b)], extras=["DNE"]),
        "KS_Peirce_to_DNE": sp([DNE(a)], extras=["P"]),
        "KS_DNE_to_original_L": sp([L(a, b, c, u)], extras=["DNE"]),
    }


def generate_one(name, spec):
    b = Builder()
    a, bb, c, u, i = "a", "b", "c", "u", "i"
    if name == "explosion_from_rho6": out = [b.explosion(a)]
    elif name == "seriality_from_rho1": out = [b.serial()]
    elif name == "positive_vacuity_implies_stability":
        out = [b.v_stable(a, i, b.given(spec["premises"][0]))]
    elif name == "implication_stability": out = [b.imp_stable(a, bb, b.given(DNE(bb)))]
    elif name == "negative_formula_stability": out = [b.neg_stable(a)]
    elif name == "negative_conjunction_projections": out = [b.conj_project(a, bb, side) for side in (0, 1)]
    elif name == "Q4_implies_quantified_stability": out = [b.quantified_stable_q4(i, a)]
    elif name in ("Q4_gated_bundle_atomic_stability", "QDN_gated_bundle_atomic_stability"):
        r, e = "r", "e"
        bundle = b.given(spec["premises"][0])
        if name.startswith("Q4"):
            drq, deq = [b.quantified_stable_q4(i, x) for x in (r, e)]
        else:
            drq, deq = [b.given(DNE(Q(i, x))) for x in (r, e)]
        vr, ve = b.bundle_vacuity(c, "g", r, e, i, bundle, drq, deq)
        out = [b.v_stable(r, i, vr), b.v_stable(e, i, ve)]
    elif name == "KS_DNE_to_Peirce": out = [b.peirce_from_dne(a, bb, b.ax("DNE", a))]
    elif name == "KS_Peirce_to_DNE": out = [b.dne_from_peirce(a)]
    elif name == "KS_DNE_to_original_L":
        pp = b.peirce_from_dne(c, u, b.ax("DNE", c))
        out = [b.l_from_peirce(a, bb, c, u, pp)]
    else: raise ValueError("No generator for " + name)
    require([b.conclusion(x) for x in out] == spec["goals"], "Generator final goal mismatch")
    return b.export(name, spec, out)


def freeze(value):
    return tuple(freeze(x) for x in value) if isinstance(value, list) else value


def replay(certificate, name, spec):
    require(certificate["name"] == name, "Wrong certificate name")
    require(list(freeze(certificate["declared_premises"])) == spec["premises"], "Wrong permitted premises")
    conclusions, counts = [], Counter()
    for at, row in enumerate(certificate["nodes"]):
        rule, args = row["rule"], freeze(row["parameters"])
        premises, f = row["premises"], freeze(row["conclusion"])
        require(rule in spec["allowed"], "Rule not permitted: " + rule)
        require(all(isinstance(p, int) and 0 <= p < at for p in premises), "Forward or missing reference")
        if rule in SCHEMAS:
            require(not premises, "Schema with premises")
            require(f == SCHEMAS[rule](*args), "Wrong schema instance")
        elif rule == "MP":
            require(not args and len(premises) == 2, "MP arity")
            major, minor = (conclusions[p] for p in premises)
            require(major == I(minor, f), "MP check failed")
        elif rule == "GEN":
            require(len(args) == len(premises) == 1, "GEN arity")
            require(f == Q(args[0], conclusions[premises[0]]), "GEN check failed")
        elif rule == "GIVEN":
            require(not args and not premises and f in spec["premises"], "Undeclared theorem premise")
        else: raise ValueError("Unexpected rule")
        conclusions.append(f)
        counts[rule] += 1
    require(len(certificate["outputs"]) == len(spec["goals"]), "Output count")
    require(all(isinstance(p, int) and 0 <= p < len(conclusions) for p in certificate["outputs"]), "Output reference")
    require([conclusions[p] for p in certificate["outputs"]] == spec["goals"], "Wrong final theorem")
    return dict(status="PASS", nodes=len(conclusions), rules=dict(sorted(counts.items())),
                local_assumptions=0, declared_theorem_premises=[pretty(p) for p in spec["premises"]],
                conclusions=[pretty(f) for f in spec["goals"]])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only", action="store_true")
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    certificate_path = args.output / "formalism_certificates.json"
    specs = specifications()
    if not args.check_only:
        generated = {name: generate_one(name, spec) for name, spec in specs.items()}
        certificate_path.write_text(json.dumps(generated, separators=(",", ":")) + "\n")
    certificates = json.loads(certificate_path.read_text())
    require(set(certificates) == set(specs), "Wrong certificate family")
    checked = {name: replay(certificates[name], name, spec) for name, spec in specs.items()}
    receipt = dict(status="PASS", certificate_count=len(checked),
                   proof_nodes=sum(item["nodes"] for item in checked.values()),
                   certificate_sha256=hashlib.sha256(certificate_path.read_bytes()).hexdigest(),
                   checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                   checked=checked, numerical_induction="Ordinary proof in formalism_sections.tex; not checked by this finite kernel.",
                   machine_claim=False, proof_assistant_endpoint=False)
    (args.output / "formalism_proof_receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({k: v for k, v in receipt.items() if k != "checked"}, indent=2))


if __name__ == "__main__": main()
