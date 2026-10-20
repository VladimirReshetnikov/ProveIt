#!/usr/bin/env python3
"""Independent actual-Rel-helper certificate checker; safe under python -O.

No generator is imported. Primitive symmetry, V_eq, and unclosed theorem
roots are forbidden. TAUT is independently evaluated over all Boolean
assignments, relative to F=Rel(0,0); its use is a derived propositional basis.
"""
from __future__ import annotations
import argparse
from functools import cache
import hashlib
from itertools import product
import json
from pathlib import Path

F = ("rel", 0, 0)
I = lambda a, b: ("imp", a, b)
Q = lambda x, a: ("all", x, a)
N = lambda a: I(a, F)
Ex = lambda x, a: N(Q(x, N(a)))
Eq = lambda a, b: ("eq", a, b)
R = lambda a, b: ("rel", a, b)
And = lambda a, b: N(I(a, N(b)))
pair = lambda a, b: (a+b)*(a+b+1)//2+b
eqcode = lambda a, b: 4*pair(a,b)+3
relcode = lambda a, b: 4*pair(a,b)+1


def need(x, why):
    if not x:
        raise ValueError(why)


def tu(x):
    return tuple(map(tu, x)) if isinstance(x, list) else x


@cache
def atoms(f):
    if f == F:
        return frozenset()
    if f[0] == "imp":
        return atoms(f[1]) | atoms(f[2])
    return frozenset([f])


@cache
def taut(f):
    atom_names = tuple(atoms(f))
    need(len(atom_names) <= 12, "unexpected tautology size")
    def value(a, env):
        if a == F:
            return False
        if a[0] == "imp":
            return not value(a[1], env) or value(a[2], env)
        return env[a]
    return all(value(f, dict(zip(atom_names, bits)))
               for bits in product((False, True), repeat=len(atom_names)))


@cache
def valid(f):
    need(isinstance(f, tuple), "formula is not a tuple")
    if f[0] in ("rel", "eq"):
        need(len(f) == 3 and all(type(n) is int and n >= 0 for n in f[1:]), "invalid atomic labels")
    elif f[0] == "all":
        need(len(f) == 3 and type(f[1]) is int and f[1] >= 0, "invalid quantifier")
        valid(f[2])
    elif f[0] == "imp":
        need(len(f) == 3, "invalid implication")
        valid(f[1]); valid(f[2])
    else:
        raise ValueError("unknown formula constructor")
    return True


def E(a, b):
    z = eqcode(a, b)
    return And(Q(z, And(I(R(z,a),R(z,b)),I(R(z,b),R(z,a)))),
               Q(z, And(I(R(a,z),R(b,z)),I(R(b,z),R(a,z)))))


def expected_roots():
    roots = {}
    for x in (0, 1, 7, 999):
        roots[f"primitive_refl/{x}"] = Eq(x,x)
        roots[f"primitive_sym/{x}/0"] = I(Eq(x,0),Eq(0,x))
    for x, y in ((0,0),(0,1),(1,0),(1,1),(2,7),(100,999)):
        roots[f"eq_to_E/{x}/{y}"] = I(Eq(x,y),E(x,y))
        roots[f"exists_E/{x}/{y}"] = Ex(x,E(x,y))
        k = eqcode(x,y)
        roots[f"E_vacuity/{x}/{y}/{k}"] = I(E(x,y),Q(k,E(x,y)))
        for z in sorted({0,x,y,k}):
            roots[f"E_in/{x}/{y}/{z}"] = I(E(x,y),I(R(z,x),R(z,y)))
            roots[f"E_out/{x}/{y}/{z}"] = I(E(x,y),I(R(x,z),R(y,z)))
    for x,y,z in ((0,0,0),(0,1,1),(2,7,eqcode(2,7)),(999,0,100)):
        roots[f"E_rho7/{x}/{y}/{z}"] = I(E(z,x),I(E(z,y),E(x,y)))
    return roots


def check(data):
    need(data["format"] == "actual-rel-helper-bootstrap-v1", "wrong format")
    forms = list(map(tu, data["formulas"]))
    for f in forms:
        valid(f)
    nodes = data["proof_nodes"]
    opens, counts = [], {}
    for i, p in enumerate(nodes):
        need(type(p["formula"]) is int and 0 <= p["formula"] < len(forms), "bad formula index")
        f, rule, args = forms[p["formula"]], p["rule"], p["args"]
        deps = frozenset()
        counts[rule] = counts.get(rule, 0) + 1
        if rule == "MP":
            need(len(args) == 2 and all(type(j) is int and 0 <= j < i for j in args), "MP not earlier")
            major, minor = args
            need(forms[nodes[major]["formula"]] == I(forms[nodes[minor]["formula"]],f), "bad MP")
            deps = opens[major] | opens[minor]
        elif rule == "GEN":
            need(len(args) == 2 and type(args[0]) is int and args[0] >= 0 and 0 <= args[1] < i, "bad GEN indices")
            x, premise = args
            need(not opens[premise], "GEN over open assumptions")
            need(f == Q(x, forms[nodes[premise]["formula"]]), "bad GEN")
        elif rule == "HYP":
            deps = frozenset([f])
        elif rule == "TAUT":
            need(not args and taut(f), "invalid Boolean tautology")
        elif rule == "K":
            need(not args and f == I(f[1],I(f[2][1],f[1])), "bad K")
        elif rule == "S":
            a,b,c = f[1][1],f[1][2][1],f[1][2][2]
            need(not args and f == I(I(a,I(b,c)),I(I(a,b),I(a,c))), "bad S")
        elif rule == "rho1":
            x = f[1][1]; atom = f[1][2][1]
            need(not args and atom[0] == "eq" and atom[1] == x and f == Ex(x,atom), "bad rho1")
        elif rule == "rho2":
            x = f[1][1]; a,b = f[1][2][1:]
            need(not args and f == I(Q(x,I(a,b)),I(Q(x,a),Q(x,b))), "bad rho2")
        elif rule == "rho4":
            x,y,a = f[1][1],f[1][2][1],f[1][2][2]
            need(not args and f == I(Q(x,Q(y,a)),Q(y,Q(x,a))), "bad rho4")
        elif rule == "rho6":
            x,a = f[1][1][1],f[2]
            need(not args and f == I(Ex(x,Q(x,a)),a), "bad rho6")
        elif rule == "rho7":
            c,a = f[1][1:]; d,b = f[2][1][1:]
            need(not args and c == d and f == I(Eq(c,a),I(Eq(c,b),Eq(a,b))), "bad rho7")
        elif rule == "rho3":
            a,b = f[1][1:]; z = f[2][1][1]
            need(not args and f == I(Eq(a,b),I(R(z,a),R(z,b))), "bad rho3")
        elif rule == "rho5":
            a,b = f[1][1:]; z = f[2][1][2]
            need(not args and f == I(Eq(a,b),I(R(a,z),R(b,z))), "bad rho5")
        elif rule == "vacRel":
            a,b = f[1][1:]; z = f[2][1]
            need(not args and z not in (a,b) and f == I(R(a,b),Q(z,R(a,b))), "bad vacRel")
        elif rule == "REL_HELPER":
            a,b = f[1][1:]
            need(not args and f == I(Eq(a,b),Q(relcode(a,b),Eq(a,b))), "wrong actual Rel-code helper")
        else:
            raise ValueError("forbidden rule " + rule)
        opens.append(deps)
    expected = expected_roots()
    need(set(data["roots"]) == set(expected), "wrong roots")
    for name, n in data["roots"].items():
        need(type(n) is int and 0 <= n < len(nodes), "invalid root")
        need(not opens[n] and forms[nodes[n]["formula"]] == expected[name], "open or wrong root " + name)
    return {"status":"PASS_ACTUAL_REL_HELPER", "closed_roots":len(expected),
            "proof_nodes":len(nodes), "formulas":len(forms), "rules":counts,
            "primitive_symmetry_leaves":0, "old_eq_code_helper_leaves":0,
            "scope":"Finite exact-label proof-local replay; uniform label theorem and K private-code coupling proved in separate mathematical notes. TAUT uses independently checked Boolean truth and the retained rho8/rho6 derived classical basis."}


def main():
    import copy
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate", nargs="?", type=Path, default=Path(__file__).with_name("rel_helper_certificate.json"))
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("rel_helper_certificate_receipt.json"))
    a = parser.parse_args()
    raw = a.certificate.read_bytes()
    data = json.loads(raw)
    result = check(data)
    rejected = []
    for kind in ("wrong_helper_binder", "old_eq_helper_leaf", "primitive_symmetry_leaf", "wrong_root"):
        bad = dict(data)
        bad["proof_nodes"] = list(data["proof_nodes"])
        bad["formulas"] = list(data["formulas"])
        bad["roots"] = dict(data["roots"])
        if kind in ("wrong_helper_binder", "old_eq_helper_leaf"):
            for i, node in enumerate(bad["proof_nodes"]):
                if node["rule"] == "REL_HELPER":
                    if kind == "wrong_helper_binder":
                        j = node["formula"]
                        bad["formulas"][j] = copy.deepcopy(data["formulas"][j])
                        bad["formulas"][j][2][1] += 1
                    else:
                        bad["proof_nodes"][i] = dict(node, rule="V_eq")
                    break
        elif kind == "primitive_symmetry_leaf":
            bad["proof_nodes"][0] = dict(bad["proof_nodes"][0], rule="SYM")
        else:
            first = next(iter(bad["roots"]))
            bad["roots"][first] = 0
        try:
            check(bad)
        except (ValueError, IndexError, TypeError):
            rejected.append(kind)
        else:
            raise ValueError("tamper accepted: " + kind)
    result["rejected_tamper_controls"] = rejected
    result["sha256"] = hashlib.sha256(raw).hexdigest()
    a.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
