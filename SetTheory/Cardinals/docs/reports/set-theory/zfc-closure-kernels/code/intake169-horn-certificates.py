"""Finite syntactic certificates for joint equational packet congruences.

Authored independently of the delivered scripts. No supplied imports, model
enumeration, proof search, compiler calls, filesystem writes, or side effects.
The checks prove the displayed universal Horn consequences by substitution;
the ordinary model/Boolean/serialization arguments remain separate obligations.
"""


def require(condition, message):
    if not condition:
        raise ValueError(message)


def term(name, *args):
    return (name, *args)


def eq(a, b):
    return term("Eq", a, b)


def variables(t):
    if isinstance(t, str):
        return {t}
    return set().union(*(variables(a) for a in t[1:])) if len(t) > 1 else set()


def subst(t, env):
    if isinstance(t, str):
        return env[t]
    return (t[0], *(subst(a, env) for a in t[1:]))


def congruence(symbol, arity, changed):
    before = tuple("x" + str(i) for i in range(arity))
    after = tuple("y" + str(i) if i in changed else before[i] for i in range(arity))
    return ([eq(before[i], after[i]) for i in changed],
            eq(term(symbol, *before), term(symbol, *after)))


SCHEMAS = {
    "refl": ([], eq("x", "x")),
    "euclid": ([eq("x", "y"), eq("x", "z")], eq("y", "z")),
    "C_full": congruence("C", 3, (0, 1, 2)),
    "C_pair": congruence("C", 3, (0, 1)),
    "C_0": congruence("C", 3, (0,)),
    "C_1": congruence("C", 3, (1,)),
    "C_2": congruence("C", 3, (2,)),
    # No premise Eq(x0,y0): the selector x0 is fixed syntactically.
    "H_objects": congruence("H", 3, (1, 2)),
    "H_1": congruence("H", 3, (1,)),
    "H_2": congruence("H", 3, (2,)),
    "Inc_congr": ([eq("x", "u"), eq("y", "v"), term("Inc", "x", "y")],
                  term("Inc", "u", "v")),
}


class Proof:
    def __init__(self, name, assumptions, allowed):
        self.name, self.assumptions = name, assumptions
        self.allowed = tuple(allowed)
        self.facts, self.steps = list(assumptions), []

    def add(self, schema, env, refs):
        require(schema in self.allowed, "Unallowed schema " + schema)
        prem, result = SCHEMAS[schema]
        used = set().union(*(variables(t) for t in [*prem, result]))
        require(set(env) == used, "Schema variable domain mismatch")
        require(all(not variables(t) for t in env.values()), "Non-ground certificate instantiation")
        require(all(type(i) is int and 0 <= i < len(self.facts) for i in refs), "Invalid premise index")
        require([self.facts[i] for i in refs] == [subst(t, env) for t in prem], "Premise mismatch")
        self.steps.append({"schema": schema, "environment": env, "premises": list(refs)})
        self.facts.append(subst(result, env))
        return len(self.facts) - 1

    def refl(self, value):
        return self.add("refl", {"x": value}, [])

    def trans(self, first, second):
        _, a, b = self.facts[first]
        _, b1, c = self.facts[second]
        require(b == b1, "Transitivity middle differs")
        r = self.refl(a)
        sym = self.add("euclid", {"x": a, "y": b, "z": a}, [first, r])
        return self.add("euclid", {"x": b, "y": a, "z": c}, [sym, second])

    def finish(self, goal):
        require(self.facts[-1] == goal, "Certificate goal mismatch")
        return {"name": self.name, "assumptions": self.assumptions,
                "allowed_schemas": self.allowed, "steps": self.steps, "goal": goal}


def partition_certificates(symbol, full_name, changed, parts, prefix):
    a = tuple(term("a" + str(i)) for i in range(3))
    b = tuple(term("b" + str(i)) if i in changed else a[i] for i in range(3))
    assumptions = [eq(a[i], b[i]) for i in changed]
    assumption_refs = dict(zip(changed, range(len(changed))))
    proof = Proof(prefix + "_parts_to_full", assumptions,
                  ["refl", "euclid", *(name for name, _ in parts)])
    current, chain = a, None
    for name, indices in parts:
        env = {"x" + str(i): current[i] for i in range(3)}
        env.update({"y" + str(i): b[i] for i in indices})
        link = proof.add(name, env, [assumption_refs[i] for i in indices])
        chain = link if chain is None else proof.trans(chain, link)
        current = tuple(b[i] if i in indices else current[i] for i in range(3))
    require(current == b, "Partition does not cover exactly changed positions")
    result = [proof.finish(eq(term(symbol, *a), term(symbol, *b)))]
    for name, indices in parts:
        proof = Proof(prefix + "_full_to_" + name, [eq(a[i], b[i]) for i in indices],
                      ["refl", full_name])
        env = {"x" + str(i): a[i] for i in range(3)}
        refs = []
        for i in changed:
            env["y" + str(i)] = b[i] if i in indices else a[i]
            refs.append(indices.index(i) if i in indices else proof.refl(a[i]))
        proof.add(full_name, env, refs)
        target = tuple(b[i] if i in indices else a[i] for i in range(3))
        result.append(proof.finish(eq(term(symbol, *a), term(symbol, *target))))
    return result


def membership_certificate(alias):
    d, tag = term("d"), term("tA")
    o = term("o") if alias else term("I", d, d)
    a, b, u, v = map(term, ("a", "b", "u", "v"))
    atom = term("H", tag, d, o)
    inner_a, inner_u = term("C", d, d, a), term("C", d, d, u)
    frame_a, frame_u = term("C", inner_a, o, b), term("C", inner_u, o, v)
    proof = Proof("derived_membership_congruence_" + ("alias" if alias else "noalias"),
                  [eq(a, u), eq(b, v), term("Inc", frame_a, atom)],
                  ["refl", "C_full", "Inc_congr"])
    rd, ro = proof.refl(d), proof.refl(o)
    p = proof.add("C_full", {"x0": d, "x1": d, "x2": a, "y0": d, "y1": d, "y2": u}, [rd, rd, 0])
    f = proof.add("C_full", {"x0": inner_a, "x1": o, "x2": b, "y0": inner_u, "y1": o, "y2": v}, [p, ro, 1])
    ra = proof.refl(atom)
    proof.add("Inc_congr", {"x": frame_a, "u": frame_u, "y": atom, "v": atom}, [f, ra, 2])
    result = proof.finish(term("Inc", frame_u, atom))
    result["derived_schema_dependency"] = "C_full is recovered by the C partition certificate for the selected variant."
    return result


def replay(certificate):
    proof = Proof(certificate["name"], certificate["assumptions"], certificate["allowed_schemas"])
    for step in certificate["steps"]:
        proof.add(step["schema"], step["environment"], step["premises"])
    proof.finish(certificate["goal"])


def verify_certificates():
    certificates = [
        *partition_certificates("C", "C_full", (0, 1, 2), [("C_pair", (0, 1)), ("C_2", (2,))], "C_two_parts"),
        *partition_certificates("C", "C_full", (0, 1, 2), [("C_0", (0,)), ("C_1", (1,)), ("C_2", (2,))], "C_single_parts"),
        *partition_certificates("H", "H_objects", (1, 2), [("H_1", (1,)), ("H_2", (2,))], "H_object_single_parts"),
        membership_certificate(False), membership_certificate(True),
    ]
    for certificate in certificates:
        replay(certificate)
    capacities = {name: len(set().union(*(variables(t) for t in [*prem, goal])))
                  for name, (prem, goal) in SCHEMAS.items()}
    require(capacities["C_pair"] == capacities["H_objects"] == 5, "Unexpected two-part variable capacity")
    require(all(capacities[x] == 4 for x in ("C_0", "C_1", "C_2", "H_1", "H_2")), "Unexpected single-part capacity")
    return {"status": "FINITE_SYNTACTIC_HORN_CERTIFICATES_PASS",
            "scope": "Ordinary universal Horn instantiation checks only; no model calibration or Boolean encoding claim.",
            "schemas": SCHEMAS, "schema_variable_capacities": capacities,
            "certificates": certificates, "certificate_count": len(certificates),
            "inference_count": sum(len(p["steps"]) for p in certificates),
            "selector_rule": "H selector coordinate 0 is identical on both sides and has no equality premise or substitution step.",
            "findings": []}
