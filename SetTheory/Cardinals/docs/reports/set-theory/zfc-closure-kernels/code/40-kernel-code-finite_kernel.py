#!/usr/bin/env python3
"""Finite class/closure presentations for Con(ZFC).

This is a literal clause generator and a reference ground satisfiability
procedure, not a Turing-machine compiler or a proof-assistant certificate.
The consistency proof and attribution are in the accompanying article.
Only the Python standard library is required. Whole-theory search is opt-in.
"""
from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path


def variable(name):
    return ("$", name)


def term(name, *children):
    return (name, *children)


def literal(sign, relation, *args):
    return (sign, relation, *args)


def positive(relation, *args):
    return literal(True, relation, *args)


def negative(relation, *args):
    return literal(False, relation, *args)


def is_variable(t):
    return t[0] == "$"


def term_variables(t):
    if is_variable(t):
        return {t[1]}
    result = set()
    for child in t[1:]:
        result.update(term_variables(child))
    return result


def clause_variables(clause):
    result = set()
    for lit in clause:
        for arg in lit[2:]:
            result.update(term_variables(arg))
    return sorted(result)


def term_size(t):
    return 1 if is_variable(t) else 1 + sum(term_size(c) for c in t[1:])


def term_depth(t):
    return 0 if is_variable(t) or len(t) == 1 else 1 + max(term_depth(c) for c in t[1:])


def subterms(t):
    yield t
    if not is_variable(t):
        for child in t[1:]:
            yield from subterms(child)


def show_term(t, tptp=False):
    if is_variable(t):
        return t[1].upper() if tptp else t[1]
    name = ({"c": "c0", "C": "upd"}.get(t[0], t[0].lower())) if tptp else t[0]
    return name if len(t) == 1 else name + "(" + ",".join(show_term(c, tptp) for c in t[1:]) + ")"


def show_literal(lit, tptp=False):
    sign, relation, *args = lit
    vals = [show_term(t, tptp) for t in args]
    if relation == "=":
        return vals[0] + (" = " if sign else " != ") + vals[1]
    name = relation.lower() if tptp else relation
    atom = name + "(" + ",".join(vals) + ")"
    return atom if sign else "~" + atom


def build(packed=True, branch="predicate"):
    """Return a completely specified universal clause presentation.

    packed=True stores the class code in V(b,c). packed=False retains t.
    branch='predicate' uses a fresh branch predicate G.
    branch='direct' distributes the two alternatives with no G.
    branch='equality' uses Flag(...)=c, charging the extra function Flag.
    """
    if branch not in ("predicate", "direct", "equality"):
        raise ValueError("unknown branch presentation")
    sig = {"c": 0, "V": 2, "C": 3, "N": 2, "A": 2, "Q": 2, "W": 3}
    params = [variable("b")] if packed else [variable("b"), variable("t")]
    p_arity = len(params)
    sig.update({"Bad": p_arity, "H": p_arity, "Out": p_arity + 1,
                "Mem": p_arity + 1, "Sup": p_arity + 1, "Pick": 1})
    relations = {"E": 2, "eps": 2, "=": 2}
    if branch == "predicate":
        relations["G"] = p_arity
    if branch == "equality":
        sig["Flag"] = p_arity
    c = term("c")
    s, j, z, k, a, b, t, x, y, q = map(variable, ("s", "j", "z", "k", "a", "b", "t", "x", "y", "q"))
    V = lambda r, i: term("V", r, i)
    C = lambda r, i, v: term("C", r, i, v)
    rows = []

    def add(source, *lits):
        rows.append({"source": source, "literals": tuple(lits)})

    add("B1.Change", positive("=", V(C(s, j, z), j), z))
    add("B1.Change", positive("=", k, j), positive("=", V(C(s, j, z), k), V(s, k)))
    n = term("N", a, b)
    add("B2.NAND", negative("eps", s, n), negative("eps", s, a), negative("eps", s, b))
    add("B2.NAND", positive("eps", s, n), positive("eps", s, a))
    add("B2.NAND", positive("eps", s, n), positive("eps", s, b))
    atom = term("A", j, k)
    add("B3.Atomic", negative("eps", s, atom), positive("E", V(s, j), V(s, k)))
    add("B3.Atomic", positive("eps", s, atom), negative("E", V(s, j), V(s, k)))
    ex = term("Q", j, a)
    witness = term("W", j, a, s)
    add("B4.Exists", negative("eps", s, ex), positive("eps", C(s, j, witness), a))
    add("B4.Exists", negative("eps", C(s, j, z), a), positive("eps", s, ex))

    def rho(sign, u, v):
        # Crucial: evaluate the code in the ORIGINAL assignment b.
        code = V(b, c) if packed else t
        updated = C(C(b, c, u), term("N", c, c), v)
        return literal(sign, "eps", updated, code)

    bad = term("Bad", *params)
    hull = term("H", *params)
    out = term("Out", *params, q)
    member = term("Mem", *params, q)
    support = term("Sup", *params, y)
    bad_lits = [rho(True, bad, out), positive("E", member, out), negative("E", member, q)]
    hull_clauses = [
        (positive("E", term("Pick", x), x), rho(False, x, y), positive("E", y, hull)),
        (negative("E", x, hull), rho(False, x, y), positive("E", y, hull)),
        (negative("E", y, hull), rho(True, support, y)),
    ]
    if branch == "direct":
        for index, rhs in enumerate(hull_clauses):
            for left in bad_lits:
                add("B5.Direct." + str(index + 1), left, *rhs)
    else:
        flag_args = params if branch == "predicate" else [term("Flag", *params), c]
        flag_rel = "G" if branch == "predicate" else "="
        for lit in bad_lits:
            add("B5.Bad", positive(flag_rel, *flag_args), lit)
        for index, rhs in enumerate(hull_clauses):
            add("B5.Hull." + str(index + 1), negative(flag_rel, *flag_args), *rhs)
    return {"name": ("packed" if packed else "unpacked") + "_" + branch,
            "packed": packed, "branch": branch, "signature": sig,
            "relations": relations, "clauses": rows}


def compress(payload, strategy="shared", derive_pick=True):
    """Literal witness substitutions whose equisatisfiability is proved in text.

    shared: Bad/H share Target; Out/Sup share Next.
    packed: use two coordinates of one Bundle for Next and Mem.
    slice: put every witness and the Boolean branch in the unconstrained
           W(c,FalseClass,assignment) slice; introduce no new proper function.
    These are not claimed to preserve the interpretations of the old Skolems.
    """
    if not payload["packed"]:
        raise ValueError("compression expects a packed presentation")
    if strategy not in ("shared", "packed", "slice"):
        raise ValueError("unknown witness strategy")
    if strategy == "slice" and payload["branch"] == "equality":
        raise ValueError("free-slice Boolean encoding expects a predicate or direct branch")
    c = term("c")
    k = term("N", c, c)
    pair = lambda b, z: term("C", term("C", c, c, b), k, z)
    true_class = term("N", c, k)
    false_class = term("N", true_class, true_class)
    free = lambda s: term("W", c, false_class, s)
    marker = term("N", term("V", c, k), term("V", c, k))
    address = lambda z: term("C", term("C", c, c, z), k, marker)
    record = lambda b, z: free(pair(b, z))
    project = lambda rec, i: term("V", rec, i)

    def rewrite(t):
        if is_variable(t):
            return t
        name = t[0]
        args = tuple(rewrite(v) for v in t[1:])
        if name == "Pick" and derive_pick:
            return term("W", c, term("A", c, k), term("C", c, k, args[0]))
        if name in ("Bad", "H"):
            if strategy == "slice":
                return project(record(args[0], c), c)
            return term("Target", *args)
        if name in ("Out", "Sup", "Mem"):
            if strategy == "shared":
                return term("Mem" if name == "Mem" else "Next", *args)
            rec = term("Bundle", *args) if strategy == "packed" else record(args[0], address(args[1]))
            return project(rec, k if name == "Mem" else c)
        return term(name, *args)

    rows = []
    for row in payload["clauses"]:
        cl = []
        for lit in row["literals"]:
            if lit[1] == "G" and strategy == "slice":
                b = rewrite(lit[2])
                cl.append(literal(lit[0], "eps", c, project(record(b, c), k)))
            else:
                cl.append(literal(lit[0], lit[1], *(rewrite(t) for t in lit[2:])))
        rows.append({"source": row["source"], "literals": tuple(cl)})
    signature = {}
    relations = {}
    for row in rows:
        for lit in row["literals"]:
            relations[lit[1]] = len(lit) - 2
            for arg in lit[2:]:
                for t in subterms(arg):
                    if not is_variable(t):
                        signature[t[0]] = len(t) - 1
    return {"name": payload["name"] + "_" + strategy + ("_derived" if derive_pick else ""),
            "packed": True, "branch": payload["branch"], "witness_strategy": strategy,
            "derived_pick": derive_pick, "signature": signature, "relations": relations,
            "clauses": rows}


def audit(payload):
    sig, rels = payload["signature"], payload["relations"]

    def check_term(t):
        if is_variable(t):
            if len(t) != 2 or not isinstance(t[1], str):
                raise ValueError("malformed variable")
            return
        if t[0] not in sig or len(t) - 1 != sig[t[0]]:
            raise ValueError("ill-formed term: " + repr(t))
        for child in t[1:]:
            check_term(child)

    for row in payload["clauses"]:
        for lit in row["literals"]:
            if type(lit[0]) is not bool or lit[1] not in rels or len(lit) - 2 != rels[lit[1]]:
                raise ValueError("ill-formed literal")
            for arg in lit[2:]:
                check_term(arg)
    terms = [arg for row in payload["clauses"] for lit in row["literals"] for arg in lit[2:]]
    by_source = {}
    for row in payload["clauses"]:
        by_source[row["source"]] = by_source.get(row["source"], 0) + 1
    return {
        "name": payload["name"], "nonlogical_blocks": 5,
        "clauses": len(payload["clauses"]),
        "literal_occurrences": sum(len(row["literals"]) for row in payload["clauses"]),
        "term_occurrences": sum(term_size(t) for t in terms),
        "maximum_term_depth": max(map(term_depth, terms)),
        "maximum_universal_variables": max(len(clause_variables(row["literals"])) for row in payload["clauses"]),
        "constants": sum(a == 0 for a in sig.values()),
        "proper_functions": sum(a > 0 for a in sig.values()),
        "function_arities": {str(a): sum(v == a for v in sig.values()) for a in range(max(sig.values()) + 1)},
        "relations_excluding_equality": len(rels) - 1,
        "clauses_by_source": by_source,
        "machine_state_count": None,
    }


def substitute(t, assignment):
    if is_variable(t):
        return assignment[t[1]]
    return term(t[0], *(substitute(c, assignment) for c in t[1:]))


def instantiate(clause, assignment):
    return tuple(literal(lit[0], lit[1], *(substitute(t, assignment) for t in lit[2:])) for lit in clause)


def ground_terms(signature):
    """Fair increasing-depth enumeration; retains a complete finite frontier."""
    prior = [term(name) for name, arity in signature.items() if arity == 0]
    if not prior:
        raise ValueError("a constant is required")
    seen = set(prior)
    yield from prior
    while True:
        new = []
        for name, arity in signature.items():
            if arity:
                for args in itertools.product(prior, repeat=arity):
                    value = term(name, *args)
                    if value not in seen:
                        seen.add(value)
                        new.append(value)
                        yield value
        if not new:
            return
        prior.extend(new)


def ground_stage(payload, count):
    if count < 1:
        raise ValueError("positive term prefix required")
    available = list(itertools.islice(ground_terms(payload["signature"]), count))
    for row in payload["clauses"]:
        names = clause_variables(row["literals"])
        # Repeated/colliding substitutions are intentionally included.
        for values in itertools.product(available, repeat=len(names)):
            yield instantiate(row["literals"], dict(zip(names, values)))


def restricted_growth_partitions(n):
    """Every equivalence relation on n items, once, without recursion."""
    if n == 0:
        yield ()
        return
    current = [0] * n
    while True:
        yield tuple(current)
        for index in range(n - 1, 0, -1):
            upper = max(current[:index]) + 1
            if current[index] < upper:
                current[index] += 1
                current[index + 1:] = [0] * (n - index - 1)
                break
        else:
            return


def ground_satisfiable(clauses):
    """Exact finite ground EUF+predicate satisfiability, deliberately simple.

    Returns a small model certificate, or None for unsatisfiability.
    This partitions denotations, not syntax: f(c)=c is permitted.
    Resource exhaustion raises an exception and is never acceptance.
    """
    clauses = tuple(tuple(c) for c in clauses)
    observed = {s for cl in clauses for lit in cl for arg in lit[2:] for s in subterms(arg)}
    if any(is_variable(t) for t in observed):
        raise ValueError("ground terms required")
    if not observed:
        observed.add(term("c"))
    ordered = sorted(observed, key=repr)
    for partition in restricted_growth_partitions(len(ordered)):
        classes = dict(zip(ordered, partition))
        applications = {}
        for t in ordered:
            key = (t[0], *(classes[a] for a in t[1:]))
            if key in applications and applications[key] != classes[t]:
                break
            applications[key] = classes[t]
        else:
            atoms = sorted({(lit[1], *(classes[t] for t in lit[2:]))
                            for cl in clauses for lit in cl if lit[1] != "="})
            for bits in itertools.product((False, True), repeat=len(atoms)):
                valuation = dict(zip(atoms, bits))

                def holds(lit):
                    if lit[1] == "=":
                        value = classes[lit[2]] == classes[lit[3]]
                    else:
                        value = valuation[(lit[1], *(classes[t] for t in lit[2:]))]
                    return value == lit[0]

                if all(any(holds(lit) for lit in cl) for cl in clauses):
                    return {"domain_size": 1 + max(partition),
                            "term_classes": [[show_term(t), classes[t]] for t in ordered],
                            "predicate_values": [[list(atom), value] for atom, value in valuation.items()]}
    return None


def ideal_search(payload):
    """Halts iff the given universal clause theory is inconsistent.

    Mathematical unbounded-resource specification. No feasible completion or
    execution of the whole K_cl search is claimed. Do not catch MemoryError,
    RecursionError or interruption and treat them as a consistency verdict.
    """
    for count in itertools.count(1):
        clauses = tuple(ground_stage(payload, count))
        if ground_satisfiable(clauses) is None:
            return count


def write_payload(payload, out):
    out.mkdir(parents=True, exist_ok=True)
    name = payload["name"]
    (out / (name + ".json")).write_text(json.dumps(payload, indent=2) + "\n")
    lines = []
    tptp = ["% Finite class/closure kernel. Genuine equality; no finite-domain assumption.",
            "% A research proposal, not a TM state-count certificate."]
    for index, row in enumerate(payload["clauses"], 1):
        cl = row["literals"]
        prefix = "forall " + ",".join(clause_variables(cl)) + ": "
        lines.append(f"{index:02d} [{row['source']}] " + prefix + " | ".join(show_literal(l) for l in cl))
        tptp.append(f"cnf(k{index:02d},axiom,(" + " | ".join(show_literal(l, True) for l in cl) + ")).")
    (out / (name + ".txt")).write_text("\n".join(lines) + "\n")
    (out / (name + ".p")).write_text("\n".join(tptp) + "\n")
    return audit(payload)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=Path(__file__).resolve().parents[1] / "data")
    parser.add_argument("--run-whole-search", action="store_true",
                        help="opt in to the computationally prohibitive unbounded reference search")
    args = parser.parse_args()
    results = [write_payload(build(packed, branch), args.out)
               for packed in (False, True) for branch in ("direct", "predicate", "equality")]
    for branch in ("direct", "predicate"):
        for strategy in ("shared", "packed", "slice"):
            results.append(write_payload(compress(build(True, branch), strategy), args.out))
    for strategy in ("shared", "packed"):
        results.append(write_payload(compress(build(True, "equality"), strategy), args.out))
    results.append(write_payload(compress(build(), "shared", False), args.out))
    (args.out / "kernel_metrics.json").write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps(results, indent=2))
    if args.run_whole_search:
        print(ideal_search(build()))


if __name__ == "__main__":
    main()
