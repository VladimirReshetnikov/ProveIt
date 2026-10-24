#!/usr/bin/env python3
"""Independent exact audit of the direct signed arithmetic deliverable.

Does not import or execute a builder. Checks quotient sign implications,
all finite Pell/power/division interfaces, topological wire reconstruction,
every quadratic row, and the complete expanded sum of squares. The sparse
interface method follows the retained Round 12 mathematical audit, adapted
here to genuine signed arithmetic. No finite check proves the imported
unbounded Pell or refutation-calibration theorem.
"""
import argparse
import collections
import functools
import hashlib
import json
import pathlib
import re


def require(condition, label):
    if not condition:
        raise ValueError(label)


def plus(a, b, scalar=1):
    z = dict(a)
    for m, c in b.items():
        z[m] = z.get(m, 0) + scalar * c
        if not z[m]:
            del z[m]
    return z


def times(a, b):
    z = collections.defaultdict(int)
    for ma, ca in a.items():
        for mb, cb in b.items():
            z[tuple(sorted(ma + mb))] += ca * cb
    return {m: c for m, c in z.items() if c}


def decode(entries):
    result = {}
    for c, m in entries:
        t = tuple(m)
        require(isinstance(c, int) and c != 0 and t == tuple(sorted(t)),
                "canonical nonzero sparse term")
        require(t not in result, "duplicate sparse monomial")
        result[t] = c
    return result


def validate_graph(circuit):
    count = len(circuit["variable_names"])
    inputs = set(range(count))
    signed = set(circuit["unrestricted_inputs"])
    natural = set(circuit["nonnegative_inputs"])
    require(not signed & natural and signed | natural == inputs, "input domain partition")
    nodes = circuit["nodes"]
    for i, n in enumerate(nodes):
        require(n[0] in ("c", "v", "a", "s", "m"), "known arithmetic opcode")
        if n[0] == "c":
            require(len(n) == 2 and isinstance(n[1], int), "integer numeral")
        elif n[0] == "v":
            require(len(n) == 2 and n[1] in inputs, "declared semantic input")
        else:
            require(len(n) == 3 and all(isinstance(j, int) and 0 <= j < i for j in n[1:]),
                    "topological arithmetic node")
    live = {j for a, b, _ in circuit["equalities"] for j in (a, b)}
    require(all(0 <= i < len(nodes) for i in live), "equality node bounds")
    for i in reversed(range(len(nodes))):
        if i in live and nodes[i][0] in ("a", "s", "m"):
            live.update(nodes[i][1:])
    require(live == set(range(len(nodes))), "all pruned nodes live")
    require({nodes[i][1] for i in live if nodes[i][0] == "v"} == inputs,
            "all declared semantic inputs live")


def check_pruning(source, circuit):
    require(source["variable_names"] == circuit["variable_names"], "source semantic input identity")
    require(source["unrestricted_inputs"] == circuit["unrestricted_inputs"], "source input domain identity")
    nodes = source["nodes"]
    live = {j for a, b, _ in source["equalities"] for j in (a, b)}
    for i in reversed(range(len(nodes))):
        if i in live and nodes[i][0] in ("a", "s", "m"):
            live.update(nodes[i][1:])
    mapping = {old:new for new, old in enumerate(sorted(live))}
    expected_nodes = [nodes[i] if nodes[i][0] in ("v", "c")
                      else [nodes[i][0], *[mapping[j] for j in nodes[i][1:]]]
                      for i in sorted(live)]
    expected_equalities = [[mapping[a], mapping[b], label] for a, b, label in source["equalities"]]
    require(expected_nodes == circuit["nodes"] and expected_equalities == circuit["equalities"],
            "literal semantics-preserving dead-node pruning")


def compare_frontend(natural, signed):
    """Bind the already audited natural front end to the signed primitive calls.

    Pure-expression identities are compared compositionally, without expanding
    the large substituted Horn polynomial. Private congruence pairs are the
    only nonshared inputs; the finite primitive checks handle their signed
    residuals independently.
    """
    nnames, snames = natural["variable_names"], signed["variable_names"]
    stem = lambda name: name.rsplit(".", 1)[0] if re.search(r"\.\d+$", name) else name
    mapping = {}
    quotient_pairs = []
    old = new = 0
    while old < len(nnames):
        a = stem(nnames[old])
        require(new < len(snames), "signed semantic input sequence")
        b = stem(snames[new])
        if a.endswith(".q0"):
            require(old+1 < len(nnames) and stem(nnames[old+1]) == a[:-3]+".q1",
                    "adjacent private natural congruence pair")
            require(b == a[:-3]+".signed_q", "matching private signed quotient")
            quotient_pairs.append((old, old+1, new))
            old += 2
            new += 1
        else:
            require(a == b, "shared natural semantic input order")
            mapping[old] = new
            old += 1
            new += 1
    require(new == len(snames), "no unexplained signed semantic inputs")
    registry = {}
    def intern(key):
        if key not in registry:
            registry[key] = len(registry)
        return registry[key]
    def evaluator(data, reindex):
        @functools.lru_cache(None)
        def ev(i):
            n = data["nodes"][i]
            if n[0] == "c":
                return intern(("c", n[1]))
            if n[0] == "v":
                require(n[1] in reindex, "private congruence quotient absent from semantic interface")
                return intern(("v", reindex[n[1]]))
            require(n[0] in ("a", "m"), "semantic interface is a natural expression")
            a, b = ev(n[1]), ev(n[2])
            return intern((n[0], *sorted((a, b))))
        return ev
    ne = evaluator(natural, mapping)
    se = evaluator(signed, {i:i for i in range(len(snames))})
    nb, sb = natural["source_binding"], signed["source_binding"]
    require(set(nb) == set(sb), "source binding fields retained")
    scalar_fields = ["upper_e", "upper_f", "encoded_e", "encoded_f", "U", "index", "T", "Q",
                     "B", "modulus", "N_factorial", "scale_argument", "label_majorant",
                     "height_exponent", "height_power", "index_quotient"]
    for key in scalar_fields:
        if key in nb:
            require(ne(nb[key]) == se(sb[key]), "semantic source binding " + key)
    for key in ("upper_environment", "encoded_environment", "coordinate_bounds", "encoded_coordinates"):
        require([ne(i) for i in nb[key]] == [se(i) for i in sb[key]], "semantic source vector " + key)
    for key in ("endpoints", "coordinate_certificates"):
        require(len(nb[key]) == len(sb[key]), "source certificate list length")
        for a, b in zip(nb[key], sb[key]):
            require(set(a) == set(b), "source certificate fields")
            require(all(ne(a[k]) == se(b[k]) for k in a), "source certificate " + key)
    for a, b in zip(nb["majorant_branches"], sb["majorant_branches"]):
        require(a["name"] == b["name"] and a["guards"] == b["guards"], "majorant branch identity")
        for key in ("p", "q", "v"):
            require(ne(a[key]) == se(b[key]), "majorant branch label")
        require(set(a["bindings"]) == set(b["bindings"]), "majorant constructor binding set")
        require(all(ne(a["bindings"][k]) == se(b["bindings"][k]) for k in a["bindings"]),
                "majorant constructor values")
    nl, sl = natural["call_ledger"], signed["call_ledger"]
    require(len(nl) == len(sl), "all arithmetic calls retained")
    for a, b in zip(nl, sl):
        require(a["kind"] == b["kind"], "arithmetic call kind/order")
        require([ne(i) for i in a["arguments"]] == [se(i) for i in b["arguments"]],
                "exact arguments to each arithmetic primitive")
        if a["kind"] != "pell":
            ar = a["result"] if isinstance(a["result"], list) else [a["result"]]
            br = b["result"] if isinstance(b["result"], list) else [b["result"]]
            require([ne(i) for i in ar] == [se(i) for i in br], "arithmetic primitive result wiring")
    require(len(natural["equalities"]) == len(signed["equalities"]), "global equality count")
    row_congruence = None
    ordinary = 0
    for a, b in zip(natural["equalities"], signed["equalities"]):
        require(a[2] == b[2], "global equality label/order")
        if a[2] == "natural power":
            continue  # independently checked against its complete signed finite criterion
        if a[2] == "encoded row evaluation congruence":
            require(row_congruence is None, "unique row congruence")
            row_congruence = b
            continue
        require(ne(a[0]) == se(b[0]) and ne(a[1]) == se(b[1]), "unchanged ordinary global equality")
        ordinary += 1
    require(row_congruence is not None, "retained row congruence")
    q = [i for i, name in enumerate(snames) if name.startswith("row evaluation.signed_q.")]
    require(len(q) == 1, "private encoded-row signed quotient")
    sym = lambda name: Poly({(name,):1})
    cuts = {sb["encoded_e"]:sym("e"), sb["encoded_f"]:sym("f"), sb["B"]:sym("B")}
    @functools.lru_cache(None)
    def polynomial(i):
        if i in cuts:
            return cuts[i]
        n = signed["nodes"][i]
        if n[0] == "c":
            return Poly(n[1])
        if n[0] == "v":
            require(n[1] == q[0], "only private quotient in cut row congruence")
            return sym("q")
        a, b = polynomial(n[1]), polynomial(n[2])
        return a+b if n[0] == "a" else a-b if n[0] == "s" else a*b
    require(polynomial(row_congruence[0])-polynomial(row_congruence[1]) ==
            sym("e")+sym("B")*sym("q")-sym("f"), "exact signed row congruence")
    return {"natural_inputs":len(nnames), "signed_inputs":len(snames),
            "private_quotient_pairs_replaced":len(quotient_pairs),
            "arithmetic_calls_bound":len(nl), "ordinary_global_equalities":ordinary,
            "source_binding":"all parameters, bounds, height, CRT certificates and function-call arguments/results match exactly"}


def sign_check(circuit):
    nodes = circuit["nodes"]
    names = circuit["variable_names"]
    table = {tuple(n): i for i, n in enumerate(nodes)}
    require(len(table) == len(nodes), "unique interned nodes")
    equalities = {(a, b, label) for a, b, label in circuit["equalities"]}
    known = set(circuit["nonnegative_inputs"])
    records = circuit.get("sign_inference", [])
    inferred = set(circuit.get("inferred_nonnegative_inputs", []))
    require(inferred == {r["variable"] for r in records} and len(inferred) == len(records),
            "complete nonduplicated inference ledger")

    def existing(op, a, b):
        if op in ("a", "m"):
            a, b = sorted((a, b))
        key = (op, a, b)
        require(key in table, "required literal arithmetic node")
        return table[key]

    for r in sorted(records, key=lambda item: item["variable"]):
        require(r["rule"] == "euclidean_quotient", "known sign rule")
        q = r["variable"]
        require(q not in known and names[q].startswith("division.quotient."),
                "new Euclidean quotient inference")
        qnode = table[("v", q)]
        dividend, divisor, remainder, slack = [r[k + "_node"] for k in
                                               ("dividend", "divisor", "remainder", "slack")]

        @functools.lru_cache(None)
        def nonnegative(i):
            node = nodes[i]
            if node[0] == "c":
                return node[1] >= 0
            if node[0] == "v":
                return node[1] in known
            if node[0] in ("a", "m"):
                return nonnegative(node[1]) and nonnegative(node[2])
            return node[1] == node[2]

        require(nonnegative(dividend), "previously justified nonnegative dividend")
        require(nonnegative(remainder) and nonnegative(slack), "retained remainder/slack signs")
        rhs = existing("a", existing("m", qnode, divisor), remainder)
        bound = existing("a", existing("a", remainder, slack), table[("c", 1)])
        require((dividend, rhs, "division equation") in equalities, "exact Euclidean equation")
        require((divisor, bound, "positive divisor/remainder bound") in equalities,
                "exact positive divisor and strict remainder bound")
        known.add(q)

    private_signed = set(circuit["unrestricted_inputs"]) - inferred
    require(all(re.fullmatch(r".*\.signed_q\.\d+", names[j]) for j in private_signed),
            "every other unrestricted semantic input is a congruence quotient")
    return {"inferred_nonnegative_quotients": len(inferred),
            "private_signed_congruence_quotients": len(private_signed),
            "reason": "q<0 would give n=qd+r <= -d+r=-s-1<0; dividends checked in dependency order"}


class Poly:
    def __init__(self, value):
        self.d = value if isinstance(value, dict) else ({(): value} if value else {})
    def __add__(self, other):
        other = other if isinstance(other, Poly) else Poly(other)
        return Poly(plus(self.d, other.d))
    __radd__ = __add__
    def __neg__(self):
        return Poly({m: -c for m, c in self.d.items()})
    def __sub__(self, other):
        return self + -(other if isinstance(other, Poly) else Poly(other))
    def __rsub__(self, other):
        return Poly(other) - self
    def __mul__(self, other):
        other = other if isinstance(other, Poly) else Poly(other)
        return Poly(times(self.d, other.d))
    __rmul__ = __mul__
    def __pow__(self, n):
        out = Poly(1)
        for _ in range(n):
            out = out * self
        return out
    def __eq__(self, other):
        return self.d == (other.d if isinstance(other, Poly) else Poly(other).d)


def interfaces(source):
    nodes, names, ledger, eqs = [source[k] for k in ("nodes", "variable_names", "call_ledger", "equalities")]
    symbol = lambda s: Poly({(s,): 1})
    norm = lambda a, x, y: x*x + y*y - a*a*y*y - 1
    sos = lambda items: sum((p*p for p in items), Poly(0))
    counts = collections.Counter()
    for ci, call in enumerate(ledger):
        kind = call["kind"]
        if kind not in ("pell", "pow", "divmod"):
            continue
        cuts = {i: symbol("argument" + str(i)) for i in call["arguments"] if nodes[i][0] != "c"}
        nested = []
        if kind == "pow":
            nested = [p for p in ledger if p["kind"] == "pell"
                      and call["before"][0] <= p["before"][0]
                      and p["after"][0] <= call["after"][0]]
            require(len(nested) == 1, "one indexed Pell call per power criterion")
            require(isinstance(nested[0]["result"], int), "signed Pell result")
            cuts[nested[0]["result"]] = symbol("Pell_criterion")

        @functools.lru_cache(None)
        def evaluate(i):
            if i in cuts:
                return cuts[i]
            n = nodes[i]
            if n[0] == "c":
                return Poly(n[1])
            if n[0] == "v":
                return symbol("variable" + str(n[1]))
            a, b = evaluate(n[1]), evaluate(n[2])
            return a+b if n[0] == "a" else a-b if n[0] == "s" else a*b

        vs = {names[i].rsplit(".", 1)[0]: symbol("variable" + str(i))
              for i in range(call["before"][0], call["after"][0])}
        v = lambda name: vs[name]
        mod = lambda a, b, m, name: a + m*v(name + ".signed_q") - b
        le = lambda a, b, name: b-a-v(name + ".slack")
        lt = lambda a, b, name: b-a-1-v(name + ".slack")
        if kind == "pell":
            a, n, x, y = map(evaluate, call["arguments"])
            u, w, s, t, b = [v("pell." + k) for k in ("u", "w", "s", "t", "b")]
            finite = sos([norm(a,x,y), norm(a,u,w), norm(b,s,t), lt(1,b,"pell.b"),
                          mod(b,1,4*y,"pell.by"), mod(b,a,u,"pell.ba"), lt(0,w,"pell.w"),
                          w-y*y*v("pell.dvd"), mod(s,x,u,"pell.sx"), mod(t,n,4*y,"pell.tn")])
            expected = sos([lt(1,a,"pell.a"), le(n,y,"pell.n")]) + sos([x-1,y])*finite
            actual = evaluate(call["result"])
        elif kind == "pow":
            n, k = map(evaluate, call["arguments"])
            m = evaluate(call["result"])
            w, a, t, z, x, y, d = [v("power." + s) for s in
                                    ("w", "a", "t", "z", "x", "y", "truncated_difference")]
            truncated = (a-d-n)**2 * sos([le(a,n,"power.sub"), d])
            finite = evaluate(nested[0]["result"]) + truncated + sos([
                mod(x,y*d+m,t,"power.mod"), 2*a*n-t-n*n-1, lt(m,t,"power.mt"),
                le(n,w,"power.nw"), le(k,w,"power.kw"), norm(w+1,a,w*z)])
            expected = sos([k,m-1]) * (lt(0,k,"power.k")**2 + sos([n,m]) *
                                      (lt(0,n,"power.n")**2 + finite))
            row = eqs[call["after"][1]-1]
            require(row[2] == "natural power", "power equality label")
            actual = evaluate(row[0])-evaluate(row[1])
        else:
            n, d = map(evaluate, call["arguments"])
            q, r = map(evaluate, call["result"])
            s = v("division.slack")
            rows = eqs[call["before"][1]:call["after"][1]]
            require(len(rows) == 2, "two Euclidean rows")
            require(evaluate(rows[0][0])-evaluate(rows[0][1]) == n-q*d-r,
                    "exact Euclidean quotient/remainder polynomial")
            expected = d-r-s-1
            actual = evaluate(rows[1][0])-evaluate(rows[1][1])
        require(expected == actual, "exact finite arithmetic interface " + str(ci) + " " + kind)
        counts[kind] += 1
    return dict(counts)


def check_quartic(circuit, rows, polynomial):
    forms = []
    nextvar = len(circuit["variable_names"])
    row_index = 0
    nonlinear = affine = 0

    def verify_row(expected, label):
        nonlocal row_index
        require(row_index < len(rows) and rows[row_index]["label"] == label, "ordered residual " + label)
        require(decode(rows[row_index]["terms"]) == expected, "exact residual " + label)
        row_index += 1

    for i, n in enumerate(circuit["nodes"]):
        if n[0] == "c":
            form = {(): n[1]} if n[1] else {}
        elif n[0] == "v":
            form = {(n[1],): 1}
        elif n[0] in ("a", "s"):
            form = plus(forms[n[1]], forms[n[2]], 1 if n[0] == "a" else -1)
        else:
            value = times(forms[n[1]], forms[n[2]])
            if any(len(m) >= 2 for m in value):
                form = {(nextvar,): 1}
                nextvar += 1
                verify_row(plus(form, value, -1), "nonlinear gate " + str(i))
                nonlinear += 1
            else:
                form = value
        label = "affine support barrier " + str(i)
        if row_index < len(rows) and rows[row_index]["label"] == label:
            value = form
            require(all(len(m) <= 1 for m in value), "retained affine definition")
            form = {(nextvar,): 1}
            nextvar += 1
            verify_row(plus(form, value, -1), label)
            affine += 1
        require(all(len(m) <= 1 for m in form), "every substituted wire is affine")
        forms.append(form)
    for a, b, label in circuit["equalities"]:
        verify_row(plus(forms[a], forms[b], -1), label)
    for j in circuit["nonnegative_inputs"]:
        a, b, c = nextvar, nextvar+1, nextvar+2
        nextvar += 3
        expected = {(j,):1, (a,a):-1, (b,b):-1, (c,c):-1, (c,):-1}
        verify_row(expected, "semantic nonnegativity " + str(j))
    require(row_index == len(rows), "no unexplained residuals")
    require(nextvar == polynomial["variable_count"], "complete quantified coordinate count")
    require(polynomial["domain"] == "unrestricted integers", "explicit integer domain")

    # Independent triangular squaring: each unordered pair contributes once,
    # with coefficient doubled off the diagonal.
    collected = collections.defaultdict(int)
    for row in rows:
        terms = list(decode(row["terms"]).items())
        require(all(len(m) <= 2 for m, _ in terms), "quadratic residual degree")
        for i, (ma, ca) in enumerate(terms):
            for j in range(i, len(terms)):
                mb, cb = terms[j]
                collected[tuple(sorted(ma+mb))] += ca*cb*(1 if i == j else 2)
    exact = {m:c for m,c in collected.items() if c}
    require(exact == decode(polynomial["terms"]), "complete collected sum-of-squares polynomial")
    require(max(map(len, exact)) == 4, "exact degree four")
    require({i for m in exact for i in m} == set(range(nextvar)), "all final quantified variables live")
    return {"integer_variables": nextvar, "nonlinear_wires": nonlinear,
            "retained_affine_wires": affine, "quadratic_residuals": len(rows),
            "expanded_monomials": len(exact), "exact_degree": 4,
            "max_abs_coefficient": max(map(abs, exact.values()))}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("directory", type=pathlib.Path)
    parser.add_argument("--receipt", type=pathlib.Path)
    parser.add_argument("--natural-source", type=pathlib.Path)
    args = parser.parse_args()
    files = ["circuit_integer.json", "residuals_integer.json", "equation_integer.json",
             "source_circuit_before_pruning.json"]
    circuit, rows, polynomial, source = [json.loads((args.directory / f).read_text()) for f in files]
    validate_graph(circuit)
    check_pruning(source, circuit)
    signs = sign_check(circuit)
    primitive_counts = interfaces(source)
    binding = compare_frontend(json.loads(args.natural_source.read_text()), source) if args.natural_source else None
    quartic = check_quartic(circuit, rows, polynomial)
    result = {"status":"PASS", "method":"exact integer polynomial identities; no sampled arithmetic",
              "sign_inference":signs, "finite_arithmetic_interfaces":primitive_counts,
              "natural_to_signed_source_binding":binding,
              "quartic":quartic,
              "scope":"Validates signed primitives, sign implications, wire maps, all residuals and full sparse quartic. Imports correctness of the unbounded Pell/CRT and logical source theorems.",
              "sha256":{f:hashlib.sha256((args.directory/f).read_bytes()).hexdigest() for f in files}}
    if args.natural_source:
        result["sha256"]["natural_source_circuit"] = hashlib.sha256(args.natural_source.read_bytes()).hexdigest()
    if args.receipt:
        args.receipt.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
