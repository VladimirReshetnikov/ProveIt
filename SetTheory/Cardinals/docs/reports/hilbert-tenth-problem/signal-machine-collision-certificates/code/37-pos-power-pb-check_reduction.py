#!/usr/bin/env python3
"""Fresh exact polynomial/Pell fixtures. No source-author or upstream code is run.

Only this file is executed. The retained source is read as bytes to check its pin.
No machine program, physical schedule, network request, or proof assistant occurs.
"""
from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path


class P:
    """Sparse integer polynomial: a monomial is a sorted tuple of variable names."""

    def __init__(self, terms=None):
        if isinstance(terms, int):
            terms = {(): terms}
        self.terms = {m: c for m, c in (terms or {}).items() if c}

    @staticmethod
    def variable(name):
        return P({(name,): 1})

    @staticmethod
    def coerce(other):
        return other if isinstance(other, P) else P(other)

    def __add__(self, other):
        result = self.terms.copy()
        for monomial, coefficient in self.coerce(other).terms.items():
            result[monomial] = result.get(monomial, 0) + coefficient
        return P(result)

    __radd__ = __add__

    def __neg__(self):
        return P({m: -c for m, c in self.terms.items()})

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other) + -self

    def __mul__(self, other):
        result = {}
        for a, ca in self.terms.items():
            for b, cb in self.coerce(other).terms.items():
                m = tuple(sorted(a + b))
                result[m] = result.get(m, 0) + ca * cb
        return P(result)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        assert isinstance(exponent, int) and exponent >= 0
        result = P(1)
        for _ in range(exponent):
            result = result * self
        return result

    def degree(self):
        return max(map(len, self.terms), default=-1)

    def variables(self):
        return set().union(*(set(m) for m in self.terms)) if self.terms else set()

    def substitute(self, assignment):
        result = P(0)
        for m, c in self.terms.items():
            term = P(c)
            for name in m:
                term *= assignment.get(name, P.variable(name))
            result += term
        return result

    def evaluate(self, assignment):
        return sum(c * math.prod(assignment[n] for n in m) for m, c in self.terms.items())

    def serialize(self):
        return [{"coefficient": c, "monomial": list(m)}
                for m, c in sorted(self.terms.items(), key=lambda item: (len(item[0]), item[0]))]


DIRECT = "o w M g x y u v s t q_b q_v J".split()
SLACKS = "d_wb d_wC d_yC".split()
QUOTIENTS = "q_alpha q_sigma q_tau q_r".split()
PAIRS = [("alpha_1", "alpha_2"), ("sigma_1", "sigma_2"),
         ("tau_1", "tau_2"), ("r_1", "r_2")]


def module(base, index, prefix="", old=False):
    natural = SLACKS + ([name for pair in PAIRS for name in pair] if old else QUOTIENTS)
    a = {name: P.variable(prefix + name) for name in DIRECT}
    for name in ["alpha", "beta"]:
        a[name] = P.variable(prefix + name + "_plus") + 1
    for name in natural:
        a[name] = P.variable(prefix + name + "_plus") - 1
    o, w, M, g, x, y, u, v, s, t, qb, qv, J = [a[n] for n in DIRECT]
    alpha, beta = a["alpha"], a["beta"]
    if old:
        fifth = beta + u*a["alpha_1"] - alpha - u*a["alpha_2"]
        seventh = s + u*a["sigma_1"] - x - u*a["sigma_2"]
        eighth = t + 4*y*a["tau_1"] - index - 4*y*a["tau_2"]
        last = x + M*a["r_1"] - y*(alpha-base) - base*o - M*a["r_2"]
    else:
        fifth = beta - alpha - u*a["q_alpha"]
        seventh = s - x - u*a["q_sigma"]
        eighth = t - index - 4*y*a["q_tau"]
        last = x - y*(alpha-base) - base*o - M*a["q_r"]
    residuals = [x*x-1-(alpha*alpha-1)*y*y,
                 u*u-1-(alpha*alpha-1)*v*v,
                 s*s-1-(beta*beta-1)*t*t,
                 beta-1-4*y*qb, fifth, v-y*y*qv, seventh, eighth,
                 y-index-a["d_yC"], w-base-a["d_wb"], w-index-a["d_wC"],
                 M-base*o-J, alpha*alpha-1-((w+1)*(w+1)-1)*(w*g)*(w*g),
                 2*alpha*base-M-(base*base+1), last]
    leaves = [prefix+n for n in DIRECT] + [prefix+n+"_plus" for n in ["alpha", "beta"]+natural]
    return residuals, leaves


def eliminated_module(base, index, count):
    """Literal new 16-, 14-, or 13-leaf alternatives; all aliases are expanded."""
    assert count in [16, 14, 13]
    direct = "o g u q_b q_v J".split()
    if count == 16:
        direct += ["v", "t"]
    natural = SLACKS + QUOTIENTS
    a = {name: P.variable(name) for name in direct}
    for name in natural:
        a[name] = P.variable(name+"_plus")-1
    leaves = direct + [name+"_plus" for name in natural]
    w, y = base+a["d_wb"], index+a["d_yC"]
    beta = 1+4*y*a["q_b"]
    v = a["v"] if count == 16 else y*y*a["q_v"]
    t = a["t"] if count == 16 else index+4*y*a["q_tau"]
    o, g, u, J = a["o"], a["g"], a["u"], a["J"]
    if count in [16, 14]:
        alpha = P.variable("alpha_plus")+1
        leaves.append("alpha_plus")
        M = 2*base*alpha-base*base-1
        x = y*(alpha-base)+base*o+M*a["q_r"]
        s = x+u*a["q_sigma"]
        residuals = [x*x-1-(alpha*alpha-1)*y*y,
                     u*u-1-(alpha*alpha-1)*v*v,
                     s*s-1-(beta*beta-1)*t*t,
                     beta-alpha-u*a["q_alpha"]]
        if count == 16:
            residuals += [v-y*y*a["q_v"], t-index-4*y*a["q_tau"]]
        residuals += [w-index-a["d_wC"], M-base*o-J,
                      alpha*alpha-1-((w+1)*(w+1)-1)*(w*g)*(w*g)]
    else:
        M, d = base*o+J, 2*base
        A = M+base*base+1
        X = y*(A-d*base)+d*base*o+d*M*a["q_r"]
        S = X+d*u*a["q_sigma"]
        residuals = [X*X-d*d-(A*A-d*d)*y*y,
                     d*d*u*u-d*d-(A*A-d*d)*v*v,
                     S*S-d*d-d*d*(beta*beta-1)*t*t,
                     d*beta-A-d*u*a["q_alpha"],
                     w-index-a["d_wC"],
                     A*A-d*d-d*d*((w+1)*(w+1)-1)*(w*g)*(w*g)]
    assert len(leaves) == count
    return residuals, leaves


def pell(parameter, index):
    """The elementary pair recurrence authored here from the displayed formula."""
    x, y = 1, 0
    for _ in range(index):
        x, y = parameter*x+(parameter*parameter-1)*y, x+parameter*y
    return x, y


def divide_nonnegative(numerator, denominator):
    assert denominator > 0 and numerator >= 0 and numerator % denominator == 0
    return numerator // denominator


def make_fixture(base, index):
    w = max(base, index)
    alpha, wg = pell(w+1, w)
    g = divide_nonnegative(wg, w)
    x, y = pell(alpha, index)
    u, v = pell(alpha, 2*index*y)
    assert math.gcd(u, 4*y) == 1
    beta = alpha + u * (((1-alpha)*pow(u, -1, 4*y)) % (4*y))
    s, t = pell(beta, index)
    o = base**(index-1)
    M = 2*alpha*base-base*base-1
    values = dict(o=o, w=w, M=M, g=g, x=x, y=y, u=u, v=v, s=s, t=t,
                  q_b=divide_nonnegative(beta-1, 4*y),
                  q_v=divide_nonnegative(v, y*y), J=M-base*o,
                  alpha=alpha, beta=beta, d_wb=w-base, d_wC=w-index, d_yC=y-index,
                  q_alpha=divide_nonnegative(beta-alpha, u),
                  q_sigma=divide_nonnegative(s-x, u),
                  q_tau=divide_nonnegative(t-index, 4*y),
                  q_r=divide_nonnegative(x-y*(alpha-base)-base*o, M))
    assert all(values[n] > 0 for n in DIRECT)
    assert values["alpha"] >= 2 and values["beta"] >= 2
    return values


def positive_adapters(values, prefix="", old=False):
    natural = SLACKS + ([name for pair in PAIRS for name in pair] if old else QUOTIENTS)
    result = {prefix+n: values[n] for n in DIRECT}
    result.update({prefix+n+"_plus": values[n]-1 for n in ["alpha", "beta"]})
    result.update({prefix+n+"_plus": values[n]+1 for n in natural})
    assert all(v > 0 for v in result.values())
    return result


def family_member(values, index, k):
    result = values.copy()
    u, y = result["u"], result["y"]
    result["beta"] += 4*y*u*k
    result["s"], result["t"] = pell(result["beta"], index)
    result["q_b"] = divide_nonnegative(result["beta"]-1, 4*y)
    result["q_alpha"] = divide_nonnegative(result["beta"]-result["alpha"], u)
    result["q_sigma"] = divide_nonnegative(result["s"]-result["x"], u)
    result["q_tau"] = divide_nonnegative(result["t"]-index, 4*y)
    return result


def square_sum(residuals):
    return sum((r*r for r in residuals), P(0))


def compressed(A, B, T, accepted):
    """Algebra only. Accepted indices are supplied, never found by an interpreter."""
    K, N = T+1, (T+1)**2
    d = math.factorial(N-1)
    j, r, s = [P.variable(n) for n in ["j", "r", "s"]]
    U, V = P(0), P(0)
    for i in range(1, N+1):
        basis = P((-1)**(N-i)*math.comb(N-1, i-1))
        for h in range(1, N+1):
            if h != i:
                basis *= j-h
        U += (1+(i-1)//K)*basis
        V += (1+(i-1)%K)*basis
    root = P(1)
    for i in range(1, N+1):
        root *= j-i
    acceptance = P(1)
    for i in sorted(accepted):
        assert 1 <= i <= N
        acceptance *= j-i
    return [root, (d*A-U)*(U-d*K), d*A-U-d*(r-1),
            (d*B-V)*(V-d*K), d*B-V-d*(s-1), acceptance]


def run():
    here = Path(__file__).resolve().parent
    source = (here/"dependencies/pell-source.lean").read_bytes()
    assert hashlib.sha256(source).hexdigest() == "993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a"
    receipts = {"scope": "Fresh exact polynomial and Pell fixtures; no upstream execution or machine simulation", "module_checks": []}
    C, B = P.variable("C"), P.variable("B")
    for label, base, external, degrees in [
        ("fixed_base_two", P(2), {"C"}, [4,4,4,2,2,3,2,2,1,1,1,1,6,1,2]),
        ("variable_base_B_plus_one", B+1, {"C", "B"}, [4,4,4,2,2,3,2,2,1,1,1,2,6,2,2])]:
        residuals, leaves = module(base, C)
        polynomial = square_sum(residuals)
        assert len(leaves) == len(set(leaves)) == 22 and len(residuals) == 15
        assert polynomial.variables() == set(leaves) | external
        assert [r.degree() for r in residuals] == degrees
        assert polynomial.degree() == 12
        top = {m: c for m, c in polynomial.terms.items() if len(m) == 12}
        assert top == {tuple(sorted(["w"]*8+["g"]*4)): 1}
        receipts["module_checks"].append(dict(label=label, positive_module_leaves_including_output=22,
            auxiliary_leaves_beyond_output=21, residuals=15, degree=12, residual_degrees=degrees,
            polynomial_monomials=len(polynomial.terms), leaves=leaves,
            top_monomial="w^8*g^4", top_coefficient=1))
        (here/"evidence"/(label+".polynomial.json")).write_text(json.dumps({
            "inputs": sorted(external), "positive_leaves": leaves,
            "residuals": [r.serialize() for r in residuals],
            "sum_of_squares": polynomial.serialize()}, indent=2)+"\n")

    # Algebraic new -> old embedding: old first natural values zero, second values q.
    old, old_leaves = module(B+1, C, old=True)
    new, _ = module(B+1, C)
    assert len(old_leaves) == 26
    embedding = {}
    for pair, q in zip(PAIRS, QUOTIENTS):
        embedding[pair[0]+"_plus"] = 1
        embedding[pair[1]+"_plus"] = P.variable(q+"_plus")
    assert all(not (o.substitute(embedding)-n).terms for o, n in zip(old, new))
    receipts["old_embedding_residual_identities"] = 15

    fixture_receipts, test_count, perturbations, maps = [], 0, 0, 0
    for base, index in [(2,1), (2,2), (3,1), (4,1), (5,1)]:
        values = make_fixture(base, index)
        residuals, leaves = module(P(base), C)
        old_residuals, _ = module(P(base), C, old=True)
        family_betas = []
        for k in [0, 1, 2, 9, 31]:
            current = family_member(values, index, k)
            assignment = positive_adapters(current) | {"C": index}
            assert all(r.evaluate(assignment) == 0 for r in residuals)
            family_betas.append(current["beta"])
            test_count += 1
            # Test both witness maps with genuinely nonzero common pair shifts.
            for shift in [0, 1, 7]:
                old_values = current.copy()
                for pair, q in zip(PAIRS, QUOTIENTS):
                    old_values[pair[0]] = shift
                    old_values[pair[1]] = current[q]+shift
                    assert old_values[pair[1]]-old_values[pair[0]] == current[q]
                old_assignment = positive_adapters(old_values, old=True) | {"C": index}
                assert all(r.evaluate(old_assignment) == 0 for r in old_residuals)
                maps += 1
        assert family_betas == sorted(set(family_betas))
        assignment = positive_adapters(values) | {"C": index}
        for leaf in leaves:
            changed = assignment.copy()
            changed[leaf] += 1
            assert any(r.evaluate(changed) != 0 for r in residuals)
            perturbations += 1
        fixture_receipts.append(dict(base=base, index=index, output=values["o"],
            family_parameters_tested=[0,1,2,9,31], largest_fixture_bit_length=max(v.bit_length() for v in values.values()),
            final_quotient=values["q_r"]))
    receipts["pell_fixtures"] = fixture_receipts
    receipts["complete_family_assignments_checked"] = test_count
    receipts["old_pair_shift_assignments_checked"] = maps
    receipts["single_leaf_perturbations_rejected"] = perturbations

    # The displayed C=1 infinite family is an exact polynomial identity in k.
    k = P.variable("k")
    values = make_fixture(2, 1)
    assignment = positive_adapters(values) | {"C": 1}
    assignment.update(beta_plus=16+2308*k, s=17+2308*k, q_b=4+577*k,
                      q_alpha_plus=1+4*k, q_sigma_plus=1+4*k)
    residuals, _ = module(P(2), C)
    assert all(not r.substitute(assignment).terms for r in residuals)
    receipts["exponent_zero_infinite_family_polynomial_identities"] = 15

    # Generic Pell recurrence identities in a symbolic parameter, finite n only.
    z = P.variable("z")
    for n in range(9):
        x, y = pell(z, n)
        assert not (x*x-(z*z-1)*y*y-1).terms
        assert P.coerce(x).evaluate({"z": 1}) == 1
        assert P.coerce(y).evaluate({"z": 1}) == n
    receipts["symbolic_pell_indices_checked"] = list(range(9))

    A, Bcounter = P.variable("A"), P.variable("Bcounter")
    left, left_leaves = module(P(2), A, "left_")
    right, right_leaves = module(P(2), Bcounter, "right_")
    gaps = [P.variable("g"+str(i)) for i in [1,2,3]]
    D = sum(gaps, P(0))
    gap_residuals = [(20*gaps[0]-D)*P.variable("left_o")-2*D,
                     (20*gaps[2]-D)*P.variable("right_o")-2*D]
    paid = gap_residuals + left + right
    decoding_leaves = {"A", "Bcounter"} | set(left_leaves) | set(right_leaves)
    assert len(decoding_leaves) == 46 and len(paid) == 32
    receipts["native_decoding"] = dict(positive_witnesses=46, residuals=32, external_inputs=3)
    composed = []
    for T, accepted in [(0, set()), (0, {1}), (1, set()), (1, set(range(1,5))),
                        (1, {1,3}), (2, set(range(1,10))), (2, {1,2,3})]:
        inner_residuals = compressed(A, Bcounter, T, accepted)
        inner = square_sum(inner_residuals)
        all_residuals = paid + inner_residuals
        total = square_sum(all_residuals)
        witnesses = decoding_leaves | {"j", "r", "s"}
        assert len(witnesses) == 49 and len(all_residuals) == 38
        assert total.variables() == witnesses | {"g1", "g2", "g3"}
        assert total.degree() == max(12, inner.degree())
        for prefix in ["left_", "right_"]:
            assert total.terms[tuple(sorted([prefix+"w"]*8+[prefix+"g"]*4))] == 1
        assignment = positive_adapters(values, "left_") | positive_adapters(values, "right_")
        assignment.update(A=1, Bcounter=1, j=1, r=1, s=1, g1=3, g2=14, g3=3)
        assert (total.evaluate(assignment) == 0) == (1 in accepted)
        composed.append(dict(T=T, accepted=sorted(accepted), positive_witnesses=49,
            total_variables=52, residual_slots=38, degree=total.degree(), inner_degree=inner.degree()))
    receipts["composed_instances"] = composed

    # Exact sparse verification of the further elimination alternatives.
    variants = []
    expected = {
        (16, False): [4,4,6,2,3,2,1,1,6],
        (16, True): [6,4,6,2,3,2,1,2,6],
        (14, False): [4,8,8,2,1,1,6],
        (14, True): [6,8,8,2,1,2,6],
        (13, False): [4,8,8,2,1,6],
        (13, True): [8,10,10,3,1,8],
    }
    for count in [16,14,13]:
        for variable_base in [False, True]:
            base = B+1 if variable_base else P(2)
            external = {"C", "B"} if variable_base else {"C"}
            residuals, leaves = eliminated_module(base, C, count)
            polynomial = square_sum(residuals)
            assert len(leaves) == len(set(leaves)) == count
            assert [r.degree() for r in residuals] == expected[(count, variable_base)]
            assert polynomial.variables() == set(leaves) | external
            degree = 12 if count == 16 else (20 if count == 13 and variable_base else 16)
            assert polynomial.degree() == degree
            if count == 16:
                leading = ["d_wb_plus"]*8+["g"]*4
            elif count == 14:
                leading = ["alpha_plus"]*4+["d_yC_plus"]*8+["q_v"]*4
            elif variable_base:
                leading = ["B"]*8+["d_yC_plus"]*8+["q_v"]*4
            else:
                leading = ["J"]*4+["d_yC_plus"]*8+["q_v"]*4
            assert len(leading) == degree
            assert polynomial.terms[tuple(sorted(leading))] == 1
            assignment_count = 0
            for fixture_base, fixture_index in [(2,1),(2,2),(3,1),(4,1),(5,1)]:
                if not variable_base and fixture_base != 2:
                    continue
                fixture = make_fixture(fixture_base, fixture_index)
                for k in [0,1,9]:
                    fixture_k = family_member(fixture, fixture_index, k)
                    full_assignment = positive_adapters(fixture_k)
                    assignment = {leaf: full_assignment[leaf] for leaf in leaves}
                    assignment["C"] = fixture_index
                    if variable_base:
                        assignment["B"] = fixture_base-1
                    assert all(r.evaluate(assignment) == 0 for r in residuals)
                    assignment_count += 1
            label = f"variant_{count}_"+("variable_base" if variable_base else "fixed_base_two")
            (here/"evidence"/(label+".polynomial.json")).write_text(json.dumps({
                "inputs": sorted(external), "positive_leaves": leaves,
                "residuals": [r.serialize() for r in residuals],
                "sum_of_squares": polynomial.serialize()}, indent=2)+"\n")
            variants.append(dict(label=label, positive_leaves_including_output=count,
                auxiliaries_beyond_output=count-1, residuals=len(residuals), degree=degree,
                residual_degrees=expected[(count,variable_base)], leaves=leaves,
                polynomial_monomials=len(polynomial.terms), full_assignments_checked=assignment_count,
                exact_degree_monomial=sorted(leading), exact_degree_coefficient=1))
    receipts["elimination_variants"] = variants

    # Generic polynomial identities behind all three eliminations.
    base = B+1
    alias = {n: P.variable(n+"_plus")-1 for n in SLACKS+QUOTIENTS}
    alpha = P.variable("alpha_plus")+1
    w, y = base+alias["d_wb"], C+alias["d_yC"]
    beta = 1+4*y*P.variable("q_b")
    M = 2*base*alpha-base*base-1
    x = y*(alpha-base)+base*P.variable("o")+M*alias["q_r"]
    s = x+P.variable("u")*alias["q_sigma"]
    substitution = {"w":w, "y":y, "beta_plus":beta-1, "M":M, "x":x, "s":s}
    r22, _ = module(base, C)
    r16, _ = eliminated_module(base, C, 16)
    kept22 = [0,1,2,4,5,7,10,11,12]
    assert all(not (r22[i].substitute(substitution)-r16[j]).terms for j,i in enumerate(kept22))
    assert all(not r22[i].substitute(substitution).terms for i in set(range(15))-set(kept22))
    r14, _ = eliminated_module(base, C, 14)
    vt = {"v":y*y*P.variable("q_v"), "t":C+4*y*alias["q_tau"]}
    kept16 = [0,1,2,3,6,7,8]
    assert all(not (r16[i].substitute(vt)-r14[j]).terms for j,i in enumerate(kept16))
    assert all(not r16[i].substitute(vt).terms for i in [4,5])
    r13, _ = eliminated_module(base, C, 13)
    modulus_gap = {"J":M-base*P.variable("o")}
    scales = [(0,4*base*base),(1,4*base*base),(2,4*base*base),(3,2*base),(4,P(1)),(6,4*base*base)]
    assert all(not (r13[j].substitute(modulus_gap)-scale*r14[i].substitute(modulus_gap)).terms
               for j,(i,scale) in enumerate(scales))
    assert not r14[5].substitute(modulus_gap).terms
    receipts["elimination_residual_identities"] = {"22_to_16":15,"16_to_14":9,"14_to_13_scaled":7}
    receipts["source_sha256"] = hashlib.sha256(source).hexdigest()
    receipts["checker_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    (here/"evidence/results.json").write_text(json.dumps(receipts, indent=2)+"\n")
    print(json.dumps({"status": "passed", "module_leaves": 22, "residuals": 15, "degree": 12,
        "family_assignments": test_count, "shift_maps": maps, "perturbations": perturbations,
        "compressed_instances": len(composed)}, indent=2))


if __name__ == "__main__":
    run()
