"""Independent audit of the short positive polynomials.

Read circuit JSON and fixed coefficient bytes only; do not import or execute
either the producer or its checker. Symbolic leaders are exact over Z with
the four coefficient ports as degree-zero indeterminates. Any cancellation
of top forms triggers full symbolic expansion of that node's ancestry.
"""
from pathlib import Path
from collections import Counter
from functools import lru_cache
import gzip
import hashlib
import json
import math
import random
import sympy as sp

HERE = Path(__file__).resolve().parent
BASE = HERE.parent / "positive"
NATIVE = HERE.parent / "native"
PORTS = ["beta", "K0", "MC", "MF"]
EXPECTED = {
    "p66_degree157": (66, 38, 15, 13, 157),
    "p68_degree101": (68, 38, 16, 14, 101),
    "p70_degree80": (70, 39, 17, 14, 80),
    "p71_degree78": (71, 40, 17, 14, 78),
    "p72_degree64": (72, 40, 18, 14, 64),
    "p73_degree62": (73, 41, 18, 14, 62),
    "p70_degree84": (70, 39, 17, 14, 84),
    "p73_degree68": (73, 40, 18, 15, 68),
}


def require(ok, why):
    if not ok:
        raise ValueError(why)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def operate(op, a, b):
    return a+b if op == "+" else a-b if op == "-" else a*b


def bind_coefficients():
    binding = json.loads((NATIVE / "COEFFICIENT_BINDING.json").read_text())
    out, receipt = {}, []
    for alias, name in [("beta", "beta"), ("K0", "K"), ("MC", "MC"), ("MF", "MF_source")]:
        require(binding["binding"][alias] == name+".bin.gz", "binding filename")
        record = next(r for r in binding["ports"] if r["name"] == name)
        compressed = (NATIVE / (name+".bin.gz")).read_bytes()
        raw = gzip.decompress(compressed)
        value = int.from_bytes(raw, "little")
        require(sha(compressed) == record["gzip_sha256"], "compressed coefficient hash")
        require(sha(raw) == record["sha256"], "raw coefficient hash")
        require(len(raw) == record["bytes"] and value.bit_length() == record["bits"], "coefficient dimensions")
        require(value > 0, "positive coefficient")
        out[alias] = value
        receipt.append({"alias": alias, "bound_name": name, "raw_sha256": sha(raw),
                        "gzip_sha256": sha(compressed), "bits": value.bit_length(), "bytes": len(raw)})
    beta = out["beta"]
    exponent = binding["native_base_exponent"]
    native_mf = out["MF"] - beta
    require(exponent == 429959 and beta == 2**exponent-1, "native base")
    require(0 < native_mf < beta and 0 < out["MC"] < beta, "native mask ranges")
    require(out["MC"] % 4 == 2 and native_mf % 8 == 4, "native low-mask phase")
    require(out["MC"].bit_count()+native_mf.bit_count() == exponent, "native mask population")
    return out, receipt


def validate_dag(obj, path):
    names = obj["witnesses"]+obj["fixed_numerals"]
    require(len(obj["witnesses"]) == 15 and len(set(names)) == 19, "input dimensions")
    require(obj["fixed_numerals"] == PORTS, "fixed port names")
    seen = set(names)
    for node, op, a, b in obj["source"]:
        require(node not in seen and op in ["+", "-", "*"], "DAG producer")
        require(all(isinstance(x, int) or isinstance(x, str) and x in seen for x in [a, b]), "DAG operand")
        seen.add(node)
    need = {obj["output"]}
    for node, op, a, b in reversed(obj["source"]):
        if node in need:
            need.update(x for x in [a, b] if isinstance(x, str))
    require(seen == need, "all gates and all input ports must be live")
    counts = Counter(row[1] for row in obj["source"])
    expect = EXPECTED[obj["name"]]
    require((len(obj["source"]), counts["*"], counts["+"], counts["-"], obj["exact_degree"]) == expect, "independent expected ledger")
    require(obj["operations"] == len(obj["source"]) and obj["operation_counts"] == dict(counts), "metadata ledger")
    b = obj["coefficient_binding"]
    require((path.parent/b["file"]).resolve() == (NATIVE/"COEFFICIENT_BINDING.json").resolve(), "whole binding target")
    require(b["aliases"] == {"beta": "beta", "K0": "K", "MC": "MC", "MF": "MF_source"}, "whole binding aliases")
    return dict(counts)


def symbolic_macro_checks(obj):
    """Exact identity checks at cuts, independent of coefficient specialization."""
    names = obj["witnesses"] + PORTS
    sym = {n: sp.Symbol(n) for n in names}
    for n in ["q", "X", "Y", "E", "k", "ell", "c", "a", "H", "Delta", "D", "R", "V", "I", "A0", "N0", "N1", "Na", "Nk", "Nt", "Ns", "S"]:
        sym.setdefault(n, sp.Symbol(n))
    v = sym.copy()
    q, X, Y, E, k, ell, c, a, H, Delta, D, R, V, I, A0, N0, N1, Na, Nk, Nt, Ns, S = [sym[n] for n in ["q", "X", "Y", "E", "k", "ell", "c", "a", "H", "Delta", "D", "R", "V", "I", "A0", "N0", "N1", "Na", "Nk", "Nt", "Ns", "S"]]
    f, T, y = sym["f"], sym["T"], sym.get("y", sp.Symbol("y"))
    macros = {
        "q": (q, sym["beta"]*sym["J"]+1),
        "X": (X, sym["w"]*q), "Y": (Y, sym["s"]*q**3),
        "E": (E, X*Y), "k": (k, sym["eta"]+sym["zeta"]),
        "ell": (ell, E*k*Y), "c": (c, k*Y+sym["eta"]),
        "a": (a, E+Y), "H": (H, 4*a+3), "Delta": (Delta, a*a+H),
        "main_root": (D, X+a*c+sym["gamma"]*H),
        "N1": (N1, D*D-Delta*c*c),
        "R": (R, ((q-1)*(q-sym["F"])+sym["alpha"])*(q*q-1)+(sym["MC"]+q*sym["MF"])*sym["J"]),
        "Nk": (Nk, k-sym["h"]*E-R),
        "Nt": (Nt, (sym["K0"]+sym["w"])*(q-sym["F"]-sym["alpha"])+q-sym["F"]-sym["z"]*(q-1)),
        "V": (V, f*f*(c*T-R)-c if obj["squared_modulus"] else c*(T*f-1)-R*f*f),
        "I": (I, sym["i"]*c*c), "A0": (A0, Delta*(f*f-1)),
        "normalized_S": (S, Delta*sym["i"]*c*c),
    }
    if obj["first_gap"]:
        r = sym["r"]
        macros["N0"] = (N0, r*r+ell*(2*r-k))
    else:
        macros["N0"] = (N0, sym["tau"]**2-ell*(ell+k))
    if obj["finalizer"] == "normalized_scaled_product":
        macros["Na"] = (Na, S*S*(V*V-y*y)+y*y)
        macros["scaled_Ns"] = (Ns, Delta*f*f-S*S)
        output = N0*N1*Na*Nk*Nt*Ns-Delta
    else:
        if obj["auxiliary_gap"]:
            u = sym["u"]
            macros["Na"] = (Na, (V+u)**2-A0*u*(2*V+u))
        else:
            macros["Na"] = (Na, A0*(V*V-y*y)+y*y)
        if obj["finalizer"] == "ordinary_minimum3":
            output = (N0*N1)**2+(Na*Nk*Nt)*(Na*Nk*Nt-2)+(I*I-A0)**2
        elif obj["finalizer"] == "ordinary_product":
            macros["Ns"] = (Ns, 1+I*I-A0)
            output = N0*N1*Na*Nk*Nt*Ns-1
        elif obj["finalizer"] == "normalized_minimum4":
            macros["Ns"] = (Ns, f*f-Delta*I*I)
            output = N0*N0+Na*Na+Ns*Ns+(N1*Nk*Nt-1)**2-3
        else:
            raise ValueError("unknown finalizer")
    checked = []
    for node, op, lhs, rhs in obj["source"]:
        lhs = v[lhs] if isinstance(lhs, str) else sp.Integer(lhs)
        rhs = v[rhs] if isinstance(rhs, str) else sp.Integer(rhs)
        v[node] = operate(op, lhs, rhs)
        if node in macros:
            atom, expected = macros[node]
            require(sp.expand(v[node]-expected) == 0, ("exact macro identity", obj["name"], node))
            v[node] = atom
            checked.append(node)
            if node == "q":
                v["qm"] = q-1
    require(sp.expand(v[obj["output"]]-output) == 0, "exact finalizer identity")
    return checked+["finalizer"]


def exact_degree_audit(obj):
    inputs = obj["witnesses"]+PORTS
    symbols = {n: sp.Symbol(n) for n in inputs}
    generators = [symbols[n] for n in inputs]
    witness_count = len(obj["witnesses"])
    rows = {r[0]: r for r in obj["source"]}
    expanded_nodes = []

    def leading(expr):
        poly = sp.Poly(sp.expand(expr), *generators)
        if poly.is_zero:
            return (-1, sp.Integer(0))
        d = max(sum(powers[:witness_count]) for powers, coeff in poly.terms())
        terms = [(powers, coeff) for powers, coeff in poly.terms() if sum(powers[:witness_count]) == d]
        h = sum(coeff*sp.prod(g**e for g, e in zip(generators, powers)) for powers, coeff in terms)
        return d, h

    @lru_cache(None)
    def full(n):
        if isinstance(n, int):
            return sp.Integer(n)
        if n in symbols:
            return symbols[n]
        node, op, a, b = rows[n]
        return sp.expand(operate(op, full(a), full(b)))

    state = {n: leading(e) for n, e in symbols.items()}
    for node, op, a, b in obj["source"]:
        da, la = state[a] if isinstance(a, str) else leading(a)
        db, lb = state[b] if isinstance(b, str) else leading(b)
        if op == "*":
            degree, lead = da+db, sp.expand(la*lb)
        else:
            degree = max(da, db)
            lead = sp.expand((la if da == degree else 0)+(1 if op == "+" else -1)*(lb if db == degree else 0))
            if lead == 0:
                previous = degree
                degree, lead = leading(full(node))
                expanded_nodes.append({"node": node, "cancelled_upper_degree": previous,
                                       "exact_degree": degree, "full_monomials": len(sp.Poly(full(node), *generators).terms()),
                                       "expanded_polynomial_sha256": sha(str(full(node)).encode())})
        require(lead != 0, ("unexpected zero polynomial", node))
        state[node] = degree, lead
    require(state[obj["output"]][0] == obj["exact_degree"], "exact output degree")
    require(expanded_nodes and all(r["node"] == "N1" and r["cancelled_upper_degree"] == 22 and r["exact_degree"] == 18 for r in expanded_nodes), "main-norm cancellation")
    q0 = symbols["beta"]*symbols["J"]
    k0 = symbols["eta"]+symbols["zeta"]
    E0 = symbols["w"]*symbols["s"]*q0**4
    c0 = k0*symbols["s"]*q0**3
    ell0 = k0*symbols["w"]*symbols["s"]**2*q0**7
    T0 = symbols["w"]*(q0-symbols["F"]-symbols["alpha"])-symbols["z"]*q0
    h, gamma, i, T, f = [symbols[n] for n in ["h", "gamma", "i", "T", "f"]]
    expected = {
        "p66_degree157": -8*q0**91*h*gamma*i**4*k0**13*symbols["w"]**13*symbols["s"]**26*T*T*f**4*T0,
        "p68_degree101": 8*h*gamma*i*i*ell0**2*E0**5*c0**7*T*T*f**6*T0,
        "p70_degree80": 64*gamma*gamma*E0**4*c0*c0*ell0**4,
        "p71_degree78": h*h*E0**6*c0**4*T**4*f**12*T0*T0,
        "p73_degree68": i**4*E0**4*c0**8,
    }
    if "u" in symbols:
        u = symbols["u"]
        expected.update({
            "p72_degree64": 4*h*h*E0**6*c0*c0*T*T*f**8*u*u*T0*T0,
            "p73_degree62": 4*h*h*E0**6*c0*c0*T*T*f**6*u*u*T0*T0,
            "p70_degree84": 16*gamma*h*i*i*ell0*(2*symbols["r"]-k0)*E0**5*c0**6*T*f**4*u*T0,
        })
    require(sp.expand(state[obj["output"]][1]-expected[obj["name"]]) == 0, "independently derived full leading form")
    monomial_specs = {
        "p66_degree157": ({"J": 92, "h": 1, "gamma": 1, "i": 4, "eta": 13, "w": 13, "s": 26, "T": 2, "f": 4, "z": 1}, 8, 92),
        "p68_degree101": ({"J": 56, "h": 1, "gamma": 1, "i": 2, "eta": 9, "w": 7, "s": 16, "T": 2, "f": 6, "z": 1}, -8, 56),
        "p70_degree80": ({"J": 50, "gamma": 2, "eta": 6, "w": 8, "s": 14}, 64, 50),
        "p71_degree78": ({"J": 38, "h": 2, "eta": 4, "w": 6, "s": 10, "T": 4, "f": 12, "z": 2}, 1, 38),
        "p72_degree64": ({"J": 32, "h": 2, "eta": 2, "w": 6, "s": 8, "T": 2, "f": 8, "u": 2, "z": 2}, 4, 32),
        "p73_degree62": ({"J": 32, "h": 2, "eta": 2, "w": 6, "s": 8, "T": 2, "f": 6, "u": 2, "z": 2}, 4, 32),
    }
    distinguished = None
    if obj["name"] in monomial_specs:
        powers, scalar, exponent = monomial_specs[obj["name"]]
        monomial = sp.prod(symbols[n]**e for n, e in powers.items())
        coeff = sp.Poly(state[obj["output"]][1], *generators[:witness_count]).coeff_monomial(monomial)
        require(coeff == scalar*symbols["beta"]**exponent, "exact distinguished coefficient")
        distinguished = {"witness_exponents": powers, "coefficient": str(coeff), "nonzero_for_bound_positive_beta": True}
    selected = ["N0", "N1", "V", "I", "A0", "Na", "Nk", "Nt", "Ns", "scaled_Ns", "strong_residual", "first_main", "aux_index_transport", obj["output"]]
    return {"exact_degree": state[obj["output"]][0], "cancellation_expansions": expanded_nodes,
            "node_degrees": {n: state[n][0] for n in selected if n in state},
            "exact_leading_form": str(sp.factor(state[obj["output"]][1])),
            "leader_terms": len(sp.Poly(state[obj["output"]][1], *generators).terms()),
            "distinguished_actual_coefficient": distinguished}


def eval_circuit(obj, values, modulus):
    v = values.copy()
    for n, op, a, b in obj["source"]:
        a = v[a] if isinstance(a, str) else a
        b = v[b] if isinstance(b, str) else b
        v[n] = operate(op, a, b) % modulus
    return v[obj["output"]]


def direct_formula(obj, v, modulus):
    q = v["beta"]*v["J"]+1
    X, Y, k = v["w"]*q, v["s"]*q**3, v["eta"]+v["zeta"]
    E, c = X*Y, k*Y+v["eta"]
    a, ell = E+Y, E*k*Y
    Delta, H = (a+2)**2-1, 4*a+3
    D = X+a*c+v["gamma"]*H
    R = ((q-1)*(q-v["F"])+v["alpha"])*(q*q-1)+(v["MC"]+q*v["MF"])*v["J"]
    f, T, I = v["f"], v["T"], v["i"]*c*c
    V = f*f*(c*T-R)-c if obj["squared_modulus"] else c*(T*f-1)-R*f*f
    A0 = Delta*(f*f-1)
    tau = ell+v["r"] if obj["first_gap"] else v["tau"]
    y = V+v["u"] if obj["auxiliary_gap"] else v["y"]
    N0, N1 = tau*tau-ell*(ell+k), D*D-Delta*c*c
    Nk = k-v["h"]*E-R
    Nt = (v["K0"]+v["w"])*(q-v["F"]-v["alpha"])+q-v["F"]-v["z"]*(q-1)
    Na = A0*(V*V-y*y)+y*y
    if obj["finalizer"] == "ordinary_minimum3":
        answer = (N0*N1)**2+(Na*Nk*Nt-1)**2+(I*I-A0)**2-1
    elif obj["finalizer"] == "ordinary_product":
        answer = N0*N1*Na*Nk*Nt*(1+I*I-A0)-1
    elif obj["finalizer"] == "normalized_minimum4":
        answer = N0*N0+Na*Na+(f*f-Delta*I*I)**2+(N1*Nk*Nt-1)**2-3
    else:
        S2 = Delta*Delta*I*I
        answer = N0*N1*(S2*(V*V-y*y)+y*y)*Nk*Nt*(Delta*f*f-S2)-Delta
    return answer % modulus


def affine_replay(obj, coefficients, prime, seed):
    rng = random.Random(seed)
    v = {n: [rng.randrange(1, 21), rng.randrange(1, 21)] for n in obj["witnesses"]}
    v.update({n: [coefficients[n] % prime] for n in PORTS})
    for n, op, a, b in obj["source"]:
        a = v[a] if isinstance(a, str) else [a]
        b = v[b] if isinstance(b, str) else [b]
        if op == "*":
            out = [0]*(len(a)+len(b)-1)
            for j, x in enumerate(a):
                for k, y in enumerate(b):
                    out[j+k] = (out[j+k]+x*y) % prime
        else:
            out = [((a[j] if j < len(a) else 0)+(1 if op == "+" else -1)*(b[j] if j < len(b) else 0)) % prime for j in range(max(len(a), len(b)))]
        while len(out) > 1 and out[-1] == 0:
            out.pop()
        v[n] = out
    out = v[obj["output"]]
    require(len(out)-1 == obj["exact_degree"], "actual-port affine specialization degree")
    return {"prime": prime, "seed": seed, "degree": len(out)-1, "leading_residue": out[-1]}


def pell(a, n):
    # Independent binary powering of the matrix [[a,a*a-1],[1,a]].
    D = a*a-1
    def mul(x, y):
        return x[0]*y[0]+D*x[1]*y[1], x[0]*y[1]+x[1]*y[0]
    ans, power = (1, 0), (a, 1)
    while n:
        if n % 2:
            ans = mul(ans, power)
        power = mul(power, power)
        n //= 2
    return ans


def auxiliary_checks():
    X, a, t = sp.symbols("X a t")
    A, B, C, ell, r, k, V, u, A0, c, gamma, H, R, f, T = sp.symbols("A B C ell r k V u A0 c gamma H R f T")
    identities = {
        "minimum_completion": A*A+B*(B-2)+C*C-(A*A+(B-1)**2+C*C-1),
        "first_gap": (ell+r)**2-ell*(ell+k)-(r*r+ell*(2*r-k)),
        "auxiliary_gap": (V+u)**2-A0*u*(2*V+u)-(A0*(V*V-(V+u)**2)+(V+u)**2),
        "squared_quotient_pullback": c*((f*T)*f-1)-R*f*f-(f*f*(c*T-R)-c),
        "main_norm_cancel": (X+a*c+gamma*H)**2-(a*a+H)*c*c-(2*a*c*(X+gamma*H)+(X+gamma*H)**2-H*c*c),
    }
    for name, difference in identities.items():
        require(sp.expand(difference) == 0, ("universal local identity", name))
    q = [sp.Integer(1), 4*X-3]
    for j in range(2, 16):
        q.append(sp.expand((4*X-2)*q[-1]-q[-2]))
    for j, poly in enumerate(q):
        n = 2*j+1
        require(poly.subs(X, 0) == (-1)**j*n, "odd-index constant term")
        chi, psi = sp.Integer(1), sp.Integer(0)
        for unused in range(n):
            chi, psi = sp.expand(a*chi+(a*a-1)*psi), sp.expand(chi+a*psi)
        require(sp.expand(poly.subs(X, 1-a*a)-(-1)**j*psi) == 0, "odd-index conjugate polynomial")
        require(sp.expand(a*poly.subs(X, a*a)-chi) == 0, "odd-index chi quotient")
    samples = []
    for A, rank in [(2, 3), (3, 3), (4, 3), (5, 3), (6, 3), (2, 7)]:
        _, c = pell(A, rank)
        f, ordinate = pell(A, rank*c)
        require(ordinate % (c*c) == 0, "canonical strong multiplier")
        j = ordinate//(c*c)
        Delta = A*A-1
        S = Delta*j*c*c
        chi, y = pell(S, rank)
        require(chi % S == 0, "integral auxiliary quotient")
        V = chi//S
        numerator, denominator = V+c+rank*f*f, c*f*f
        require(numerator % denominator == 0, "squared modulus quotient")
        T = numerator//denominator
        require(S*S == Delta*(f*f-1), "ordinary strong equation")
        require(math.gcd(c, f) == 1 and f*f % c == 1, "coprimality")
        require((V+c) % (f*f) == 0 and (V+rank) % c == 0, "both quotient congruences")
        require(V == f*f*(c*T-rank)-c and T > 0, "positive reconstructed T")
        require(S*S*V*V-(S*S-1)*y*y == 1 and y-V > 0 and V > 1, "positive auxiliary gap")
        samples.append({"A": A, "rank": rank, "c": c, "f_bits": f.bit_length(), "T_bits": T.bit_length(), "positive_gap_bits": (y-V).bit_length()})
    n, x, z = sp.symbols("n x z")
    xp, zp = (2*n+1)*x-2*n*(n+1)*z, (2*n+1)*z-2*x
    require(sp.expand(xp*xp-n*(n+1)*zp*zp-(x*x-n*(n+1)*z*z)) == 0, "negative Pell descent preserves norm")
    residue_checks = 0
    for aa in range(4):
        delta = ((aa+2)**2-1) % 4
        for ff in range(4):
            A0 = delta*(ff*ff-1) % 4
            require(A0 in [0, 1], "A0 allowed residues")
            for ii in range(4):
                require((1+ii*ii-A0) % 4 != 3, "ordinary strong negative unit")
                require((ff*ff-delta*ii*ii) % 4 != 3, "normalized strong negative unit")
                for cc in range(4):
                    require((ii*ii-delta*cc*cc) % 4 != 3, "main negative unit")
                    require((ii*ii*ff*ff-(ii*ii-1)*cc*cc) % 4 != 3, "auxiliary negative unit")
                    residue_checks += 1
    counterexamples = []
    for A, rank, c, multiplier in [(2, 3, 15, 1), (3, 3, 35, 1)]:
        delta = A*A-1
        S = delta*multiplier*c*c
        nonsquare = 1+delta*multiplier*multiplier*c**4
        V = nonsquare*(c-rank)-c
        y = 4*S*S-1
        main_root, pell_c = pell(A, rank)
        require(pell_c == c and main_root*main_root-delta*c*c == 1, "counterexample main Pell norm")
        require(math.isqrt(nonsquare)**2 != nonsquare, "counterexample modulus is nonsquare")
        require(S*S*V*V-(S*S-1)*y*y == 1, "counterexample still satisfies auxiliary norm")
        counterexamples.append({"a0": A, "Delta": delta, "c": c, "i": multiplier, "S": S,
                                "nonsquare_modulus": nonsquare, "T": 1, "V": V, "y": y, "main_root": main_root})
    A = sp.Symbol("a0")
    c = 4*A*A-1
    delta = A*A-1
    S = delta*c*c
    D = 1+delta*c**4
    require(sp.expand(D*(c-3)-c-(4*S*S-3)) == 0, "general lost-square family quotient identity")
    require(sp.expand(S*S*(4*S*S-3)**2-(S*S-1)*(4*S*S-1)**2-1) == 0, "general lost-square family norm identity")
    return {"universal_local_polynomial_identities": list(identities),
            "odd_index_polynomial_checks": len(q)*3, "exact_reconstruction_examples": samples,
            "lost_strong_square_counterexamples": counterexamples,
            "general_lost_square_family_identities": True,
            "mod4_cases": residue_checks, "negative_pell_descent_identity": True}


def main():
    coefficients, payloads = bind_coefficients()
    records = []
    rng = random.Random(2361798)
    for path in sorted(BASE.rglob("p*_degree*.json")):
        obj = json.loads(path.read_text())
        counts = validate_dag(obj, path)
        macros = symbolic_macro_checks(obj)
        degrees = exact_degree_audit(obj)
        for trial in range(300):
            p = [1000000007, 1000000009, 998244353][trial % 3]
            v = {n: rng.randrange(-19, 20) for n in obj["witnesses"]}
            v.update({n: coefficients[n] % p for n in PORTS})
            require(eval_circuit(obj, v, p) == direct_formula(obj, v, p), "actual-port direct evaluation")
        replays = [affine_replay(obj, coefficients, p, seed) for p in [1000000007, 1000000009, 998244353] for seed in [902, 1902]]
        rec = {"file": str(path.relative_to(BASE)), "input_sha256": sha(path.read_bytes()),
               "operations": len(obj["source"]), "operation_counts": counts,
               "all_15_witnesses_and_4_fixed_ports_live": True, "exact_macro_identity_checks": macros,
               "degree_certificate": degrees, "actual_port_direct_checks": 300,
               "actual_port_full_affine_degree_checks": replays}
        records.append(rec)
        print(obj["name"], "PASS", len(obj["source"]), degrees["exact_degree"], flush=True)
    report = {"status": "PASS", "scope": "Independent finite and exact algebraic checks, not an unbounded compiler/kernel proof.",
              "coefficient_payloads": payloads, "circuits": records, "auxiliary_checks": auxiliary_checks()}
    (HERE/"INDEPENDENT_SHORT_RESULTS.json").write_text(json.dumps(report, indent=2)+"\n")
    print("ALL CHECKS PASS", flush=True)


if __name__ == "__main__":
    main()
