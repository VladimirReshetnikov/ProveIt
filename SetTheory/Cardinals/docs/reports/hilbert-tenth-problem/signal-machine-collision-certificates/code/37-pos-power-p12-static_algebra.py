#!/usr/bin/env python3
"""Fresh exact static algebra and declared finite fixtures, 4 October 2026.

Only this new, inspected program is executed. No old script is imported, no
subprocess or network is used, and no machine/physical dynamics is interpreted.
All generated files stay in this separate packet. Pell recurrences below are
exact arithmetic for the explicitly fixed finite fixture list, not an
all-exponent proof. Sparse polynomial operations use integer coefficients.
"""
from pathlib import Path
from fractions import Fraction
from math import factorial, comb, gcd
from hashlib import sha256
import json

ROOT = Path(__file__).resolve().parent
EVIDENCE = ROOT / "evidence"
ORIGINAL = Path("/workspace/shared/positive-power22-reduction-20261004")


class P:
    def __init__(self, value=0):
        if isinstance(value, P):
            self.t = dict(value.t)
        elif isinstance(value, int):
            self.t = {(): value} if value else {}
        else:
            self.t = {m: c for m, c in value.items() if c}

    @staticmethod
    def var(name):
        return P({((name, 1),): 1})

    def __add__(self, other):
        out = dict(self.t)
        for m, c in P(other).t.items():
            out[m] = out.get(m, 0) + c
        return P(out)

    __radd__ = __add__

    def __neg__(self):
        return P({m: -c for m, c in self.t.items()})

    def __sub__(self, other):
        return self + -P(other)

    def __rsub__(self, other):
        return P(other) + -self

    def __mul__(self, other):
        out = {}
        for m, a in self.t.items():
            for n, b in P(other).t.items():
                powers = dict(m)
                for name, power in n:
                    powers[name] = powers.get(name, 0) + power
                key = tuple(sorted(powers.items()))
                out[key] = out.get(key, 0) + a*b
        return P(out)

    __rmul__ = __mul__

    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        value = P(1)
        for _ in range(n):
            value = value*self
        return value

    def __eq__(self, other):
        return self.t == P(other).t

    def degree(self):
        return max((sum(e for _, e in m) for m in self.t), default=-1)

    def variables(self):
        return {name for m in self.t for name, _ in m}

    def coefficient(self, powers):
        return self.t.get(tuple(sorted(powers.items())), 0)

    def evaluate(self, values):
        result = 0
        for m, c in self.t.items():
            term = c
            for name, e in m:
                term *= values[name]**e
            result += term
        return result

    def serialized(self):
        return [{"powers": dict(m), "coefficient": str(c)}
                for m, c in sorted(self.t.items())]


DIRECT = ["o", "g", "q_b", "q_v", "J", "q_alpha"]
NATURAL = ["d_wb", "d_wC", "d_yC", "q_sigma", "q_tau", "q_r"]


def module(b, C, prefix=""):
    a = {name: P.var(prefix+name) for name in DIRECT}
    leaves = [prefix+name for name in DIRECT]
    for name in NATURAL:
        a[name] = P.var(prefix+name+"_plus") - 1
        leaves.append(prefix+name+"_plus")
    o, g, qb, qv, J, qa = [a[name] for name in DIRECT]
    w, y = b+a["d_wb"], C+a["d_yC"]
    beta, v, t = 1+4*y*qb, y**2*qv, C+4*y*a["q_tau"]
    M, d = b*o+J, 2*b
    A = M+b**2+1
    X = y*(A-d*b)+d*b*o+d*M*a["q_r"]
    U = d*beta-A
    S = qa*X+U*a["q_sigma"]
    residuals = [X**2-d**2-(A**2-d**2)*y**2,
                 U**2-d**2*qa**2-(A**2-d**2)*qa**2*v**2,
                 S**2-d**2*qa**2-d**2*qa**2*(beta**2-1)*t**2,
                 w-C-a["d_wC"],
                 A**2-d**2-d**2*((w+1)**2-1)*(w*g)**2]
    a.update({"w": w, "y": y, "beta": beta, "v": v, "t": t,
              "M": M, "d": d, "A": A, "X": X, "U": U, "S": S})
    assert len(leaves) == len(set(leaves)) == 12
    return residuals, leaves, a


def squares(residuals):
    return sum((r**2 for r in residuals), P(0))


def dump(name, value):
    path = EVIDENCE/name
    path.write_text(json.dumps(value, indent=2, sort_keys=True)+"\n")
    return {"file": "evidence/"+name,
            "sha256": sha256(path.read_bytes()).hexdigest(),
            "bytes": path.stat().st_size}


def receipt(residuals, leaves, inputs, monomial):
    total = squares(residuals)
    assert total.variables() == set(leaves)|set(inputs)
    assert total.coefficient(monomial) == 1
    return total, {"leaves_including_output": len(leaves),
                   "residual_slots": len(residuals),
                   "external_inputs": inputs,
                   "all_declared_variables_live": True,
                   "residual_degrees": [r.degree() for r in residuals],
                   "sum_of_squares_degree": total.degree(),
                   "sum_of_squares_terms": len(total.t),
                   "degree_certificate": monomial,
                   "certificate_coefficient": total.coefficient(monomial)}


def pell(z, n):
    x, y = 1, 0
    for _ in range(n):
        x, y = z*x+(z*z-1)*y, x+z*y
    return x, y


def finite_fixture(b, C, k):
    # The only called pairs are the five literals in main(), and k in 1,2,3,7.
    w = max(b, C)
    alpha, auxiliary_y = pell(w+1, w)
    assert auxiliary_y % w == 0
    g = auxiliary_y//w
    x, y = pell(alpha, C)
    u, v = pell(alpha, 2*C*y)
    assert gcd(u, 4*y) == 1 and v % (y*y) == 0
    qa0 = ((1-alpha)*pow(u, -1, 4*y)) % (4*y)
    beta0 = alpha+u*qa0
    beta = beta0+4*y*u*k
    s, t = pell(beta, C)
    M, o = 2*b*alpha-b*b-1, b**(C-1)
    assert (x-y*(alpha-b)-b*o) % M == 0
    assert (s-x) % u == 0 and (t-C) % (4*y) == 0
    natural = {"d_wb": w-b, "d_wC": w-C, "d_yC": y-C,
               "q_sigma": (s-x)//u, "q_tau": (t-C)//(4*y),
               "q_r": (x-y*(alpha-b)-b*o)//M}
    values = {"C": C, "o": o, "g": g, "q_b": (beta-1)//(4*y),
              "q_v": v//(y*y), "J": M-b*o, "q_alpha": qa0+4*y*k}
    values.update({name+"_plus": v+1 for name, v in natural.items()})
    assert all(n >= 0 for n in natural.values())
    assert all(n > 0 for n in values.values())
    old = dict(alpha=alpha, beta=beta, x=x, y=y, u=u, v=v, s=s, t=t,
               w=w, M=M, g=g, C=C, o=o, J=M-b*o, **natural)
    return values, old


def reconstruct(values, b, residuals, aliases):
    assert all(r.evaluate(values) == 0 for r in residuals)
    a = {name: expr.evaluate(values) for name, expr in aliases.items()}
    alpha = Fraction(a["A"], a["d"])
    u = Fraction(a["U"], a["d"]*a["q_alpha"])
    x, s = Fraction(a["X"], a["d"]), Fraction(a["S"], a["d"]*a["q_alpha"])
    assert all(n.denominator == 1 and n > 0 for n in (alpha, u, x, s))
    alpha, u, x, s = map(int, (alpha, u, x, s))
    y, beta, v, t = [a[n] for n in ("y", "beta", "v", "t")]
    w, M, g, o, C = a["w"], a["M"], a["g"], a["o"], values["C"]
    old_residuals = [x*x-1-(alpha*alpha-1)*y*y,
        u*u-1-(alpha*alpha-1)*v*v, s*s-1-(beta*beta-1)*t*t,
        beta-1-4*y*a["q_b"], beta-alpha-u*a["q_alpha"],
        v-y*y*a["q_v"], s-x-u*a["q_sigma"], t-C-4*y*a["q_tau"],
        y-C-a["d_yC"], w-b-a["d_wb"], w-C-a["d_wC"], M-b*o-a["J"],
        alpha*alpha-1-((w+1)**2-1)*(w*g)**2,
        2*alpha*b-M-(b*b+1), x-y*(alpha-b)-b*o-M*a["q_r"]]
    assert old_residuals == [0]*15 and alpha > w >= b
    assert beta > alpha and u >= alpha and u >= x
    return {"alpha": alpha, "u": u, "x": x, "s": s}


def compressed(L, R, T, accepted):
    K, N = T+1, (T+1)**2
    delta, j, r, s = factorial(N-1), P.var("j"), P.var("r"), P.var("s")
    V1, V2, range_poly = P(0), P(0), P(1)
    for i in range(1, N+1):
        basis = P((-1)**(N-i)*comb(N-1, i-1))
        for h in range(1, N+1):
            if h != i:
                basis *= j-h
        V1 += (1+(i-1)//K)*basis
        V2 += (1+(i-1)%K)*basis
        range_poly *= j-i
    accept_poly = P(1)
    for i in sorted(accepted):
        assert 1 <= i <= N
        accept_poly *= j-i
    residuals = [range_poly, (delta*L-V1)*(V1-delta*K),
                 delta*L-V1-delta*(r-1), (delta*R-V2)*(V2-delta*K),
                 delta*R-V2-delta*(s-1), accept_poly]
    return residuals


def main():
    EVIDENCE.mkdir(exist_ok=True)
    result = {"scope": "fresh exact static algebra and finite declared fixtures only",
              "checker_sha256": sha256(Path(__file__).read_bytes()).hexdigest()}
    C = P.var("C")
    mon_fixed = {"J": 4, "q_alpha": 4, "d_yC_plus": 8, "q_v": 4}
    variants, artifacts = {}, []
    for label, base in [("fixed_base_two", P(2)), ("variable_base_B_plus_one", P.var("B")+1)]:
        residuals, leaves, aliases = module(base, C)
        variable = label.startswith("variable")
        mon = dict(mon_fixed) if not variable else {"B": 8, "q_alpha": 4, "d_yC_plus": 8, "q_v": 4}
        total, info = receipt(residuals, leaves, ["B", "C"] if variable else ["C"], mon)
        assert info["residual_degrees"] == ([8,12,12,1,8] if variable else [4,10,10,1,6])
        assert total.degree() == (24 if variable else 20)
        variants[label] = info
        artifacts.append(dump(label+".polynomial.json", {"receipt": info,
            "residuals": [p.serialized() for p in residuals], "polynomial": total.serialized()}))
    for b in (3,4,5):
        residuals, leaves, _ = module(P(b), C)
        total, info = receipt(residuals, leaves, ["C"], mon_fixed)
        assert info["residual_degrees"] == [4,10,10,1,6] and total.degree() == 20
        variants["fixed_base_"+str(b)] = info
    result["module_expansions"] = variants

    # Generic exact identities (17), without assuming any residual vanishes.
    H, _, a = module(P.var("b"), C)
    u = P.var("u")
    A,d,X,U,y,v,t,beta,qa,qs = [a[n] for n in ("A","d","X","U","y","v","t","beta","q_alpha","q_sigma")]
    F = [X**2-d**2-(A**2-d**2)*y**2,
         d**2*u**2-d**2-(A**2-d**2)*v**2,
         (X+d*u*qs)**2-d**2-d**2*(beta**2-1)*t**2,
         U-d*u*qa, H[3], H[4]]
    assert H[0] == F[0] and H[3] == F[4] and H[4] == F[5]
    assert H[1]-qa**2*F[1] == F[3]*(U+d*u*qa)
    assert H[2]-qa**2*F[2] == F[3]*qs*(2*qa*X+(U+d*u*qa)*qs)
    result["generic_elimination_identities"] = 5

    fixtures = []
    for b,C0 in [(2,1),(3,1),(4,1),(5,1),(2,2)]:
        H, leaves, aliases = module(P(b), C)
        for k in (1,2,3,7):
            values, old = finite_fixture(b,C0,k)
            restored = reconstruct(values,b,H,aliases)
            assert all(restored[n] == old[n] for n in restored)
            variable_values = dict(values, B=b-1)
            HV,_,_ = module(P.var("B")+1,C)
            assert all(p.evaluate(variable_values) == 0 for p in HV)
            fixtures.append({"b":b,"C":C0,"k":k,"positive_leaves":values,
                             "restored": restored})
    result["complete_fixture_assignments"] = len(fixtures)
    result["fixture_evaluations_fixed_and_variable"] = 2*len(fixtures)
    artifacts.append(dump("full_fixtures.json",fixtures))

    # Symbolically check the entire exponent-zero family, not merely samples.
    k=P.var("k")
    family={"C":P(1),"o":P(1),"g":P(3),"J":P(61),"q_v":P(34),
            "q_b":4+577*k,"q_alpha":4*k,"d_wb_plus":P(1),"d_wC_plus":P(2),
            "d_yC_plus":P(1),"q_sigma_plus":4*k+1,"q_tau_plus":P(1),"q_r_plus":P(1)}
    HF,_,_=module(P(2),C)
    assert all(r.evaluate(family) == P(0) for r in HF)
    result["symbolic_exponent_zero_family_identities"] = 5
    result["family_domain"] = "k>=1; k=0 is a polynomial zero outside the new positive q_alpha domain"

    # Complete literal compositions. Acceptance sets are declarations, never
    # obtained by running a counter program. Six residual slots are retained.
    g1,g2,g3,L,R = [P.var(n) for n in ("g1","g2","g3","L","R")]
    D=g1+g2+g3
    HA,la,aa=module(P(2),L,"left_")
    HB,lb,ab=module(P(2),R,"right_")
    gaps=[(20*g1-D)*aa["o"]-2*D,(20*g3-D)*ab["o"]-2*D]
    witnesses=["L","R"]+la+lb+["j","r","s"]
    assert len(witnesses) == len(set(witnesses)) == 29
    compositions=[]
    for T,accepted in [(0,set()),(0,{1}),(1,set()),(1,{1,2,3,4}),
                       (3,set(range(1,13))),(3,{9,10,11,12})]:
        compiler=compressed(L,R,T,accepted)
        residuals=gaps+HA+HB+compiler
        assert len(residuals)==18
        total=squares(residuals)
        compiler_total=squares(compiler)
        assert total.variables()==set(witnesses)|{"g1","g2","g3"}
        certificate={"left_"+n:e for n,e in mon_fixed.items()}
        assert total.coefficient(certificate)==1
        assert total.degree()==max(20,compiler_total.degree())
        assert compiler_total.degree() <= (2 if T==0 else 4*(T+1)**2-4)
        vals, _=finite_fixture(2,1,1)
        complete={"g1":3,"g2":14,"g3":3,"L":1,"R":1,"j":1,"r":1,"s":1}
        complete.update({"left_"+n:val for n,val in vals.items() if n!="C"})
        complete.update({"right_"+n:val for n,val in vals.items() if n!="C"})
        assert (total.evaluate(complete)==0)==(1 in accepted)
        compositions.append({"T":T,"accepted_classes":sorted(accepted),
            "witnesses":29,"external_inputs":3,"all_variables":32,"residual_slots":18,
            "compiler_degree":compiler_total.degree(),"composed_degree":total.degree(),
            "expanded_terms":len(total.t),"full_exponent_zero_fixture_accepted":1 in accepted})
    result["literal_composition_expansions"]=compositions

    # Verify frozen dependencies against independently recorded byte pins.
    pins={
      "LICENSE.mathlib-Apache-2.0.txt":"cfc7749b96f63bd31c3c42b5c471bf756814053e847c10f3eb003417bc523d30",
      "NOTICE.md":"45800127cf9faad081c34d4ecf8d5689eba081b9483c842ee44138cf5468242b",
      "POWER58_PROOF.md":"b55f301d2b1531f348163f026b3c1f7f827669d266afb77d854eef7ceb21c482",
      "POWER60_PROOF.md":"e93fdbefc3ba72e34c44e4f9d8a9b97e72027f72dc3ce53d54570113b7db5e5a",
      "compressed_PROOF.md":"233b0f67ce13e81a41132017214db5b34d10c965cd9a3ef56d1cbc9d280ac33c",
      "elimination_PROOF.md":"b0c4025fbed63ee4ff036a29df3bef67e132f1fe8f0370db2f9e4ff06b9f9db1",
      "native_gap_PROOF.md":"8cc5911e528d0555ee89fe63f0e30b8a3eac4a32e3e4237ee9b00a38107a7d1b",
      "pell-source.lean":"993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a",
      "positive22_PROOF.md":"861905b08f6e2d04143c4a4e0075ba8f50548ddca2d8c8f0f46e458052825281"}
    sources=[]
    for name,expected in sorted(pins.items()):
        path=ROOT/"dependencies"/name
        data=path.read_bytes()
        assert sha256(data).hexdigest()==expected
        origin=(ORIGINAL/"PROOF.md" if name=="positive22_PROOF.md" else
                ORIGINAL/"ELIMINATION_VARIANTS.md" if name=="elimination_PROOF.md" else
                ORIGINAL/"dependencies"/name)
        assert origin.read_bytes()==data
        sources.append({"file":"dependencies/"+name,"origin":str(origin),
                        "sha256":expected,"bytes":len(data),"executed":False})
    (ROOT/"SOURCE_PINS.json").write_text(json.dumps(sources,indent=2)+"\n")
    snapshot="".join(sha256(path.read_bytes()).hexdigest()+"  ./"+
             path.relative_to(ORIGINAL).as_posix()+"\n"
             for path in sorted(ORIGINAL.rglob("*")) if path.is_file())
    before=(EVIDENCE/"frozen_original.before.sha256").read_text()
    assert snapshot==before
    (EVIDENCE/"frozen_original.after.sha256").write_text(snapshot)
    result["frozen_original_unchanged"]=True
    result["frozen_original_inventory_sha256"]=sha256(before.encode()).hexdigest()
    result["artifacts"]=artifacts
    dump("results.json",result)
    print(json.dumps({"success":True,"module_expansions":len(variants),
      "fixtures":len(fixtures),"compositions":len(compositions),
      "fixed_degree":20,"variable_degree":24,"original_unchanged":True},sort_keys=True))


if __name__=="__main__":
    main()
