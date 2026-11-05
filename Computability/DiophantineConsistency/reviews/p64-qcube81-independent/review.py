#!/usr/bin/env python3
"""Independent structural and small-polynomial review; no Lean invocation."""
import collections
import hashlib
import json
import pathlib
import subprocess

HERE = pathlib.Path(__file__).resolve().parent
ROOT = pathlib.Path(subprocess.check_output(["git", "-C", str(HERE), "rev-parse", "--show-toplevel"], text=True).strip())
PACK = ROOT / "Computability/DiophantineConsistency/research/p64-qcube81-candidate"
PARENT = ROOT / "Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/positive14/polynomial.json"
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
g, p, checks = (json.loads(x.read_text()) for x in (PACK / "graph.json", PARENT, PACK / "checks.json"))
assert sha(PARENT) == "b9731360a30bcbcfd6f9161241cafb01b8c5d68aa40b84ddc50ba689a0745d0e"
assert sha(PACK / "graph.json") == "41c8602480cee0e9a21d3a4cd2a7719fa395bd6aabba821aeb7a9f5c776a3db3"
assert checks["builder_sha256"] == sha(PACK / "build.py")
assert g["witnesses"][:7] == p["witnesses"][:7] and g["witnesses"][7] == "s"
assert g["witnesses"][8:] == p["witnesses"][8:] and p["witnesses"][7] == "Y"
assert g["fixed_numerals"] == p["fixed_numerals"] and g["output"] == p["output"]
old = {r[0]: r for r in p["source"]}
new = {r[0]: r for r in g["source"]}
removed = {"ell_plus_rho", "scaled_gap", "first_carrier", "first_carrier_square", "q6", "scaled_first_radicand", "A0"}
added = {"Y", "ell_plus_rho", "first_unscaled", "first_unscaled_square", "A0"}
assert [r for r in p["source"] if r[0] not in removed] == [r for r in g["source"] if r[0] not in added]
assert [old[n] for n in ("ell_plus_rho", "scaled_gap", "first_carrier", "first_carrier_square", "q6", "scaled_first_radicand", "A0")] == [
    ["ell_plus_rho", "+", "ell", "rho"], ["scaled_gap", "*", "q3", "ell_plus_rho"],
    ["first_carrier", "+", "scaled_gap", "Y"], ["first_carrier_square", "*", "first_carrier", "first_carrier"],
    ["q6", "*", "q3", "q3"], ["scaled_first_radicand", "*", "q6", "first_radicand"],
    ["A0", "-", "first_carrier_square", "scaled_first_radicand"]]
assert [new[n] for n in ("Y", "ell_plus_rho", "first_unscaled", "first_unscaled_square", "A0")] == [
    ["Y", "*", "q3", "s"], ["ell_plus_rho", "+", "ell", "rho"],
    ["first_unscaled", "+", "ell_plus_rho", "s"],
    ["first_unscaled_square", "*", "first_unscaled", "first_unscaled"],
    ["A0", "-", "first_unscaled_square", "first_radicand"]]
known = set(g["witnesses"]+g["fixed_numerals"]) | set(range(5))
deps = {}
for name, op, x, y in g["source"]:
    assert name not in known and op in "+-*" and x in known and y in known
    known.add(name)
    deps[name] = (x, y)
seen, todo = set(), [g["output"]]
while todo:
    n = todo.pop()
    if n not in deps or n in seen:
        continue
    seen.add(n)
    todo.extend(deps[n])
assert len(g["source"]) == len(seen) == 81
assert dict(collections.Counter(r[1] for r in g["source"])) == {"*": 42, "+": 23, "-": 16}
lean_text = (PACK / "P64QCube81.lean").read_text()
assert lean_text.startswith("import DiophantineConsistency.Compact44.P64Graph\n")
begin, end = "  -- BEGIN GENERATED GRAPH\n", "  -- END GENERATED GRAPH"
lean_rows = lean_text.split(begin, 1)[1].split(end, 1)[0].splitlines()
assert lean_rows == [f"  let {name} := {x} {op} {y}" for name, op, x, y in g["source"]]
for i, name in enumerate(g["witnesses"]):
    assert f"  let {name} : Expr (Fin 14) := .var {i}\n" in lean_text
for i, name in enumerate(g["fixed_numerals"]):
    assert f"  let {name} : Expr (Fin 14) := .constant (p {i})\n" in lean_text
assert "  ⟨A0, M, W, Na, Lt, polynomial⟩\n" in lean_text

# A small independently implemented exact polynomial ring for algebraic checks.
class P:
    def __init__(self, terms=None): self.t = {k:v for k,v in (terms or {}).items() if v}
    @staticmethod
    def var(name): return P({((name, 1),): 1})
    @staticmethod
    def coerce(x): return x if isinstance(x, P) else P({():x})
    def __add__(self, other):
        out = dict(self.t)
        for k,v in P.coerce(other).t.items(): out[k] = out.get(k,0)+v
        return P(out)
    __radd__ = __add__
    def __neg__(self): return P({k:-v for k,v in self.t.items()})
    def __sub__(self, other): return self+-P.coerce(other)
    def __rsub__(self, other): return P.coerce(other)+-self
    def __mul__(self, other):
        out = collections.defaultdict(int)
        for a,x in self.t.items():
            for b,y in P.coerce(other).t.items():
                powers = collections.Counter(dict(a)); powers.update(dict(b))
                out[tuple(sorted(powers.items()))] += x*y
        return P(out)
    __rmul__ = __mul__
    def __pow__(self, n):
        out = P.coerce(1)
        for _ in range(n): out = out*self
        return out
    def __eq__(self, other): return self.t == P.coerce(other).t

q,l,r,s,k = (P.var(x) for x in ("q", "ell", "rho", "s", "k"))
first_old = (q**3*(l+r)+q**3*s)**2-q**6*(l*(l+k)+1)
first_new = (l+r+s)**2-(l*(l+k)+1)
assert first_old == q**6*first_new
assert first_new == l*(2*(r+s)-k)+(r+s)**2-1
U,X,a,c,H,gamma,R = (P.var(x) for x in ("U", "X", "a", "c", "H", "gamma", "R"))
main = (U*(X+a*c)+H*(U*gamma-R))**2-U**2*((a*a+H)*c*c+1)
expanded = U**2*(2*a*c*(X+H*gamma)+(X+H*gamma)**2-H*c*c-1)-2*U*H*R*(X+a*c+H*gamma)+H**2*R**2
assert main == expanded
A,V,e = (P.var(x) for x in ("A", "V", "e"))
assert A*(V**2-(V+e)**2)+(V+e)**2 == V**2-(A-1)*e*(2*V+e)
beta,J,w,s,eta,zeta,gamma = (P.var(x) for x in ("beta","J","w","s","eta","zeta","gamma"))
Ytop = beta**3*J**3*s
atop = beta**4*J**4*w*s
ctop = beta**3*J**3*s*(eta+zeta)
main_top = 2*Ytop**4*atop*ctop*(4*atop)*gamma
expected = 64*beta**46*J**46*w**4*s**14*(eta+zeta)**2*gamma**2
assert main_top**2 == expected
assert max(sum(e for v,e in m if v != "beta") for m in expected.t) == 68
assert checks["degree"] == 68 and checks["leading_form_condition"] == "beta != 0"
print(json.dumps({"status":"INDEPENDENT_STRUCTURAL_AND_POLYNOMIAL_CHECKS_PASS",
    "graph_sha256":sha(PACK/"graph.json"), "parent_sha256":sha(PARENT), "builder_sha256":sha(PACK/"build.py"),
    "checks_sha256":sha(PACK/"checks.json"), "generator_sha256":sha(PACK/"generate_lean.py"),
    "lean_source_sha256":sha(PACK/"P64QCube81.lean"), "gates":len(seen), "exact_first_factor_identity":True,
    "expanded_main_identity":True, "expanded_auxiliary_identity":True,
    "lean_graph_transcription":True, "leading_degree":68,
    "scope":"Source graph and exact small-polynomial algebra; no Lean or zero-set equivalence."}, indent=2, sort_keys=True))
