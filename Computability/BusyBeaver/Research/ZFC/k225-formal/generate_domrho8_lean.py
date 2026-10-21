#!/usr/bin/env python3
"""Generate DomRho8.lean: dominated rho8 instances derive every rho8 instance.

  python generate_domrho8_lean.py CERTIFICATE_JSON OUT_LEAN

The certificate is Source 149's `theory/dominated_rho8_full_certificate.json` (term_dag_v1:
a shared term table over implication, truth and variables, and 3,728 proof nodes whose rules
are a dominated rho8 leaf, the truth leaf, modus ponens, a substitution instance, or modus
ponens of two substitution instances). Exact earlier-schema instances are reused and unused dependencies are pruned. The optimizer
and certificate are untrusted: every retained term becomes a definition
`tK : (Nat → Nat) → Nat` (a code under a valuation of the variables) and every node a theorem
`nK : ∀ v, T (tK v)` about an arbitrary predicate `T` closed under the three rules
(`DomImp`). Lean checks each step by definitional unfolding; a dominated leaf carries the
proof `u ≤ a` that its fourth argument is a literal subterm of its first (or truth), using
only that implication codes dominate both inputs.
"""
import json
import sys

src, out = sys.argv[1], sys.argv[2]
d = json.load(open(src))
assert d["format"] == "term_dag_v1"
T, N = d["term_table"], d["nodes"]


def reduce_certificate(terms, nodes):
    """Reuse exact instances of earlier schemas, then retain the root's dependencies.

    This is only proof production: the resulting substitutions, dominated leaves and
    modus-ponens steps are all emitted below as ordinary Lean proofs.
    """
    sizes = []
    for term in terms:
        sizes.append(1 + sum(sizes[c] for c in term) if isinstance(term, list) else 1)

    def match(pattern, target, env, seen):
        if (pattern, target) in seen:
            return True
        seen.add((pattern, target))
        p, t = terms[pattern], terms[target]
        if isinstance(p, dict):
            return env.setdefault(p["var"], target) == target
        if p == "T":
            return t == "T"
        return (isinstance(t, list) and match(p[0], t[0], env, seen)
                and match(p[1], t[1], env, seen))

    schemas, rules = [], []
    for i, node in enumerate(nodes):
        for parent in schemas:
            if sizes[nodes[parent]["term"]] > sizes[node["term"]]:
                continue
            env = {}
            if match(nodes[parent]["term"], node["term"], env, set()):
                rules.append({"kind": "substitution", "parent": parent, "substitution": env})
                break
        else:
            schemas.append(i)
            rules.append(node["rule"])

    used_nodes, used_terms = set(), set()

    def visit_node(i):
        if i in used_nodes:
            return
        used_nodes.add(i)
        for field in ("major", "minor", "parent"):
            if field in rules[i]:
                parent = rules[i][field]
                assert parent < i
                visit_node(parent)

    def visit_term(i):
        if i in used_terms:
            return
        used_terms.add(i)
        if isinstance(terms[i], list):
            for child in terms[i]:
                assert child < i
                visit_term(child)

    visit_node(len(nodes) - 1)
    for i in used_nodes:
        visit_term(nodes[i]["term"])
        for field in ("substitution", "major_substitution", "minor_substitution"):
            for term in rules[i].get(field, {}).values():
                visit_term(term)
    # Conversion proofs also use zero and the certificate's named variables.
    for i, term in enumerate(terms):
        if term == "T" or isinstance(term, dict):
            visit_term(i)

    node_ids = {old: new for new, old in enumerate(sorted(used_nodes))}
    term_ids = {old: new for new, old in enumerate(sorted(used_terms))}
    reduced_terms = [[term_ids[c] for c in terms[i]] if isinstance(terms[i], list)
                     else terms[i] for i in sorted(used_terms)]
    reduced_nodes = []
    for i in sorted(used_nodes):
        rule = dict(rules[i])
        for field in ("major", "minor", "parent"):
            if field in rule:
                rule[field] = node_ids[rule[field]]
        for field in ("substitution", "major_substitution", "minor_substitution"):
            if field in rule:
                rule[field] = {v: term_ids[t] for v, t in rule[field].items()}
        reduced_nodes.append({"id": node_ids[i], "term": term_ids[nodes[i]["term"]], "rule": rule})
    return reduced_terms, reduced_nodes


original_terms, original_nodes = len(T), len(N)
T, N = reduce_certificate(T, N)


def kind(i):
    t = T[i]
    if t == "T":
        return "T"
    if isinstance(t, dict):
        return "v"
    assert isinstance(t, list) and len(t) == 2 and all(0 <= x < i for x in t), i
    return "I"


def parts(i):
    assert kind(i) == "I", i
    return T[i]


def rho8_args(i):
    """the term ((C → U) → A) → ((A → C) → (B → C)) as (A, B, C, U)"""
    l, r = parts(i)
    cu, a = parts(l)
    c, u = parts(cu)
    ac, bc = parts(r)
    a2, c2 = parts(ac)
    b, c3 = parts(bc)
    assert a2 == a and c2 == c and c3 == c, i
    return a, b, c, u


def path(a, u):
    """a proof of `tU v ≤ tA v` from u being a literal subterm of a (or truth)"""
    if kind(u) == "T":
        return "Nat.zero_le _"
    best = {}

    def go(x):
        if x == u:
            return "Nat.le_refl _"
        if x in best:
            return best[x]
        res = None
        if kind(x) == "I":
            l, r = parts(x)
            pl = go(l)
            if pl is not None:
                res = f"le_l (t{r} v) ({pl})"
            else:
                pr = go(r)
                if pr is not None:
                    res = f"le_r (t{l} v) ({pr})"
        best[x] = res
        return res

    p = go(a)
    assert p is not None, ("not dominated", a, u)
    return p


def subst(env, val="v"):
    m = {int(k): v for k, v in env.items()}
    n = max(m) + 1 if m else 0
    return "(sub [" + ", ".join(f"t{m[i]} {val}" if i in m else "0" for i in range(n)) + "])"


L = []
w = L.append
w("""import BusyBeaver.ZFC.Code254

/-!
Dominated rho8 instances derive every rho8 instance.

For a predicate `T` on codes that holds of truth (code 0), is closed under modus ponens, and
contains every instance `rho8 a b c u = ((c → u) → a) → ((a → c) → (b → c))` whose fourth
argument is numerically at most its first (`DomImp`), `rho8_all` derives every instance.
Codes need not decode: the argument uses only that an implication code dominates both inputs.

The derivation reduces Source 149's certificate by exact substitution into earlier theorem
schemas, then prunes unused dependencies. Every retained step and substitution is checked by
Lean; the optimizer is not trusted. See the generator for the finite input and reduction.
Generated by `Computability/BusyBeaver/Research/ZFC/k225-formal/generate_domrho8_lean.py`:
the term `tK` is a code under a valuation `v` of the certificate's nine variables, and node
`nK` derives it for every valuation; substitution instances re-instantiate the valuation.
-/

namespace SetTheory.BusyBeaver.ZFC.DomRho8

open Code254

/-- Truth, modus ponens and the dominated rho8 instances. -/
structure DomImp (T : Nat → Prop) : Prop where
  truth : T 0
  mp : ∀ {a b : Nat}, T (wim a b) → T a → T b
  rho8 : ∀ a b c u : Nat, u ≤ a → T (Code254.rho8 a b c u)

theorem le_l {u x : Nat} (y : Nat) (h : u ≤ x) : u ≤ wim x y :=
  Nat.le_trans h (by have := le_P_left x y; simp only [wim]; omega)

theorem le_r {u y : Nat} (x : Nat) (h : u ≤ y) : u ≤ wim x y :=
  Nat.le_trans h (by have := le_P_right x y; simp only [wim]; omega)

/-- A substitution: the valuation sending variable `i` to the `i`-th code. -/
def sub (l : List Nat) (i : Nat) : Nat := l.getD i 0

/-! ## Terms -/
""")
# An extended, hash-consed term table: the certificate's terms keep their ids; substitution
# instances computed without the truth collapse I(T, T) = T are appended. Where a step needs
# the collapse, an explicit conversion lemma (congruence and `wim 0 0 = 0`) bridges the two.
X, IX = [], {}


def put(key):
    if key not in IX:
        IX[key] = len(X)
        X.append(key)
    return IX[key]


for i in range(len(T)):
    k = kind(i)
    key = ("T",) if k == "T" else ("v", T[i]["var"]) if k == "v" else ("I", T[i][0], T[i][1])
    assert put(key) == i, ("certificate table is not hash-consed", i)
TT = IX[("T",)]
NORM = {}


def norm(x):
    if x not in NORM:
        k = X[x]
        if k[0] != "I":
            NORM[x] = x
        else:
            a, b = norm(k[1]), norm(k[2])
            NORM[x] = TT if a == TT and b == TT else put(("I", a, b))
    return NORM[x]


def subst_naive(x, env, memo):
    if x not in memo:
        k = X[x]
        if k[0] == "v":
            memo[x] = env[k[1]]
        elif k[0] == "I":
            memo[x] = put(("I", subst_naive(k[1], env, memo), subst_naive(k[2], env, memo)))
        else:
            memo[x] = x
    return memo[x]


CONV, CL = {}, []


def conv(x, y):
    """name of a lemma `t x v = t y v`, or None when x = y"""
    if x == y:
        return None
    if (x, y) not in CONV:
        assert norm(x) == norm(y), (x, y)
        kx, ky = X[x], X[y]
        arg = lambda c, s: f"({c} v)" if c else f"(rfl : t{s} v = t{s} v)"
        if kx[0] != "I":
            back = conv(y, x)
            name = f"c{x}_{y}"
            CL.append(f"theorem {name} (v : Nat → Nat) : t{x} v = t{y} v := ({back} v).symm")
            CONV[(x, y)] = name
            return name
        if ky[0] == "I":
            ca, cb = conv(kx[1], ky[1]), conv(kx[2], ky[2])
            pf = f"wim_congr {arg(ca, kx[1])} {arg(cb, kx[2])}"
        else:
            assert ky == ("T",)
            ca, cb = conv(kx[1], TT), conv(kx[2], TT)
            pf = f"(wim_congr {arg(ca, kx[1])} {arg(cb, kx[2])}).trans wim00"
        name = f"c{x}_{y}"
        CL.append(f"theorem {name} (v : Nat → Nat) : t{x} v = t{y} v := {pf}")
        CONV[(x, y)] = name
    return CONV[(x, y)]


def env_of(e):
    return {int(k): v for k, v in e.items()}


def cast(c, pf, val="v"):
    return f"cast_T ({c} {val}) ({pf})" if c else pf


def renaming(x, y, rho, seen):
    """variables of the normalized term x renamed onto those of y (same shape)"""
    if (x, y) in seen:
        return
    seen.add((x, y))
    kx, ky = X[x], X[y]
    if kx[0] == "v":
        assert ky[0] == "v" and rho.setdefault(kx[1], ky[1]) == ky[1], (x, y)
    elif kx[0] == "T":
        assert ky == ("T",), (x, y)
    else:
        assert ky[0] == "I", (x, y)
        renaming(kx[1], ky[1], rho, seen)
        renaming(kx[2], ky[2], rho, seen)


NL = []
for k, node in enumerate(N):
    assert node["id"] == k
    r = node["rule"]
    t = node["term"]
    kd = r["kind"]
    if kd == "truth":
        assert kind(t) == "T"
        pf = "h.truth"
    elif kd == "dominated_rho8":
        a, b, c, u = rho8_args(t)
        pf = f"h.rho8 (t{a} v) (t{b} v) (t{c} v) (t{u} v) ({path(a, u)})"
    elif kd == "mp":
        maj, mn = r["major"], r["minor"]
        assert maj < k and mn < k and X[N[maj]["term"]] == ("I", N[mn]["term"], t)
        pf = f"h.mp (n{maj} h v) (n{mn} h v)"
    elif kd == "substitution":
        p = r["parent"]
        assert p < k
        xn = subst_naive(N[p]["term"], env_of(r["substitution"]), {})
        pf = cast(conv(xn, t), f"n{p} h {subst(r['substitution'])}")
    elif kd == "mp_substitution":
        maj, mn = r["major"], r["minor"]
        assert maj < k and mn < k
        mj = subst_naive(N[maj]["term"], env_of(r["major_substitution"]), {})
        mi = subst_naive(N[mn]["term"], env_of(r["minor_substitution"]), {})
        assert X[mj][0] == "I"
        _, a, b = X[mj]
        # the conclusion is the consequent up to a renaming of variables: run the step at the
        # valuation w = v after the renaming
        rho = {}
        renaming(norm(b), t, rho, set())
        assert len(set(rho.values())) == len(rho)
        b2 = subst_naive(b, {x: IX[("v", y)] for x, y in rho.items()}, {})
        nv = max(rho) + 1 if rho else 0
        wv = "sub [" + ", ".join(f"v {rho[x]}" if x in rho else "0" for x in range(nv)) + "]"
        pmin = cast(conv(mi, a), f"n{mn} h {subst(r['minor_substitution'], 'w')}", "w")
        core = (f"h.mp (a := t{a} w) (b := t{b} w) (n{maj} h "
                f"{subst(r['major_substitution'], 'w')}) ({pmin})")
        pf = cast(conv(b2, t), f"show T (t{b2} v) from let w := {wv}; {core}")
    else:
        raise ValueError(kd)
    NL.append(f"theorem n{k} (v : Nat → Nat) : T (t{t} v) := {pf}")

for i, key in enumerate(X):
    body = "0" if key[0] == "T" else f"v {key[1]}" if key[0] == "v" else f"wim (t{key[1]} v) (t{key[2]} v)"
    binder = "_v" if key[0] == "T" else "v"
    w(f"def t{i} ({binder} : Nat → Nat) : Nat := {body}")
w("")
w("theorem wim00 : wim 0 0 = 0 := by simp [wim, P, Cantor.toNat, Cantor.tri]")
w("")
w("attribute [local irreducible] wim")
w("")
w("theorem wim_congr {a b c d : Nat} (h : a = b) (k : c = d) : wim a c = wim b d := by")
w("  cases h")
w("  cases k")
w("  rfl")
w("")
w("theorem cast_T {T : Nat → Prop} {x y : Nat} (e : x = y) (h : T x) : T y := e ▸ h")
w("")
w("/-! ## Conversions where a step uses `wim 0 0 = 0` -/")
w("")
L.extend(CL)
w("")
w("/-! ## Proof nodes -/")
w("")
w("section")
w("variable {T : Nat → Prop} (h : DomImp T)")
w("include h")
w("")
L.extend(NL)
w("")
root = N[-1]["term"]
a, b, c, u = rho8_args(root)
assert all(kind(x) == "v" for x in (a, b, c, u)), "root is not rho8 on four variables"
va, vb, vc, vu = (T[x]["var"] for x in (a, b, c, u))
assert len({va, vb, vc, vu}) == 4
n = max(va, vb, vc, vu) + 1
slots = ["0"] * n
for var, name in ((va, "a"), (vb, "b"), (vc, "c"), (vu, "u")):
    slots[var] = name
w(f"""/-- **Every rho8 instance**, from the dominated ones. -/
theorem rho8_all (a b c u : Nat) : T (Code254.rho8 a b c u) :=
  n{len(N) - 1} h (sub [{", ".join(slots)}])

end

#print axioms rho8_all

end SetTheory.BusyBeaver.ZFC.DomRho8
""")
open(out, "w", encoding="utf-8", newline="\n").write("\n".join(L))
print("reduced", original_nodes, "proof nodes to", len(N), "and", original_terms, "terms to", len(T))
print("wrote", out, len(T), "certificate terms,", len(X) - len(T), "uncollapsed,",
      len(CL), "conversions,", len(N), "nodes")
