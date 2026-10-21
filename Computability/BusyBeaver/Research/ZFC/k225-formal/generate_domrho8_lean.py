#!/usr/bin/env python3
"""Generate DomRho8.lean: dominated rho8 instances derive every rho8 instance.

Superseded for the maintained Lean proof: DomRho8.lean is now a compatibility adapter over the
generic DominatedImplication.lean, produced by
verification/k215/simplification/proposals/proof-core/generation/generation/regenerate.py.
This script still renders the earlier single-module proof from the same certificate.

  python generate_domrho8_lean.py CERTIFICATE_JSON OUT_LEAN [--plan PLAN | --no-plan | --templates CD230_V]

The exact Source149 input uses a guarded lemma hierarchy by default. Its pinned CD230
templates are found in the repository or supplied with --templates. An explicit --plan
retains original-node replay; --no-plan and other inputs retain the generic direct route.

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
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path

GUARDED_HEAD = """import BusyBeaver.ZFC.Code254

/-!
Dominated rho8 derives unrestricted rho8, for arbitrary natural codes.

The proof has three layers. A 61-lemma bootstrap from Source 149 gives identity,
weakening, Peirce and the implication-transport lemma. The original CD230 lemma
hierarchy then derives composition and distribution. We retain 81 of its 107
schemas; eight carry one explicit numerical dominance hypothesis. Keeping these
hypotheses avoids expanding each schema at every substitution instance.
Finally a small deduction theorem and Peirce's law give the unrestricted row.

The bootstrap is Source 149's original nodes0..60; the CD230 templates are its
pinned adaptation of the upstream condensed-detachment derivation. Every emitted
step is an ordinary Lean proof. The source producer is untrusted. The only code
normalization is the proved identity `wim 0 0 = 0`; numerical injectivity,
formula decoding and ZFC consistency are not assumptions.
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

theorem wim00 : wim 0 0 = 0 := by simp [wim, P, Cantor.toNat, Cantor.tri]
attribute [local irreducible] wim

section
variable {T : Nat → Prop} (h : DomImp T)
include h

"""

GUARDED_MIDDLE = """
end

section
variable {T : Nat → Prop} (h : DomImp T)
include h
private theorem basisI (a : Nat) : T (wim a a) := b17 h a
private theorem basisK (a b : Nat) : T (wim a (wim b a)) := b60 h a b
private theorem basisP (a b : Nat) : T (wim (wim (wim a b) a) a) := b25 h a b
private theorem basisJ (a b c : Nat) : T (wim (wim a b) (wim (wim (wim a c) a) b)) := b57 h a b c

"""

GUARDED_TAIL = """theorem composition (a b c : Nat) : T (wim (wim a b) (wim (wim b c) (wim a c))) := cd91 h a b c
theorem distribution (a b c : Nat) : T (wim (wim a (wim b c)) (wim (wim a b) (wim a c))) := cd106 h a b c
/-! Deduction is used only after deriving K and S from the dominated rows. -/
private inductive Proof (T : Nat → Prop) : List Nat → Nat → Prop
  | ax {G a} : T a → Proof T G a
  | hyp {G a} : a ∈ G → Proof T G a
  | mp {G a b} : Proof T G (wim a b) → Proof T G a → Proof T G b

private theorem proof_sound {G : List Nat} {a : Nat} (d : Proof T G a)
    (hG : ∀ x, x ∈ G → T x) : T a := by
  induction d with
  | ax ht => exact ht
  | hyp hm => exact hG _ hm
  | mp _ _ ih1 ih2 => exact h.mp ih1 ih2

private theorem discharge_aux {a : Nat} {G' : List Nat} {b : Nat}
    (d : Proof T G' b) : ∀ G : List Nat, G' = a :: G → Proof T G (wim a b) := by
  induction d with
  | ax hb => intro G _; exact .mp (.ax (basisK h _ a)) (.ax hb)
  | hyp hm =>
      intro G hG
      subst hG
      cases List.mem_cons.mp hm with
      | inl he => subst he; exact .ax (basisI h _)
      | inr hin => exact .mp (.ax (basisK h _ a)) (.hyp hin)
  | mp _ _ ih1 ih2 =>
      intro G hG
      exact .mp (.mp (.ax (distribution h _ _ _)) (ih1 G hG)) (ih2 G hG)

private theorem discharge {G : List Nat} {a b : Nat}
    (d : Proof T (a :: G) b) : Proof T G (wim a b) :=
  discharge_aux h d G rfl

/-- Every unrestricted instance follows by deduction and Peirce's law. -/
theorem rho8_all (a b c u : Nat) : T (Code254.rho8 a b c u) := by
  let f := wim (wim c u) a
  let g := wim a c
  have hc : Proof T [wim c u, b, g, f] c :=
    .mp (.hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
      (.mp (.hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
        (.hyp (List.mem_cons_self ..)))
  have closedC : Proof T [b, g, f] c :=
    .mp (.ax (basisP h c u)) (discharge h hc)
  have result : Proof T [] (Code254.rho8 a b c u) :=
    discharge h (discharge h (discharge h closedC))
  exact proof_sound h result (by intro x hx; cases hx)

end
#print axioms rho8_all
#print axioms composition
#print axioms distribution
end SetTheory.BusyBeaver.ZFC.DomRho8
"""

def render_guarded(certificate_bytes, template_bytes):
    """Render the small guarded hierarchy; all output inferences are kernel checked.

    This specialized route binds the immutable Source149 inputs. Other certificates
    are handled by the generic renderer below, not by assumptions about this layout.
    """
    from functools import cache
    import re
    assert hashlib.sha256(certificate_bytes).hexdigest() == "3cf18a5fe9f187b50b79d97b84535ce9bf776305728b0cdfe17285e94f028452"
    assert hashlib.sha256(template_bytes).hexdigest() == "c788460c8dd0f4dda4440cae4595d73723223b385825d18df2bf94b52764d087"
    data = json.loads(certificate_bytes)
    terms, nodes = data["term_table"], data["nodes"][:61]
    assert data["format"] == "term_dag_v1"
    assert {k:data["roots"][k] for k in ("I","K","P","cd59")} == {"I":17,"K":60,"P":25,"cd59":57}
    truth = "T"

    def norm(t):
        if not isinstance(t, tuple): return t
        a,b = map(norm,t)
        return truth if a == truth and b == truth else (a,b)

    def contains(a,u):
        return a == u or isinstance(a,tuple) and (contains(a[0],u) or contains(a[1],u))

    def variables(t):
        return set().union(*map(variables,t)) if isinstance(t,tuple) else {t} if isinstance(t,int) else set()

    def substitute(t,e):
        return (substitute(t[0],e),substitute(t[1],e)) if isinstance(t,tuple) else e[t] if isinstance(t,int) else truth

    def boot_lean(t):
        if isinstance(t,tuple): return "(wim "+boot_lean(t[0])+" "+boot_lean(t[1])+")"
        return "v"+str(t) if isinstance(t,int) else "0"

    def boot_bound(u,a):
        if u == truth: return "(Nat.zero_le _)"
        if u == a: return "(Nat.le_refl _)"
        assert isinstance(a,tuple)
        if contains(a[0],u): return "(le_l "+boot_lean(a[1])+" "+boot_bound(u,a[0])+")"
        assert contains(a[1],u)
        return "(le_r "+boot_lean(a[0])+" "+boot_bound(u,a[1])+")"

    @cache
    def expression(i):
        t = terms[i]
        return (expression(t[0]),expression(t[1])) if isinstance(t,list) else t["var"] if isinstance(t,dict) else truth

    forms = [expression(n["term"]) for n in nodes]
    # Equal schemas share their earliest proof, preserving the Source149 IDs.
    canonical = {i: next(j for j in range(i + 1) if forms[j] == f)
                 for i, f in enumerate(forms)}

    def rename(a,b,e):
        if isinstance(a,int):
            assert isinstance(b,int) and e.setdefault(a,b) == b
        elif a == truth: assert b == truth
        else:
            assert isinstance(b,tuple)
            rename(a[0],b[0],e); rename(a[1],b[1],e)

    def bootstrap_call(i,e):
        i = canonical[i]
        if forms[i] == truth:
            return "h.truth", truth
        args = {v:norm(e[v]) for v in variables(forms[i])}
        raw = substitute(forms[i],args)
        output = norm(raw)
        pf = "(b"+str(i)+" h"+"".join(" "+boot_lean(args[v]) for v in sorted(args))+")"
        if raw != output:
            pf = "(show T "+boot_lean(output)+" from by simpa only [wim00] using "+pf+")"
        return pf,output

    bootstrap = {}
    for i,node in enumerate(nodes):
        assert node["id"] == i
        if canonical[i] != i or forms[i] == truth:
            continue
        f,r = forms[i],node["rule"]
        if r["kind"] == "truth":
            assert f == truth
            pf = "h.truth"
        elif r["kind"] == "dominated_rho8":
            (cu,a),((aa,c),(b,cc)) = f
            ccc,u = cu
            assert c == cc == ccc and a == aa
            pf = "(show T "+boot_lean(f)+" from by simpa only [Code254.rho8] using h.rho8 "+boot_lean(a)+" "+boot_lean(b)+" "+boot_lean(c)+" "+boot_lean(u)+" "+boot_bound(u,a)+")"
        else:
            assert r["kind"] == "mp_substitution"
            major,minor = r["major"],r["minor"]
            assert major < i and minor < i
            me = {int(k):expression(v) for k,v in r["major_substitution"].items()}
            ie = {int(k):expression(v) for k,v in r["minor_substitution"].items()}
            ma,mi = substitute(forms[major],me),substitute(forms[minor],ie)
            assert isinstance(ma,tuple)
            rho = {}
            rename(norm(ma[1]),f,rho)
            assert len(set(rho.values())) == len(rho)
            # This is the certificate's documented consequent-renaming convention.
            # Variables absent from the conclusion are instantiated by truth0.
            for v in variables(ma) | variables(mi): rho.setdefault(v,truth)
            me = {v:substitute(t,rho) for v,t in me.items()}
            ie = {v:substitute(t,rho) for v,t in ie.items()}
            pm,tm = bootstrap_call(major,me)
            pi,ti = bootstrap_call(minor,ie)
            if tm == truth:
                pm = "(show T (wim 0 0) from by simpa only [wim00] using "+pm+")"
                tm = (truth,truth)
            assert tm == (ti,f)
            pf = "(h.mp "+pm+" "+pi+")"
        names = " ".join("v"+str(v) for v in sorted(variables(f)))
        binder = " ("+names+" : Nat)" if names else ""
        bootstrap[i] = "private theorem b"+str(i)+binder+" : T "+boot_lean(f)+" :=\n  "+pf+"\n"

    def parse(text):
        tokens = re.findall(r"[()]|[^\s()]+",text)
        index = 0
        def one():
            nonlocal index
            t=tokens[index]; index+=1
            if t != "(": return t
            out=[]
            while tokens[index] != ")": out.append(one())
            index+=1
            return tuple(out)
        result=one()
        assert index == len(tokens)
        return result

    rows={int(m[1]):(m[2].split(),parse(m[3]),parse("("+m[4]+")")) for m in re.finditer(
        r"Lemma cd_(\d+) \((.*?) : nat\) : thm230 (.*?)\.\s*Proof\. exact \((.*?)\)\. Qed\.",
        template_bytes.decode(),re.S)}
    assert set(rows) == set(range(107))

    def term(t,e,normalize=True):
        if isinstance(t,str): return truth if t == "0" else e[t]
        assert len(t) == 3 and t[0] == "wim"
        pair=(term(t[1],e,normalize),term(t[2],e,normalize))
        return norm(pair) if normalize else pair

    def subst(t,e):
        return norm((subst(t[0],e),subst(t[1],e))) if isinstance(t,tuple) else e.get(t,t)

    def lean(t):
        return "(wim "+lean(t[0])+" "+lean(t[1])+")" if isinstance(t,tuple) else "0" if t == truth else t

    # A template conclusion already proved in the bootstrap needs no second
    # derivation. Equality is literal after naming its universally bound codes.
    named_boot = {i: substitute(f, {v: "v" + str(v) for v in variables(f)})
                  for i, f in enumerate(forms) if canonical[i] == i}
    reused = {}
    for n, (names, wanted, _) in rows.items():
        target = term(wanted, {v: v for v in names})
        for i, f in named_boot.items():
            if f == target:
                assert variables(forms[i]) == {int(v[1:]) for v in names}
                reused[n] = i
                break
    base={2,3,6,8,9,12,13,15,16,17,25,39,40,59}
    @cache
    def guards(n):
        if n in base or n in reused:return frozenset()
        if n == 0:return frozenset({("v1","v2")})
        names,_,body=rows[n]
        e={v:v for v in names}
        def walk(t):
            if t[0] == "T_mp":
                assert len(t)==5 and t[1:3]==("_","_")
                return walk(t[3]) | walk(t[4])
            j=int(t[0][3:]); assert j<n
            args=[term(x,e) for x in t[1:]]
            assert len(args)==len(rows[j][0])
            env=dict(zip(rows[j][0],args))
            instantiated={(subst(u,env),subst(a,env)) for u,a in guards(j)}
            return {(u,a) for u,a in instantiated if u!=truth and not contains(a,u)}
        return frozenset(walk(body))
    assert not guards(91) and not guards(106)
    assert max(map(lambda n:len(guards(n)),rows)) == 1

    used=set()
    def use(n):
        if n in used:return
        used.add(n)
        if n in base or n in reused or n==0:return
        def walk(t):
            if t[0]=="T_mp":walk(t[3]);walk(t[4])
            else:use(int(t[0][3:]))
        walk(rows[n][2])
    use(91);use(106)
    assert 91 in used and 106 in used

    def bound(u,a,available):
        if u==truth:return "(Nat.zero_le _)"
        if u==a:return "(Nat.le_refl _)"
        if (u,a) in available:return available[(u,a)]
        if isinstance(a,tuple):
            if contains(a[0],u):return "(le_l "+lean(a[1])+" "+bound(u,a[0],available)+")"
            if contains(a[1],u):return "(le_r "+lean(a[0])+" "+bound(u,a[1],available)+")"
        raise ValueError("unproved numerical guard")

    patterns=[("basisI",("a","a")),("basisK",("a",("b","a"))),
              ("basisP",((("a","b"),"a"),"a")),
              ("basisJ",(("a","b"),((("a","c"),"a"),"b")))]
    def match(p,t,e):
        if isinstance(p,str):
            if p in e:return e[p]==t
            e[p]=t;return True
        return isinstance(t,tuple) and match(p[0],t[0],e) and match(p[1],t[1],e)
    def basis(t):
        for name,p in patterns:
            e={}
            if match(p,t,e):return "("+name+" h "+" ".join(lean(e[x]) for x in ("a","b","c") if x in e)+")"
        assert isinstance(t,tuple)
        return "(h.mp (basisK h "+lean(t[1])+" "+lean(t[0])+") "+basis(t[1])+")"

    lemmas=[]
    for n,(names,wanted,body) in rows.items():
        if n not in used or n in reused:continue
        e={v:v for v in names}
        gs=sorted(guards(n),key=repr)
        available={g:"hb"+str(i) for i,g in enumerate(gs)}
        bind=" ".join("(hb"+str(i)+" : "+lean(u)+" ≤ "+lean(a)+")" for i,(u,a) in enumerate(gs))
        def walk(t):
            if t[0]=="T_mp":
                mi,miout=walk(t[3]);ma,maout=walk(t[4])
                if maout==truth:maout=(truth,truth)
                assert maout[0]==miout
                return "(h.mp "+ma+" "+mi+")",maout[1]
            j=int(t[0][3:]);assert j<n
            args=[term(x,e) for x in t[1:]]
            env=dict(zip(rows[j][0],args))
            bs=[bound(subst(u,env),subst(a,env),available) for u,a in sorted(guards(j),key=repr)]
            if j in reused:
                i = reused[j]
                assert not bs
                assert subst(named_boot[i], env) == term(rows[j][1], env)
                pf = "(b" + str(i) + " h " + " ".join(lean(env["v" + str(v)])
                       for v in sorted(variables(forms[i]))) + ")"
            else:
                pf="(cd"+str(j)+" h "+" ".join(map(lean,args))+(" "+" ".join(bs) if bs else "")+")"
            output=term(rows[j][1],env)
            if term(rows[j][1],env,False)!=output:
                pf="(show T "+lean(output)+" from by simpa only [wim00] using "+pf+")"
            return pf,output
        if n==0:
            pf="(show T "+lean(term(wanted,e))+" from by simpa only [Code254.rho8] using h.rho8 v2 v3 v0 v1 hb0)"
        elif n in base:pf=basis(term(wanted,e))
        else:
            pf,output=walk(body)
            assert output==term(wanted,e)
        lemmas.append("private theorem cd"+str(n)+" ("+" ".join(names)+" : Nat) "+bind+" :\n    T "+lean(term(wanted,e))+" := by\n  simpa only [wim00] using "+pf+"\n")
    # Retain only actual proof dependencies after schema reuse. Source149 node
    # labels remain stable, making each retained statement easy to cross-check.
    keep = set()
    def retain(i):
        if i in keep:
            return
        keep.add(i)
        for parent in map(int, re.findall(r"\bb(\d+)\b", bootstrap[i].split(":=", 1)[1])):
            assert parent < i
            retain(parent)
    for i in map(int, re.findall(r"\bb(\d+)\b", GUARDED_MIDDLE + "\n".join(lemmas))):
        retain(i)
    header = GUARDED_HEAD.replace("A 61-lemma bootstrap", "A " + str(len(keep)) + "-lemma bootstrap")
    header = header.replace("We retain 81 of its 107\nschemas; eight carry", "We retain " +
                            str(len(lemmas)) + " of its 107\nschemas; " +
                            str(sum(bool(guards(n)) for n in used if n not in reused)) + " carry")
    header = header.replace("The bootstrap is Source 149's original nodes0..60;",
                            "The bootstrap shares and prunes Source 149's original nodes0..60;")
    header = header.replace("Every emitted\nstep is", "Duplicate template conclusions reuse bootstrap lemmas. Every emitted\nstep is")
    print("retained bootstrap", len(keep), "CD templates", len(lemmas),
          "reused template conclusions", len(used & reused.keys()))
    return header+"\n".join(bootstrap[i] for i in sorted(keep))+GUARDED_MIDDLE+"\n".join(lemmas)+"\n"+GUARDED_TAIL


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("certificate", type=Path)
parser.add_argument("output", type=Path)
options = parser.add_mutually_exclusive_group()
options.add_argument("--plan", type=Path, help="use an explicit original-node plan")
options.add_argument("--no-plan", action="store_true", help="use only greedy schema pruning")
parser.add_argument("--templates", type=Path, help="CD230 template file for the guarded Source149 route")
args = parser.parse_args()
if args.templates and (args.plan or args.no_plan):
    parser.error("--templates cannot be combined with --plan or --no-plan")
src, out = args.certificate, args.output
raw = src.read_bytes()
original149 = "3cf18a5fe9f187b50b79d97b84535ce9bf776305728b0cdfe17285e94f028452"
if not args.plan and not args.no_plan and hashlib.sha256(raw).hexdigest() == original149:
    template_path = args.templates or (Path(__file__).resolve().parents[5] /
        "SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/149-dom-theory-ev-CD230.v")
    out.write_text(render_guarded(raw, template_path.read_bytes()), encoding="utf-8", newline="\n")
    print("wrote shared guarded hierarchy and deduction")
    raise SystemExit(0)
if args.templates:
    parser.error("--templates requires the exact original Source149 certificate")
if args.plan or (not args.no_plan and hashlib.sha256(raw).hexdigest() == original149):
    # The shared replay validates its input hash, substitutions and acyclic order.
    # Its output remains untrusted: the direct proofs below are checked by Lean.
    directory = Path(__file__).resolve().with_name("rho8plan")
    plan_path = args.plan or directory / "plan.json"
    spec = importlib.util.spec_from_file_location("rho8_plan", directory / "replay.py")
    replay = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(replay)
    d = json.loads(replay.replay(raw, json.loads(plan_path.read_text())))
    print("replayed original-node plan:", len(d["nodes"]), "proof nodes")
else:
    # Other term_dag_v1 inputs retain the generic, solver-free rendering interface.
    d = json.loads(raw)
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
