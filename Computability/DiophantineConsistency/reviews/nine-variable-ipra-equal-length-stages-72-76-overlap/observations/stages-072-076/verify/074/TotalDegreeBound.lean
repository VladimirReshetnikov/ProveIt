import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# A syntactic total-degree bound tactic

`total_degree_bound` proves goals `p.totalDegree ≤ n` for an explicit `MvPolynomial`
expression `p` built from variables, constants, numerals, `+`, `-`, `*`, negation
and natural powers. It reads the bound off the syntax tree: variables count one,
constants zero, sums take the maximum and products add. Shared subterms are
bounded once. The bound ignores cancellation, so a polynomial whose leading
terms cancel needs a rewrite to a cancellation-free form first.
-/

namespace DiophantineConsistency.TotalDegreeBound

open MvPolynomial Lean Meta Elab Tactic

variable {σ R : Type*} [CommRing R]

theorem add_le {p q : MvPolynomial σ R} {a b n : ℕ} (hp : p.totalDegree ≤ a)
    (hq : q.totalDegree ≤ b) (ha : a ≤ n) (hb : b ≤ n) : (p + q).totalDegree ≤ n :=
  (totalDegree_add p q).trans (max_le (hp.trans ha) (hq.trans hb))

theorem sub_le {p q : MvPolynomial σ R} {a b n : ℕ} (hp : p.totalDegree ≤ a)
    (hq : q.totalDegree ≤ b) (ha : a ≤ n) (hb : b ≤ n) : (p - q).totalDegree ≤ n :=
  (totalDegree_sub p q).trans (max_le (hp.trans ha) (hq.trans hb))

theorem mul_le {p q : MvPolynomial σ R} {a b n : ℕ} (hp : p.totalDegree ≤ a)
    (hq : q.totalDegree ≤ b) (h : a + b ≤ n) : (p * q).totalDegree ≤ n :=
  ((totalDegree_mul p q).trans (Nat.add_le_add hp hq)).trans h

theorem pow_le {p : MvPolynomial σ R} {a n : ℕ} (k : ℕ) (hp : p.totalDegree ≤ a)
    (h : k * a ≤ n) : (p ^ k).totalDegree ≤ n :=
  ((totalDegree_pow p k).trans (Nat.mul_le_mul_left k hp)).trans h

theorem neg_le {p : MvPolynomial σ R} {a : ℕ} (hp : p.totalDegree ≤ a) :
    (-p).totalDegree ≤ a := by rwa [totalDegree_neg]

theorem X_le (i : σ) : (X i : MvPolynomial σ R).totalDegree ≤ 1 := by
  have h := totalDegree_monomial_le (R := R) (Finsupp.single i 1) 1
  rwa [Finsupp.sum_single_index rfl] at h

theorem C_le (c : R) : (C c : MvPolynomial σ R).totalDegree ≤ 0 := (totalDegree_C c).le

theorem natCast_le (k : ℕ) : (k : MvPolynomial σ R).totalDegree ≤ 0 := by
  simpa only [map_natCast] using (totalDegree_C (σ := σ) (k : R)).le

theorem ofNat_le (k : ℕ) [k.AtLeastTwo] :
    (OfNat.ofNat k : MvPolynomial σ R).totalDegree ≤ 0 := natCast_le k

theorem zero_le' : (0 : MvPolynomial σ R).totalDegree ≤ 0 := totalDegree_zero.le

theorem one_le : (1 : MvPolynomial σ R).totalDegree ≤ 0 := totalDegree_one.le

private abbrev Cache := Std.HashMap Expr (Nat × Expr)

/-- A proof of `a ≤ b` for closed natural-number terms, by `decide`. -/
private def leProof (a b : Expr) : MetaM Expr := do
  mkDecideProof (← mkAppM ``LE.le #[a, b])

/-- Returns `(n, h)` with `h : e.totalDegree ≤ n`. -/
private partial def bound (e : Expr) : StateT Cache MetaM (Nat × Expr) := do
  if let some r := (← get)[e]? then return r
  let lit := mkNatLit
  let r ← match e.getAppFnArgs with
    | (``HAdd.hAdd, #[_, _, _, _, a, b]) | (``HSub.hSub, #[_, _, _, _, a, b]) => do
        let (m, pa) ← bound a
        let (k, pb) ← bound b
        let n := max m k
        let thm := if e.isAppOf ``HAdd.hAdd then ``add_le else ``sub_le
        pure (n, ← mkAppM thm #[pa, pb, ← leProof (lit m) (lit n), ← leProof (lit k) (lit n)])
    | (``HMul.hMul, #[_, _, _, _, a, b]) => do
        let (m, pa) ← bound a
        let (k, pb) ← bound b
        pure (m + k, ← mkAppM ``mul_le
          #[pa, pb, ← leProof (← mkAppM ``HAdd.hAdd #[lit m, lit k]) (lit (m + k))])
    | (``Neg.neg, #[_, _, a]) => do
        let (m, pa) ← bound a
        pure (m, ← mkAppM ``neg_le #[pa])
    | (``HPow.hPow, #[_, _, _, _, a, k]) => do
        let some kv ← (evalNat k).run | throwError "total_degree_bound: exponent {k}"
        let (m, pa) ← bound a
        pure (kv * m, ← mkAppM ``pow_le
          #[k, pa, ← leProof (← mkAppM ``HMul.hMul #[k, lit m]) (lit (kv * m))])
    | _ => do
        let ty ← instantiateMVars (← inferType e)
        let .some (σ, R) := (match ty.getAppFnArgs with
          | (``MvPolynomial, #[σ, R, _]) => some (σ, R) | _ => none)
          | throwError "total_degree_bound: {e} is not an MvPolynomial"
        let leaves : List (Nat × Name × Array (Option Expr)) :=
          match e.getAppFnArgs with
          | (``MvPolynomial.X, #[_, _, _, i]) => [(1, ``X_le, #[σ, R, none, i])]
          | (``DFunLike.coe, #[_, _, _, _, f, c]) =>
              if f.isAppOf ``MvPolynomial.C then [(0, ``C_le, #[σ, R, none, c])] else []
          | (``OfNat.ofNat, #[_, k, _]) =>
              [(0, ``ofNat_le, #[σ, R, none, k, none]), (0, ``zero_le', #[σ, R, none]),
                (0, ``one_le, #[σ, R, none])]
          | (``Nat.cast, #[_, _, k]) => [(0, ``natCast_le, #[σ, R, none, k])]
          | _ => []
        let found ← leaves.findSomeM? fun (n, thm, args) => do
          try
            let pf ← mkAppOptM thm args
            let goal ← mkAppM ``LE.le #[← mkAppM ``MvPolynomial.totalDegree #[e], lit n]
            if ← isDefEq (← inferType pf) goal then return some (n, pf) else return none
          catch _ => return none
        let some r := found | throwError "total_degree_bound: cannot bound {e}"
        pure r
  modify (·.insert e r)
  return r

/-- Proves `p.totalDegree ≤ n` from the syntax of `p`, as described in the module doc. -/
elab "total_degree_bound" : tactic => liftMetaFinishingTactic fun g => do
  let t ← instantiateMVars (← whnfR (← g.getType))
  let some (_, lhs, rhs) := t.le? | throwError "total_degree_bound: goal is not `≤`"
  let some n ← (evalNat rhs).run | throwError "total_degree_bound: bound {rhs} is not a numeral"
  let ((m, pf), _) ← (bound lhs.appArg!).run {}
  unless m ≤ n do throwError "total_degree_bound: syntactic bound {m} exceeds {n}"
  g.assign (← mkAppM ``le_trans #[pf, ← leProof (mkNatLit m) rhs])

end DiophantineConsistency.TotalDegreeBound
