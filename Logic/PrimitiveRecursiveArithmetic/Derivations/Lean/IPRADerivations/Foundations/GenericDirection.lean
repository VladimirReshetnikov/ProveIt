import IPRADerivations.Foundations.VandermondeDeterminant
import IPRADerivations.Foundations.IntersectionEnumeration

/-!
# A bounded generic direction (`ipra_resources_and_elimination_2026-11-15`, `lem:elim-shear`)

Packet: `foundations/ipra_resources_and_elimination_2026-11-15`, lemma `lem:elim-shear`: "There is
a `c ∈ {0, …, d + e}` such that `a(c) := F_d(−c, 1) ≠ 0`, `b(c) := G_e(−c, 1) ≠ 0` (E2)." Proof:
"Their product is nonzero: the product of their leading coefficients is nonzero in `ℚ`. ...
Consequently `a(T) b(T)` cannot vanish at all `d + e + 1` candidates `0, …, d + e`. A scan with
a success flag, frozen at the first passing candidate, returns the required `c`."

Derived for integer terms and every number `k` of coefficients (a parameter of the Lean
statements; for the lemma `k = d + e + 1` and the polynomial is `a(T) b(T)`):

* `zdec`: an equation of integer terms holds or fails (decidable equality);
* `all_or_some`: for a finite family of integer terms, either all are zero or one is nonzero;
* `some_nonroot`: a polynomial with a nonzero coefficient, evaluated at `k` pairwise distinct
  points, is nonzero at one of them (from `root_bound` of
  `Foundations/VandermondeDeterminant`);
* `lit_succ_ne`, `lit_distinct`: the numerals `0, 1, …` are pairwise distinct;
* `generic_direction`: among the candidates `0, …, k − 1` there is one at which the polynomial
  does not vanish: the existence statement of `lem:elim-shear`.

The conclusion is a finite disjunction over the candidates; the first disjunct that holds is
the packet's canonical `c`. Not derived: the shear `F ↦ F_c` on coefficient arrays, the
identification of `a(c)`, `b(c)` with the leading coefficients of `F_c`, `G_c` (E3), and the
scan as a primitive recursive function of the arrays.
-/

namespace LeanProofs.IPRA.Foundations.GenericDirection

open_ipra exports
open LeanProofs.IPRA.Foundations.NullVectorDeterminant
open LeanProofs.IPRA.Foundations.VandermondeDeterminant (root_bound ne_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Equality of integer terms is decidable. -/
theorem zdec (u v : ZT n) : Γ ⊢[PRAAx] ZT.eq u v ⋎ neg (ZT.eq u v) :=
  eq_or_ne (u.pos + v.neg) (v.pos + u.neg)

/-- Either all members of a finite family vanish, or one of them does not. -/
theorem all_or_some : {k : ℕ} → (f : Fin k → ZT n) →
    (Γ ⊢[PRAAx] conjFin (fun i => ZT.eq (f i) (ZT.natLit 0)) ⋎
      disjFin (fun i => neg (ZT.eq (f i) (ZT.natLit 0))))
  | 0, _ => .orI₁ (.eqRefl _)
  | 1, f => zdec (f 0) (ZT.natLit 0)
  | _ + 2, f =>
    .orE (zdec (f 0) (ZT.natLit 0))
      (.orE (all_or_some fun i => f i.succ).wk
        (.orI₁ (.andI Prf.hyp1 Prf.hyp0))
        (.orI₂ (.orI₂ Prf.hyp0)))
      (.orI₂ (.orI₁ Prf.hyp0))

/-- A polynomial with a nonzero coefficient does not vanish at all of `k` pairwise distinct
points. -/
theorem some_nonroot {k : ℕ} {v c : Vec k n}
    (hv : ∀ i j, i < j → (Γ ⊢[PRAAx] neg (ZT.eq (v j - v i) (ZT.natLit 0))))
    (j : Fin k) (hne : Γ ⊢[PRAAx] neg (ZT.eq (c j) (ZT.natLit 0))) :
    Γ ⊢[PRAAx] disjFin
      (fun i => neg (ZT.eq (ZT.sumFin fun l => vpow (v i) l * c l) (ZT.natLit 0))) := by
  refine .orE (all_or_some fun i => ZT.sumFin fun l => vpow (v i) l * c l) ?_ Prf.hyp0
  refine .botE _ (.impE hne.wk ?_)
  exact root_bound (fun i j h => (hv i j h).wk) (fun i => conjFin_elim Prf.hyp0 i) j

/-- A positive numeral is not zero. -/
theorem lit_succ_ne (m : ℕ) :
    Γ ⊢[PRAAx] neg (ZT.eq (ZT.natLit (m + 1) : ZT n) (ZT.natLit 0)) := by
  refine .impI (succ_ne_zero' _ (a := num m) ?_)
  have h : (ZT.eq (ZT.natLit (m + 1) : ZT n) (ZT.natLit 0) :: Γ) ⊢[PRAAx]
      succ (num m) + zero ≐ zero + zero := Prf.hyp0
  exact (add_zero _).eqSymm.eqTrans (h.eqTrans (zero_add _))

/-- Distinct numerals are distinct integers. -/
theorem lit_distinct {i j : ℕ} (h : i < j) :
    Γ ⊢[PRAAx] neg (ZT.eq (ZT.natLit j - ZT.natLit i : ZT n) (ZT.natLit 0)) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = i + (m + 1) := ⟨j - i - 1, by omega⟩
  refine ne_congr (Y := ZT.natLit (m + 1)) (ZT.derive ?_) (lit_succ_ne m)
  simp only [ZT.toZ_sub, ZT.toZ_natLit]
  push_cast
  ring

/-- `lem:elim-shear`, existence: a polynomial with `k` coefficients, one of them nonzero, does
not vanish at one of the candidates `0, …, k − 1`. -/
theorem generic_direction {k : ℕ} {c : Vec k n} (j : Fin k)
    (hne : Γ ⊢[PRAAx] neg (ZT.eq (c j) (ZT.natLit 0))) :
    Γ ⊢[PRAAx] disjFin (fun i : Fin k =>
      neg (ZT.eq (ZT.sumFin fun l => vpow (ZT.natLit (i : ℕ)) l * c l) (ZT.natLit 0))) :=
  some_nonroot (v := fun i : Fin k => ZT.natLit (i : ℕ))
    (fun _ _ h => lit_distinct (Fin.lt_def.mp h)) j hne

end LeanProofs.IPRA.Foundations.GenericDirection
