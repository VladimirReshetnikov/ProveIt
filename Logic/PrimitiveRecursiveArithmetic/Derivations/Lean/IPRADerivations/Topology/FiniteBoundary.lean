import IPRADerivations.Topology.FiniteInteriorClosure

/-!
# Exterior and boundary decomposition on a finite preorder

Packet: `topology/general_topology_ipra_2026-11-19`, `paper/sections/03_finite.tex`, Theorem F05 ("exterior and
boundary decomposition"): with `Ext A = Int(A^c)` and `Bd A = Cl A ∩ Cl(A^c)`, every point lies in the interior,
the exterior or the boundary. In the paper "All subsets here have Boolean codes. Consequently bounded searches,
complement formation, and case distinctions on membership are legitimate in iPRA." Accordingly the subsets
here are families of iPRA formulas with derivable decisions `A y ∨ ¬A y`.

* `dec_conj`: finite conjunctions of decidable formulas are decidable;
* `neg_conj`: for decidable components, `¬⋀_i f_i` gives `⋁_i ¬f_i` (a bounded search, not Markov's principle);
* `int_or_cl_neg`: `Int A x ∨ Cl(¬A) x`;
* `trichotomy`: `Int A x ∨ (Ext A x ∨ Bd A x)`.
-/

namespace LeanProofs.IPRA.Topology.FiniteBoundary

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.IntersectionEnumeration (disjFin disjFin_intro disjFin_imp)
open LeanProofs.IPRA.Topology.FiniteInteriorClosure
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `φ ∨ ¬φ`. -/
def dec (φ : Fm PTm n) : Fm PTm n := φ ⋎ neg φ

theorem dec_conj : {k : ℕ} → {f : Fin k → Fm PTm n} → (∀ i, Γ ⊢[PRAAx] dec (f i)) →
    (Γ ⊢[PRAAx] dec (conjFin f))
  | 0, _, _ => .orI₁ (.eqRefl _)
  | 1, _, h => h 0
  | _ + 2, f, h => by
    have h0 := h 0
    have hs := dec_conj (f := fun i => f i.succ) (fun i => h i.succ)
    refine .orE h0 ?_ ?_
    · refine .orE hs.wk ?_ ?_
      · exact .orI₁ (.andI Prf.hyp1 Prf.hyp0)
      · exact .orI₂ (.impI (.impE Prf.hyp1 (Prf.andE₂ Prf.hyp0)))
    · exact .orI₂ (.impI (.impE Prf.hyp1 (Prf.andE₁ Prf.hyp0)))

theorem neg_conj : {k : ℕ} → {f : Fin k → Fm PTm n} → (∀ i, Γ ⊢[PRAAx] dec (f i)) →
    (Γ ⊢[PRAAx] neg (conjFin f) ⟶ disjFin fun i => neg (f i))
  | 0, _, _ => .impI (.botE _ (.impE Prf.hyp0 (.eqRefl _)))
  | 1, _, _ => .impI Prf.hyp0
  | _ + 2, f, h => by
    have hs := neg_conj (f := fun i => f i.succ) (fun i => (h i.succ))
    have ds := dec_conj (Γ := Γ) (f := fun i => f i.succ) (fun i => h i.succ)
    refine .impI (.orE (h 0).wk ?_ ?_)
    · -- `f 0` holds: the tail fails
      refine .orE ds.wk.wk ?_ ?_
      · exact .botE _ (.impE LeanProofs.IPRA.hyp2 (.andI Prf.hyp1 Prf.hyp0))
      · exact .orI₂ (.impE hs.wk.wk.wk Prf.hyp0)
    · exact .orI₁ Prf.hyp0

variable {k : ℕ} {rel : Fin k → Fin k → Prop} [DecidableRel rel]

/-- `Int A x ∨ Cl(¬A) x` for decidable `A`. -/
theorem int_or_cl_neg {A : Fin k → Fm PTm n} (hA : ∀ y, Γ ⊢[PRAAx] dec (A y)) (x : Fin k) :
    Γ ⊢[PRAAx] Int rel A x ⋎ Cl rel (fun y => neg (A y)) x := by
  have hd : ∀ y, Γ ⊢[PRAAx] dec (if rel x y then A y else truth) := fun y => by
    by_cases hxy : rel x y
    · rw [if_pos hxy]; exact hA y
    · rw [if_neg hxy]; exact .orI₁ (.eqRefl _)
  refine .orE (dec_conj hd) (.orI₁ Prf.hyp0) (.orI₂ ?_)
  refine .impE ?_ (.impE (neg_conj hd).wk Prf.hyp0)
  refine disjFin_imp fun y => ?_
  by_cases hxy : rel x y
  · simp only [hxy, if_true]
    exact .impI (cl_intro hxy Prf.hyp0)
  · simp only [hxy, if_false]
    exact .impI (.botE _ (.impE Prf.hyp0 (.eqRefl _)))

/-- F05: every point is interior, exterior or a boundary point. -/
theorem trichotomy {A : Fin k → Fm PTm n} (hA : ∀ y, Γ ⊢[PRAAx] dec (A y)) (x : Fin k) :
    Γ ⊢[PRAAx] Int rel A x ⋎ (Int rel (fun y => neg (A y)) x ⋎ (Cl rel A x ⋏ Cl rel (fun y => neg (A y)) x)) := by
  have hd : ∀ y, Γ ⊢[PRAAx] dec (if rel x y then neg (A y) else truth) := fun y => by
    by_cases hxy : rel x y
    · rw [if_pos hxy]
      exact .orE (hA y) (.orI₂ (.impI (.impE Prf.hyp0 Prf.hyp1))) (.orI₁ Prf.hyp0)
    · rw [if_neg hxy]; exact .orI₁ (.eqRefl _)
  refine .orE (int_or_cl_neg hA x) (.orI₁ Prf.hyp0) ?_
  -- `Cl(¬A) x`: decide `Ext A x`
  refine .orE (dec_conj hd).wk (.orI₂ (.orI₁ Prf.hyp0)) ?_
  -- `¬Int(¬A) x`, hence `Cl(¬¬A) x`, hence `Cl A x` by decidability
  refine .orI₂ (.orI₂ (.andI ?_ Prf.hyp1))
  refine .impE ?_ (.impE (neg_conj hd).wk.wk Prf.hyp0)
  refine disjFin_imp fun y => ?_
  by_cases hxy : rel x y
  · simp only [hxy, if_true]
    refine .impI (.orE (hA y).wk.wk.wk (cl_intro hxy Prf.hyp0) (.botE _ (.impE Prf.hyp1 Prf.hyp0)))
  · simp only [hxy, if_false]
    exact .impI (.botE _ (.impE Prf.hyp0 (.eqRefl _)))

end LeanProofs.IPRA.Topology.FiniteBoundary
