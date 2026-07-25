import PAFiniteBasisReduction.FiniteSkolemCut

/-!
# Canonical selectors in every raw model of PA

`FiniteSkolemCut.CanonicalSelectors` deliberately exposes totality and
functionality of its object-language least/default graph.  This file
discharges that interface from semantic validity of the genuine PA axioms.

The only induction below is an instance of the object-language PA induction
schema.  In particular, the carrier remains a `PA.PreModel`; no meta-level
`PA.Model` induction field is introduced.
-/

namespace LeanProofs
namespace PAFiniteBasisReduction

open SetTheory PA

universe u

namespace FiniteSkolemCut

/-- Semantic validity of every sealed PA axiom in a raw arithmetic model. -/
def RawPASatisfies {alpha : Type u} (M : PA.PreModel alpha) : Prop :=
  ∀ (e : Nat → alpha) (f : PA.Formula),
    PA.Formula.Ax_s f → PA.Formula.Sat M e f

/-- Soundness convenience for the closed PA derivations already developed in
`PAHF.PASyntax`. -/
theorem sat_of_bprov_axs {alpha : Type u} {M : PA.PreModel alpha}
    (hPA : RawPASatisfies M) {phi : PA.Formula}
    (h : PA.Formula.BProv PA.Formula.Ax_s [] phi)
    (e : Nat → alpha) : PA.Formula.Sat M e phi := by
  exact PA.Formula.soundness_BProv M h e
    (fun ax hax => hPA e ax hax)
    (by intro g hg; cases hg)

/-- Contextual form of `sat_of_bprov_axs`.  This is convenient when a
previously proved PA order theorem is applied to semantic hypotheses. -/
theorem sat_of_bprov_axs_context {alpha : Type u} {M : PA.PreModel alpha}
    (hPA : RawPASatisfies M) {G : List PA.Formula} {phi : PA.Formula}
    (h : PA.Formula.BProv PA.Formula.Ax_s G phi)
    (e : Nat → alpha)
    (hG : ∀ g ∈ G, PA.Formula.Sat M e g) :
    PA.Formula.Sat M e phi := by
  exact PA.Formula.soundness_BProv M h e
    (fun ax hax => hPA e ax hax) hG

/-- The strict and non-strict arithmetic relations, stated directly on a raw
PA carrier.  They are useful for keeping environment bookkeeping out of the
least-number argument. -/
def RawLt {alpha : Type u} (M : PA.PreModel alpha) (x y : alpha) : Prop :=
  ∃ d, M.add x (M.succ d) = y

def RawLe {alpha : Type u} (M : PA.PreModel alpha) (x y : alpha) : Prop :=
  ∃ d, M.add x d = y

@[simp] theorem sat_ltTermAt_iff_raw {alpha : Type u}
    (M : PA.PreModel alpha) (left right : PA.Term) (e : Nat → alpha) :
    PA.Formula.Sat M e (PA.Formula.ltTermAt left right) ↔
      RawLt M (PA.Term.eval M e left) (PA.Term.eval M e right) := by
  simp [RawLt, PA.Formula.ltTermAt, PA.Formula.Sat,
    PA.Term.eval, PA.Term.eval_rename, scons]

@[simp] theorem sat_leTermAt_iff_raw {alpha : Type u}
    (M : PA.PreModel alpha) (left right : PA.Term) (e : Nat → alpha) :
    PA.Formula.Sat M e (PA.Formula.leTermAt left right) ↔
      RawLe M (PA.Term.eval M e left) (PA.Term.eval M e right) := by
  simp [RawLe, PA.Formula.leTermAt, PA.Formula.Sat,
    PA.Term.eval, PA.Term.eval_rename, scons]

@[simp] theorem sat_ltTermAt_vars_iff {alpha : Type u}
    (M : PA.PreModel alpha) (x y : alpha) (e : Nat → alpha) :
    PA.Formula.Sat M (scons x (scons y e))
        (PA.Formula.ltTermAt (PA.Term.var 0) (PA.Term.var 1)) ↔
      RawLt M x y := by
  simp [RawLt, PA.Formula.ltTermAt, PA.Formula.Sat,
    PA.Term.eval, PA.Term.eval_rename, scons]

@[simp] theorem sat_leTermAt_vars_iff {alpha : Type u}
    (M : PA.PreModel alpha) (x y : alpha) (e : Nat → alpha) :
    PA.Formula.Sat M (scons x (scons y e))
        (PA.Formula.leTermAt (PA.Term.var 0) (PA.Term.var 1)) ↔
      RawLe M x y := by
  simp [RawLe, PA.Formula.leTermAt, PA.Formula.Sat,
    PA.Term.eval, PA.Term.eval_rename, scons]

/-- Nothing is strictly below zero in a raw model satisfying PA. -/
theorem not_rawLt_zero {alpha : Type u} {M : PA.PreModel alpha}
    (hPA : RawPASatisfies M) (x : alpha) : ¬RawLt M x M.zero := by
  intro hlt
  let f := PA.Formula.ltTermAt (PA.Term.var 0) PA.Term.zero
  let G : List PA.Formula := [f]
  have hass : PA.Formula.BProv PA.Formula.Ax_s G f :=
    PA.Formula.BProv_ass (B := PA.Formula.Ax_s) (G := G) (by simp [G])
  have hzeroLe : PA.Formula.BProv PA.Formula.Ax_s G
      (PA.Formula.leTermAt PA.Term.zero (PA.Term.var 0)) :=
    PA.Formula.BProv_Ax_s_leTermAt_zero_left (PA.Term.var 0)
  have hbot : PA.Formula.BProv PA.Formula.Ax_s G PA.Formula.bot :=
    PA.Formula.BProv_Ax_s_ltTermAt_leTermAt_bot hass hzeroLe
  let e : Nat → alpha := fun _ => M.zero
  have hsat : PA.Formula.Sat M (scons x e) f := by
    simpa [f, RawLt, PA.Formula.ltTermAt, PA.Formula.Sat,
      PA.Term.eval, PA.Term.eval_rename, scons] using hlt
  exact sat_of_bprov_axs_context hPA hbot (scons x e)
    (by
      intro g hg
      have : g = f := by simpa [G] using hg
      simpa [this] using hsat)

/-- The PA order theorem `z < S x → z < x ∨ z = x`, transported to
raw semantics. -/
theorem rawLt_succ_cases {alpha : Type u} {M : PA.PreModel alpha}
    (hPA : RawPASatisfies M) {z x : alpha} (h : RawLt M z (M.succ x)) :
    RawLt M z x ∨ z = x := by
  let f := PA.Formula.ltTermAt
    (PA.Term.var 0) (PA.Term.succ (PA.Term.var 1))
  let G : List PA.Formula := [f]
  have hass : PA.Formula.BProv PA.Formula.Ax_s G f :=
    PA.Formula.BProv_ass (B := PA.Formula.Ax_s) (G := G) (by simp [G])
  have hcases : PA.Formula.BProv PA.Formula.Ax_s G
      (PA.Formula.or
        (PA.Formula.ltTermAt (PA.Term.var 0) (PA.Term.var 1))
        (PA.Formula.eq (PA.Term.var 0) (PA.Term.var 1))) :=
    PA.Formula.BProv_Ax_s_ltTermAt_succ_right_cases hass
  let e : Nat → alpha := fun _ => M.zero
  have hsat : PA.Formula.Sat M (scons z (scons x e)) f := by
    simpa [f, RawLt, PA.Formula.ltTermAt, PA.Formula.Sat,
      PA.Term.eval, PA.Term.eval_rename, scons] using h
  have hout := sat_of_bprov_axs_context hPA hcases
    (scons z (scons x e)) (by
      intro g hg
      have : g = f := by simpa [G] using hg
      simpa [this] using hsat)
  simpa [RawLt, PA.Formula.ltTermAt, PA.Formula.Sat,
    PA.Term.eval, PA.Term.eval_rename, scons] using hout

/-- Total comparison, inherited from the corresponding PA theorem. -/
theorem rawLe_or_gt {alpha : Type u} {M : PA.PreModel alpha}
    (hPA : RawPASatisfies M) (x y : alpha) :
    RawLe M x y ∨ RawLt M y x := by
  let e : Nat → alpha := fun _ => M.zero
  have h := sat_of_bprov_axs hPA
    (PA.Formula.BProv_Ax_s_leTermAt_or_gtTermAt
      (PA.Term.var 0) (PA.Term.var 1)) (scons x (scons y e))
  simpa [RawLe, RawLt, PA.Formula.leTermAt, PA.Formula.ltTermAt,
    PA.Formula.Sat, PA.Term.eval, PA.Term.eval_rename, scons] using h

/-- Antisymmetry of non-strict PA order, again obtained by soundness of the
already kernel-checked PA derivation. -/
theorem rawLe_antisymm {alpha : Type u} {M : PA.PreModel alpha}
    (hPA : RawPASatisfies M) {x y : alpha}
    (hxy : RawLe M x y) (hyx : RawLe M y x) : x = y := by
  let fxy := PA.Formula.leTermAt (PA.Term.var 0) (PA.Term.var 1)
  let fyx := PA.Formula.leTermAt (PA.Term.var 1) (PA.Term.var 0)
  let G : List PA.Formula := [fxy, fyx]
  have hassXY : PA.Formula.BProv PA.Formula.Ax_s G fxy :=
    PA.Formula.BProv_ass (B := PA.Formula.Ax_s) (G := G) (by simp [G])
  have hassYX : PA.Formula.BProv PA.Formula.Ax_s G fyx :=
    PA.Formula.BProv_ass (B := PA.Formula.Ax_s) (G := G) (by simp [G])
  have heq : PA.Formula.BProv PA.Formula.Ax_s G
      (PA.Formula.eq (PA.Term.var 0) (PA.Term.var 1)) :=
    PA.Formula.BProv_Ax_s_eq_of_leTermAt_leTermAt hassXY hassYX
  let e : Nat → alpha := fun _ => M.zero
  have hsatXY : PA.Formula.Sat M (scons x (scons y e)) fxy := by
    simpa [fxy, RawLe, PA.Formula.leTermAt, PA.Formula.Sat,
      PA.Term.eval, PA.Term.eval_rename, scons] using hxy
  have hsatYX : PA.Formula.Sat M (scons x (scons y e)) fyx := by
    simpa [fyx, RawLe, PA.Formula.leTermAt, PA.Formula.Sat,
      PA.Term.eval, PA.Term.eval_rename, scons] using hyx
  have hout := sat_of_bprov_axs_context hPA heq
    (scons x (scons y e)) (by
      intro g hg
      simp [G] at hg
      rcases hg with rfl | rfl
      · exact hsatXY
      · exact hsatYX)
  simpa [PA.Formula.Sat, PA.Term.eval, scons] using hout

theorem raw_order_trichotomy {alpha : Type u} {M : PA.PreModel alpha}
    (hPA : RawPASatisfies M) (x y : alpha) :
    x = y ∨ RawLt M x y ∨ RawLt M y x := by
  rcases rawLe_or_gt hPA x y with hxy | hyx
  · rcases rawLe_or_gt hPA y x with hyx' | hxy'
    · exact Or.inl (rawLe_antisymm hPA hxy hyx')
    · exact Or.inr (Or.inl hxy')
  · exact Or.inr (Or.inr hyx)

/-- Exact semantics of the `noSmallerGraph` component. -/
theorem sat_noSmallerGraph_iff {alpha : Type u} (M : PA.PreModel alpha)
    (body : PA.Formula) (out : alpha) (e : Nat → alpha) :
    PA.Formula.Sat M (scons out e) (noSmallerGraph body) ↔
      ∀ z,
        PA.Formula.Sat M (scons z (scons out e))
            (PA.Formula.ltTermAt (PA.Term.var 0) (PA.Term.var 1)) →
          ¬PA.Formula.Sat M (scons z e) body := by
  simp only [noSmallerGraph, PA.Formula.Sat]
  constructor
  · intro h z hlt hz
    apply h z hlt
    exact (PA.Formula.Sat_rename M body (SetTheory.up Nat.succ)
      (scons z (scons out e))).mpr
      ((PA.Formula.Sat_ext M body (fun i => by cases i <;> rfl)).mpr hz)
  · intro h z hlt hz
    apply h z hlt
    exact (PA.Formula.Sat_ext M body (fun i => by cases i <;> rfl)).mp
      ((PA.Formula.Sat_rename M body (SetTheory.up Nat.succ)
        (scons z (scons out e))).mp hz)

/-- Semantic induction for an object-language predicate in any raw model
satisfying all sealed PA axioms. -/
theorem definable_induction {alpha : Type u} {M : PA.PreModel alpha}
    (hPA : RawPASatisfies M) (phi : PA.Formula) (e : Nat → alpha)
    (hzero : PA.Formula.Sat M (scons M.zero e) phi)
    (hsucc : ∀ x,
      PA.Formula.Sat M (scons x e) phi →
      PA.Formula.Sat M (scons (M.succ x) e) phi) :
    ∀ x, PA.Formula.Sat M (scons x e) phi := by
  have hsealed : ∀ v : Nat → alpha,
      PA.Formula.Sat M v
        (PA.Formula.sealPA (PA.Formula.inductionForm phi)) := by
    intro v
    exact hPA v _ (PA.Formula.Ax_s_induction phi)
  have hindAll : ∀ v : Nat → alpha,
      PA.Formula.Sat M v (PA.Formula.inductionForm phi) :=
    (PA.Formula.seal_valid M (PA.Formula.inductionForm phi)).mp hsealed
  have hind := hindAll e
  simp only [PA.Formula.inductionForm, PA.Formula.Sat] at hind
  apply hind
  refine ⟨(PA.Formula.sat_substZero M phi e).mpr hzero, ?_⟩
  intro x hx
  exact (PA.Formula.sat_substSuccVar M phi e x).mpr (hsucc x hx)

/-- Every nonempty definable subset has a least element.  The proof is the
usual least-number argument, but carried out semantically from one genuine
instance of the first-order PA induction schema. -/
theorem definable_least_witness {alpha : Type u} {M : PA.PreModel alpha}
    (hPA : RawPASatisfies M) (body : PA.Formula) (e : Nat → alpha)
    (hex : ∃ d, PA.Formula.Sat M (scons d e) body) :
    ∃ out,
      PA.Formula.Sat M (scons out e) body ∧
      ∀ z, RawLt M z out → ¬PA.Formula.Sat M (scons z e) body := by
  classical
  apply Classical.byContradiction
  intro hnone
  have hnoSmallerAll : ∀ x,
      PA.Formula.Sat M (scons x e) (noSmallerGraph body) := by
    apply definable_induction hPA (noSmallerGraph body) e
    · apply (sat_noSmallerGraph_iff M body M.zero e).mpr
      intro z hlt
      exact False.elim
        (not_rawLt_zero hPA z
          ((sat_ltTermAt_vars_iff M z M.zero e).mp hlt))
    · intro x hx
      have hxNo := (sat_noSmallerGraph_iff M body x e).mp hx
      apply (sat_noSmallerGraph_iff M body (M.succ x) e).mpr
      intro z hlt hzBody
      have hzLt : RawLt M z (M.succ x) :=
        (sat_ltTermAt_vars_iff M z (M.succ x) e).mp hlt
      rcases rawLt_succ_cases hPA hzLt with hzLtX | hzx
      · exact hxNo z
          ((sat_ltTermAt_vars_iff M z x e).mpr hzLtX) hzBody
      · subst z
        apply hnone
        refine ⟨x, hzBody, ?_⟩
        intro z hzLtX
        exact hxNo z ((sat_ltTermAt_vars_iff M z x e).mpr hzLtX)
  rcases hex with ⟨d, hd⟩
  apply hnone
  refine ⟨d, hd, ?_⟩
  intro z hzLt
  exact (sat_noSmallerGraph_iff M body d e).mp (hnoSmallerAll d) z
    ((sat_ltTermAt_vars_iff M z d e).mpr hzLt)

theorem leastDefaultGraph_total_of_pa {alpha : Type u}
    {M : PA.PreModel alpha} (hPA : RawPASatisfies M)
    (body : PA.Formula) (e : Nat → alpha) :
    ∃ out, PA.Formula.Sat M (scons out e) (leastDefaultGraph body) := by
  classical
  by_cases hex : ∃ d, PA.Formula.Sat M (scons d e) body
  · rcases definable_least_witness hPA body e hex with
      ⟨out, hout, hleast⟩
    refine ⟨out, (sat_leastDefaultGraph_iff M body out e).mpr
      (Or.inl ⟨hout, ?_⟩)⟩
    intro z hlt
    exact hleast z ((sat_ltTermAt_vars_iff M z out e).mp hlt)
  · exact ⟨M.zero, (sat_leastDefaultGraph_iff M body M.zero e).mpr
      (Or.inr ⟨hex, rfl⟩)⟩

theorem leastDefaultGraph_functional_of_pa {alpha : Type u}
    {M : PA.PreModel alpha} (hPA : RawPASatisfies M)
    (body : PA.Formula) (e : Nat → alpha) {x y : alpha}
    (hx : PA.Formula.Sat M (scons x e) (leastDefaultGraph body))
    (hy : PA.Formula.Sat M (scons y e) (leastDefaultGraph body)) :
    x = y := by
  rcases (sat_leastDefaultGraph_iff M body x e).mp hx with
      hxLeast | hxNone
  · rcases (sat_leastDefaultGraph_iff M body y e).mp hy with
        hyLeast | hyNone
    · rcases raw_order_trichotomy hPA x y with hxy | hxy | hyx
      · exact hxy
      · exact False.elim
          (hyLeast.2 x ((sat_ltTermAt_vars_iff M x y e).mpr hxy)
            hxLeast.1)
      · exact False.elim
          (hxLeast.2 y ((sat_ltTermAt_vars_iff M y x e).mpr hyx)
            hyLeast.1)
    · exact False.elim (hyNone.1 ⟨x, hxLeast.1⟩)
  · rcases (sat_leastDefaultGraph_iff M body y e).mp hy with
        hyLeast | hyNone
    · exact False.elim (hxNone.1 ⟨y, hyLeast.1⟩)
    · exact hxNone.2.trans hyNone.2.symm

/-- The abstract selector interface used by the finite Skolem-hull
construction is therefore available in every raw model of first-order PA. -/
theorem canonicalSelectorsOfPA {alpha : Type u} {M : PA.PreModel alpha}
    (hPA : RawPASatisfies M) : CanonicalSelectors M where
  graph_total := leastDefaultGraph_total_of_pa hPA
  graph_functional := leastDefaultGraph_functional_of_pa hPA

/-- Unconditional selector package for the raw PA algebra extracted from an
arbitrary first-order finite-adjunction model. -/
theorem fofamCanonicalSelectors {alpha : Type u}
    (M : AckermannHF.FirstOrderFiniteAdjunctionModel alpha) :
    CanonicalSelectors (AckermannHF.PAInHF.fofamPAPreModel M) :=
  canonicalSelectorsOfPA (fun e f hf =>
    AckermannHF.PAInHF.fofam_PA_Ax_s_valid M f e hf)

end FiniteSkolemCut

end PAFiniteBasisReduction
end LeanProofs
