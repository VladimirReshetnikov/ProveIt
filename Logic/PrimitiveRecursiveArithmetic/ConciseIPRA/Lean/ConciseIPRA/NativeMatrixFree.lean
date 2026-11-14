import ConciseIPRA.NativeReconIntro

/-!
# A calculus whose inferences carry no template and no matrix

`MFPrf` has seven rules: hypothesis, the two computation equations, backward
replacement at sources other than the literal `0` (`bRep`: from `s = t`, `s ≢ 0`, and
`Rep_t^s(u) = r` infer `r = u`), elimination by abstraction (`aqE`: from
`Q_y Rep_t^y(A)` and `Rep_t^0(A)` infer `A`), `DE`, and the reconstructed introduction
(`dIrP`, `dIrC`: the matrix is abstracted from the conclusion of the premise).

No instance of a rule is given a term template or a formula matrix: the equality rule
replaces every occurrence of its target, and the matrices of the elimination and of the
introduction of a closure are computed by abstraction.  The data of an inference are at
most one term (the abstracted term of `aqE`, the witness of the introduction).

`mfprf_iff_nprf`: the calculus derives the same sequents as the kernel.  The bootstrap
is the composition of two generic ones: `BMKernel` gives transport in equation
templates from `bRep`, with `QI` at equations from the introduction in the mode of
progress and the name for zero introduced at a marker; `RKernel` then recovers
transport in formulas, `QE` and the introductions of the kernel.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

variable {n m k : ℕ}

/-- The calculus without templates and matrices. -/
inductive MFPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : MFPrf Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      MFPrf Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      MFPrf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  | bRep {n : ℕ} {Γ : List (NFm n)} {s t u r : Tm n} (hs : s ≠ zero)
      (h₁ : MFPrf Γ (.eq s t)) (h₂ : MFPrf Γ (.eq (Tm.rpl t s Syn.var u) r)) :
      MFPrf Γ (.eq r u)
  | aqE {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (t : Tm n) (h₁ : MFPrf Γ (.Q (NFm.abs t A)))
      (h₂ : MFPrf Γ (NFm.rep t zero A)) : MFPrf Γ A
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : MFPrf Γ (.D B)) (h₂ : MFPrf (.Q B :: Γ.map NFm.shift) A.shift) : MFPrf Γ A
  | dIrP {n : ℕ} {Γ : List (NFm n)} {C : NFm (n + 1)} (a b : Tm (n + 1))
      (hC : NFm.abs (succ (Syn.var 0)) C = (NFm.eq a b).subst skz)
      (h : MFPrf (NFm.eq a b :: Γ.map NFm.shift) C) : MFPrf Γ (.D ((NFm.eq a b).subst skz))
  | dIrC {n : ℕ} {Γ : List (NFm n)} {C : NFm (n + 1)} (B : NFm (n + 2)) (w : Tm n)
      (hm : ¬ ((∃ a b, B = NFm.eq a b) ∧ w = zero))
      (hC : NFm.abs (Syn.shift (Syn.shift w)) (NFm.abs (succ (Syn.var 0)) C) = B.subst tauC)
      (h : MFPrf ((B.subst (up (inst w))).subst (repl zero) :: Γ.map NFm.shift) C) :
      MFPrf Γ (.D B)

variable {Γ : List (NFm n)} {A : NFm n}

/-- **Soundness**: every rule is a rule of `W_rr` or backward replacement. -/
theorem MFPrf.toRR (h : MFPrf Γ A) : RRPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | bRep _ _ _ ih₁ ih₂ =>
    exact rrprf_iff_nprf.2 (NPrf.bRep (rrprf_iff_nprf.1 ih₁) (rrprf_iff_nprf.1 ih₂))
  | aqE t _ _ ih₁ ih₂ => exact .aqE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dIrP a b hC _ ih => exact .dIrP a b hC ih
  | dIrC B w hm hC _ ih => exact .dIrC B w hm hC ih

/-! ### Structural rules -/

namespace MFPrf

theorem hyp0 : MFPrf (A :: Γ) A := .hyp List.mem_cons_self

theorem weaken (h : MFPrf Γ A) : ∀ {Δ : List (NFm n)}, Γ ⊆ Δ → MFPrf Δ A := by
  induction h with
  | hyp h => intro Δ s; exact .hyp (s h)
  | iterZero a h => intro Δ _; exact .iterZero a h
  | iterSucc c a h => intro Δ _; exact .iterSucc c a h
  | bRep hs _ _ ih₁ ih₂ => intro Δ s; exact .bRep hs (ih₁ s) (ih₂ s)
  | aqE t _ _ ih₁ ih₂ => intro Δ s; exact .aqE t (ih₁ s) (ih₂ s)
  | dE _ _ ih₁ ih₂ =>
    intro Δ s
    exact .dE (ih₁ s) (ih₂ (List.cons_subset_cons _ (List.map_subset _ s)))
  | dIrP a b hC _ ih =>
    intro Δ s; exact .dIrP a b hC (ih (List.cons_subset_cons _ (List.map_subset _ s)))
  | dIrC B w hm hC _ ih =>
    intro Δ s; exact .dIrC B w hm hC (ih (List.cons_subset_cons _ (List.map_subset _ s)))

theorem wk {B : NFm n} (h : MFPrf Γ A) : MFPrf (B :: Γ) A :=
  h.weaken (List.subset_cons_self _ _)

theorem ren (h : MFPrf Γ A) : ∀ {m : ℕ} (ξ : Fin n → Fin m), Function.Injective ξ →
    MFPrf (Γ.map fun B => B.subst fun i => (Syn.var (ξ i) : Tm m))
      (A.subst fun i => (Syn.var (ξ i) : Tm m)) := by
  induction h with
  | hyp h => intro m ξ _; exact .hyp (List.mem_map_of_mem h)
  | iterZero a h => intro m ξ _; exact .iterZero _ _
  | iterSucc c a h =>
    intro m ξ _
    simp only [NFm.subst_eq, Tm.subst_iter, Tm.subst_succ, Syn.subst_subst_inst]
    exact .iterSucc _ _ _
  | bRep hs _ _ ih₁ ih₂ =>
    intro m ξ hξ
    have h₂ := ih₂ ξ hξ
    simp only [NFm.subst_eq, Tm.rpl_rn _ _ _ hξ] at h₂
    exact .bRep (Tm.subst_rn_ne_zero hs ξ) (ih₁ ξ hξ) h₂
  | aqE t _ _ ih₁ ih₂ =>
    intro m ξ hξ
    have h₁ := ih₁ ξ hξ
    have h₂ := ih₂ ξ hξ
    simp only [NFm.subst_Q, NFm.abs_rn _ _ hξ] at h₁
    rw [NFm.rep_rn _ _ _ hξ] at h₂
    exact .aqE _ h₁ h₂
  | dE _ _ ih₁ ih₂ =>
    intro m ξ hξ
    have h := ih₂ (Tm.upRen ξ) (Tm.upRen_inj hξ)
    rw [← Tm.up_rn, List.map_cons, NFm.map_shift_subst, NFm.shift_subst_up] at h
    exact .dE (ih₁ ξ hξ) h
  | @dIrP _ Γ C a b hC _ ih =>
    intro m ξ hξ
    have h := ih (Tm.upRen ξ) (Tm.upRen_inj hξ)
    rw [← Tm.up_rn, List.map_cons, NFm.map_shift_subst] at h
    show MFPrf _ (.D (((NFm.eq a b).subst skz).subst (up (up fun i => Syn.var (ξ i)))))
    rw [NFm.skz_rn]
    refine .dIrP _ _ ?_ h
    rw [NFm.abs_succ_rn C hξ, hC, NFm.skz_rn]
    rfl
  | @dIrC _ Γ C B w hm hC _ ih =>
    intro m ξ hξ
    have h := ih (Tm.upRen ξ) (Tm.upRen_inj hξ)
    rw [← Tm.up_rn, List.map_cons, NFm.map_shift_subst, NFm.subst_repl_up, NFm.subst_up_inst]
      at h
    show MFPrf _ (.D (B.subst (up (up fun i => Syn.var (ξ i)))))
    refine MFPrf.dIrC (C := C.subst (up fun i => Syn.var (ξ i))) _
      (Syn.subst (fun i => Syn.var (ξ i)) w) ?_ ?_ ?_
    · rintro ⟨⟨a', b', e⟩, hw⟩
      refine hm ⟨?_, ?_⟩
      · cases B with
        | eq a b => exact ⟨a, b, rfl⟩
        | Q B => cases e
        | D B => cases e
      · by_contra hw'
        exact Tm.subst_rn_ne_zero hw' ξ hw
    · rw [NFm.abs2_rn C w hξ, hC, NFm.tauC_rn]
    · simpa using h

theorem shift (h : MFPrf Γ A) : MFPrf (Γ.map NFm.shift) A.shift :=
  h.ren Fin.succ (Fin.succ_injective _)

theorem cutLift {Δ : List (NFm n)} (h : ∀ B ∈ Γ, MFPrf Δ B) (C : NFm (n + 1)) :
    ∀ B ∈ C :: Γ.map NFm.shift, MFPrf (C :: Δ.map NFm.shift) B := by
  intro B hB
  rcases List.mem_cons.1 hB with rfl | hB
  · exact hyp0
  · obtain ⟨B₀, hB₀, rfl⟩ := List.mem_map.1 hB
    exact (h B₀ hB₀).shift.wk

/-- Cut: hypotheses may be replaced by derivations of them. -/
theorem cut (h : MFPrf Γ A) : ∀ {Δ : List (NFm n)}, (∀ B ∈ Γ, MFPrf Δ B) → MFPrf Δ A := by
  induction h with intro Δ hΔ
  | hyp h => exact hΔ _ h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | bRep hs _ _ ih₁ ih₂ => exact .bRep hs (ih₁ hΔ) (ih₂ hΔ)
  | aqE t _ _ ih₁ ih₂ => exact .aqE t (ih₁ hΔ) (ih₂ hΔ)
  | dE _ _ ih₁ ih₂ => exact .dE (ih₁ hΔ) (ih₂ (cutLift hΔ _))
  | dIrP a b hC _ ih => exact .dIrP a b hC (ih (cutLift hΔ _))
  | dIrC B w hm hC _ ih => exact .dIrC B w hm hC (ih (cutLift hΔ _))

end MFPrf

/-- `QI` at a literal equation with the assumption unused: the introduction in the mode
of progress, opened. -/
theorem MFPrf.qI (a b : Tm (n + 1))
    (h : MFPrf (Γ.map NFm.shift) ((NFm.eq a b).subst (repl (succ (Syn.var 0))))) :
    MFPrf Γ (.Q (.eq a b)) := by
  refine .dE (.dIrP a b (RKernel.NFm.recon_eqP (.eq a b)) h.wk) ?_
  have e : (NFm.eq a b).subst skz = (NFm.eq a b).subst (up fun i => Syn.var i.succ) :=
    NFm.subst_ext _ fun i => by refine Fin.cases ?_ (fun j => ?_) i <;> simp [skz]
  rw [e]
  exact .hyp List.mem_cons_self

instance : BMKernel @MFPrf :=
  ⟨fun h => .hyp h, fun a h => .iterZero a h, fun c a h => .iterSucc c a h,
    fun hs h₁ h₂ => .bRep hs h₁ h₂, fun t h₁ h₂ => .aqE t h₁ h₂, fun h₁ h₂ => .dE h₁ h₂,
    fun a b h => MFPrf.qI a b h, fun h s => h.weaken s, fun h => h.shift⟩

/-- The name for zero, introduced at a marker of its matrix whose value is `0`. -/
theorem MFPrf.dZ (n : ℕ) (Γ : List (NFm n)) : MFPrf Γ (.D (BMKernel.zname (n := n))) := by
  refine .dIrC _ (NFm.markD BMKernel.zname zero) (fun h => by cases h.2)
    (NFm.recon_mark _ _ (NFm.big_markD _ _)) ?_
  generalize hΔ : ((BMKernel.zname (n := n)).subst (up (inst (NFm.markD BMKernel.zname zero)))).subst
    (repl zero) :: Γ.map NFm.shift = Δ
  have k₁ := BMKernel.iterSucc (P := @MFPrf) (Γ := Δ) (Syn.var 0) zero
    (Syn.shift (Syn.shift (NFm.markD (BMKernel.zname (n := n)) zero)))
  have k₂ := BMKernel.iterSucc (P := @MFPrf) (Γ := Δ) (Syn.var 0) zero zero
  have k₃ : MFPrf Δ (.eq (Syn.shift (NFm.markD (BMKernel.zname (n := n)) zero)) zero) := by
    rw [← hΔ]
    exact BMKernel.wk (BMKernel.shift (BMKernel.iterZero (P := @MFPrf) (Γ := Γ) zero
      (Tm.big (NFm.sz (BMKernel.zname (n := n))))))
  simp only [Syn.subst_inst_shift, Tm.subst_zero] at k₁ k₂
  have k := BMKernel.eqTrans k₁ (BMKernel.eqTrans k₃ (BMKernel.eqSymm k₂))
  have u2 : ∀ σ : Fin (n + 2) → Tm (n + 1), Syn.up σ 2 = Syn.shift (σ 1) := fun σ => by
    rw [← Fin.succ_one_eq_two]; exact Syn.up_succ σ 1
  simpa [BMKernel.zname, Syn.subst_up_shift, u2] using k

instance : RKernel @MFPrf :=
  ⟨fun h => .hyp h, fun a h => .iterZero a h, fun c a h => .iterSucc c a h,
    fun a b => BMKernel.trEq MFPrf.dZ a b, fun t h₁ h₂ => .aqE t h₁ h₂,
    fun h₁ h₂ => .dE h₁ h₂, fun a b hC h => .dIrP a b hC h,
    fun B w hm hC h => .dIrC B w hm hC h, fun h s => h.weaken s, fun h => h.shift,
    fun h s => h.cut s⟩

/-- **No templates and no matrices**: the calculus with backward replacement at nonzero
sources, elimination by abstraction and the reconstructed introduction derives the same
sequents as the kernel. -/
theorem mfprf_iff_nprf : MFPrf Γ A ↔ NPrf Γ A :=
  ⟨fun h => rrprf_iff_nprf.1 h.toRR, RKernel.ofNPrf⟩

end LeanProofs.ConciseIPRA
