import IPRADerivations.Core.Header

/-!
# Existence and uniqueness of an observed relation

Packet: `foundations/scope_ipra_framework_2026-11-16_2`, Theorem `thm:observed-relation` ("Existence and
uniqueness of an observed relation"): for an observer term `O(c)` put `Out(o) :⟺ ∃ c (V(c) ∧ o = O(c))`.
From a producer `Γ ⊢ ∃ c V(c)` and observer coherence `V(c), V(d), Γ^{↑↑} ⊢ O(c) = O(d)`, iPRA proves
(i) `∃ o Out(o)` and (ii) `Out(o) ∧ Out(o′) → o = o′`.

Variables: in `V` and `O` (context `n + 1`) the certificate is `var 0`. In `Out` (context `n + 1`) the output
is `var 0`; inside its existential the certificate is `var 0` and the output `var 1`. Instances at a
parameter substitution `ρ` (for the `n` context variables) and a term `a` use `Fin.cons a ρ`.

* `Out`: the observed relation;
* `out_exists` (i): the producer's certificate `c` gives the witness `O(c)`, and `c` itself witnesses
  `Out(O(c))`; both local variables are sealed by existential elimination;
* `Coherent`: observer coherence as a rule at arbitrary contexts and parameter instances;
* `out_unique` (ii): `Out(a)` and `Out(b)` give `a = b`: the two hidden certificates are opened and
  coherence identifies their observations.
-/

namespace LeanProofs.IPRA.Foundations.ObservedRelation

open_ipra exports

variable {n : ℕ}

/-- Moving the context of a certificate formula past one new output variable (`0 ↦ 0`, `j + 1 ↦ j + 2`). -/
def σ₁ : Fin (n + 1) → PTm (n + 2) := Fin.cons (Syn.var 0) (fun j => Syn.var j.succ.succ)

/-- `Out(o) = ∃ c (V(c) ∧ o = O(c))`, output `var 0`. -/
def Out (V : Fm PTm (n + 1)) (O : PTm (n + 1)) : Fm PTm (n + 1) :=
  Fm.ex (V.subst σ₁ ⋏ (Syn.var 1 ≐ Syn.subst σ₁ O))

/-! ## Substitution bookkeeping -/

theorem sigma_up {m : ℕ} (a : PTm m) (ρ : Fin n → PTm m) :
    (fun i => Syn.subst (Syn.up (Fin.cons a ρ)) (σ₁ i)) =
      (Fin.cons (Syn.var 0) (fun j => Syn.shift (ρ j)) : Fin (n + 1) → PTm (m + 1)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [σ₁, Syn.shift]

theorem var1_up {m : ℕ} (a : PTm m) (ρ : Fin n → PTm m) :
    Syn.subst (Syn.up (Fin.cons a ρ)) (Syn.var 1 : PTm (n + 2)) = Syn.shift a := by
  simp [Syn.shift]

theorem out_inst {m : ℕ} (V : Fm PTm (n + 1)) (O : PTm (n + 1)) (a : PTm m) (ρ : Fin n → PTm m) :
    (Out V O).subst (Fin.cons a ρ) =
      Fm.ex (V.subst (Fin.cons (Syn.var 0) (fun j => Syn.shift (ρ j))) ⋏
        (Syn.shift a ≐ Syn.subst (Fin.cons (Syn.var 0) (fun j => Syn.shift (ρ j))) O)) := by
  simp only [Out, Fm.subst_ex, Fm.subst_and, Fm.subst_eq, Fm.subst_subst, Syn.subst_subst, sigma_up, var1_up]

theorem cons_shift {m : ℕ} (a : PTm m) (ρ : Fin n → PTm m) :
    (fun i => Syn.shift ((Fin.cons a ρ : Fin (n + 1) → PTm m) i)) =
      (Fin.cons (Syn.shift a) (fun j => Syn.shift (ρ j)) : Fin (n + 1) → PTm (m + 1)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem cons_up_shift {m : ℕ} (ρ : Fin n → PTm m) :
    (fun i => Syn.subst (Syn.up (fun k => Syn.var k.succ))
        ((Fin.cons (Syn.var 0) (fun j => Syn.shift (ρ j)) : Fin (n + 1) → PTm (m + 1)) i)) =
      (Fin.cons (Syn.var 0) (fun j => Syn.shift (Syn.shift (ρ j))) : Fin (n + 1) → PTm (m + 2)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp [Syn.shift, Syn.subst_subst]

theorem up_shift_shift {m : ℕ} (b : PTm m) :
    Syn.subst (Syn.up (fun k => (Syn.var k.succ : PTm (m + 1)))) (Syn.shift b) = Syn.shift (Syn.shift b) := by
  simp [Syn.shift, Syn.subst_subst]

theorem shift_var0 {m : ℕ} : Syn.shift (Syn.var 0 : PTm (m + 1)) = Syn.var 1 := by
  simp [Syn.shift]

/-! ## Existence -/

/-- (i): `∃ o Out(o)`. -/
theorem out_exists {Γ : List (Fm PTm n)} {V : Fm PTm (n + 1)} {O : PTm (n + 1)} (h : Γ ⊢[PRAAx] Fm.ex V) :
    Γ ⊢[PRAAx] Fm.ex (Out V O) := by
  refine .exE h ?_
  rw [Fm.shift, Fm.subst_ex]
  refine .exI O ?_
  have e : (fun i => Syn.subst (Syn.inst O) (Syn.up (fun j => (Syn.var j.succ : PTm (n + 1))) i)) =
      (Fin.cons O (fun j => Syn.var j.succ) : Fin (n + 1) → PTm (n + 1)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [Fm.subst_subst, e, out_inst]
  refine .exI (Syn.var 0) ?_
  simp only [Fm.subst_and, Fm.subst_eq, Fm.subst_subst, Syn.subst_subst]
  have eV : (fun i => Syn.subst (Syn.inst (Syn.var 0 : PTm (n + 1)))
      ((Fin.cons (Syn.var 0) (fun j => Syn.shift (Syn.var j.succ : PTm (n + 1))) :
        Fin (n + 1) → PTm (n + 2)) i)) = (Syn.var : Fin (n + 1) → PTm (n + 1)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [Syn.shift]
  rw [eV, Fm.subst_id, Syn.subst_id]
  simp only [Syn.subst_inst_shift]
  exact .andI Prf.hyp0 (.eqRefl O)

/-! ## Uniqueness -/

/-- Observer coherence `V(c), V(d) ⊢ O(c) = O(d)`, as a rule at arbitrary contexts and parameters. -/
def Coherent (V : Fm PTm (n + 1)) (O : PTm (n + 1)) : Prop :=
  ∀ {m : ℕ} {Δ : List (Fm PTm m)} (ρ : Fin n → PTm m) (c d : PTm m),
    (Δ ⊢[PRAAx] V.subst (Fin.cons c ρ)) → (Δ ⊢[PRAAx] V.subst (Fin.cons d ρ)) →
      (Δ ⊢[PRAAx] Syn.subst (Fin.cons c ρ) O ≐ Syn.subst (Fin.cons d ρ) O)

/-- (ii): `Out(a)` and `Out(b)` give `a = b`. -/
theorem out_unique {V : Fm PTm (n + 1)} {O : PTm (n + 1)} (H : Coherent V O) {m : ℕ}
    {Δ : List (Fm PTm m)} {ρ : Fin n → PTm m} {a b : PTm m}
    (ha : Δ ⊢[PRAAx] (Out V O).subst (Fin.cons a ρ)) (hb : Δ ⊢[PRAAx] (Out V O).subst (Fin.cons b ρ)) :
    Δ ⊢[PRAAx] a ≐ b := by
  rw [out_inst] at ha hb
  refine .exE ha ?_
  have hb' := hb.shift
  rw [Fm.shift, Fm.subst_ex] at hb'
  refine .exE hb'.wk ?_
  let τ : Fin (n + 1) → PTm (m + 1) := Fin.cons (Syn.var 0) (fun j => Syn.shift (ρ j))
  let Ba : Fm PTm (m + 1) := V.subst τ ⋏ (Syn.shift a ≐ Syn.subst τ O)
  let Bb : Fm PTm (m + 1) := V.subst τ ⋏ (Syn.shift b ≐ Syn.subst τ O)
  let Δ₂ : List (Fm PTm (m + 2)) := Bb.subst (Syn.up (fun i => Syn.var i.succ)) :: (Ba :: Δ.map Fm.shift).map Fm.shift
  have hA : Δ₂ ⊢[PRAAx] (V.subst τ).shift ⋏ (Syn.shift (Syn.shift a) ≐ Syn.shift (Syn.subst τ O)) := Prf.hyp1
  have hB : Δ₂ ⊢[PRAAx] (V.subst τ).subst (Syn.up (fun i => Syn.var i.succ)) ⋏
      (Syn.subst (Syn.up (fun i => Syn.var i.succ)) (Syn.shift b) ≐
        Syn.subst (Syn.up (fun i => Syn.var i.succ)) (Syn.subst τ O)) := Prf.hyp0
  rw [Fm.shift_subst, cons_shift, Syn.shift_subst, cons_shift, shift_var0] at hA
  rw [Fm.subst_subst, cons_up_shift, Syn.subst_subst, cons_up_shift, up_shift_shift] at hB
  have coh := H (fun j => Syn.shift (Syn.shift (ρ j))) (Syn.var 1) (Syn.var 0) (.andE₁ hA) (.andE₁ hB)
  exact (Prf.andE₂ hA).eqTrans (coh.eqTrans (Prf.andE₂ hB).eqSymm)

end LeanProofs.IPRA.Foundations.ObservedRelation
