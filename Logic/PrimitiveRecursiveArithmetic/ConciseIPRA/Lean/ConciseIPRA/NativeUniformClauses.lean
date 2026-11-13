import ConciseIPRA.NativeClausal

/-!
# Four rule families and one reflexivity clause

`VPrf` is the calculus of the package `Research/uniform_clauses`.  A clause
has at most one antecedent: `[; y.B(y)]`, read `∀ y, B(y)`, or `[A; y.B(y)]`,
read `A → ∀ y, B(y)`.  An ordinary assumption `A` is the unconditional clause
`[; v.A]`.  Reflexivity is not a rule: every context contains the fixed clause

  `R = [; y. y = y]`,

and `t = t` is a use of it.  There are four rule families:

* **Use**: from the antecedents of a clause of the context, of which there are
  none or one, infer an instance of its consequent;
* **Eval**, in its two cases;
* **Elim** and **Intro**, as in `NativeClausal`.

`vprf_iff_cprf` proves that with the clause `R` in the context `VPrf` derives
what the five-rule clause calculus `CPrf` derives, and
`vprf_iff_nprf_of_qfree` that on `Q`-free sequents it derives exactly what the
kernel derives.  Both translations are inductions that carry an invariant on
the contexts; no structural rule of `VPrf` is used.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

variable {n m : ℕ}

/-- A clause with at most one antecedent. -/
structure UCl (n : ℕ) where
  /-- The antecedent, if there is one. -/
  ante : Option (NFm n)
  /-- The consequent, with one more variable. -/
  cons : NFm (n + 1)

namespace UCl

def shift (c : UCl n) : UCl (n + 1) :=
  ⟨c.ante.map NFm.shift, c.cons.subst (up fun i => Syn.var i.succ)⟩

/-- The fixed reflexivity clause `[; y. y = y]`. -/
def refl : UCl n := ⟨none, .eq (Syn.var 0) (Syn.var 0)⟩

/-- An ordinary assumption, as the unconditional clause `[; v.A]`. -/
def asm (A : NFm n) : UCl n := ⟨none, A.shift⟩

/-- The clause with an antecedent that it stands for: `0 = 0` when it has none. -/
def toCl (c : UCl n) : Cl n := ⟨c.ante.getD (.eq zero zero), c.cons⟩

/-- A clause with an antecedent, as a uniform clause. -/
def ofCl (c : Cl n) : UCl n := ⟨some c.ante, c.cons⟩

theorem refl_shift : (refl : UCl n).shift = refl := rfl

theorem toCl_shift (c : UCl n) : c.shift.toCl = c.toCl.shift := by
  obtain ⟨a, b⟩ := c
  cases a <;> rfl

end UCl

/-- Derivability with uniform clause use and no reflexivity rule. -/
inductive VPrf : {n : ℕ} → List (UCl n) → NFm n → Prop
  /-- Use: from the antecedents of a clause, none or one, infer an instance of
  its consequent. -/
  | use {n : ℕ} {Γ : List (UCl n)} {c : UCl n} (t : Tm n) (hc : c ∈ Γ)
      (h : ∀ A, c.ante = some A → VPrf Γ A) : VPrf Γ (c.cons.subst (inst t))
  | evalZero {n : ℕ} {Γ : List (UCl n)} (h : Tm (n + 1)) {a t r : Tm n}
      (h₁ : VPrf Γ (.eq a t)) (h₂ : VPrf Γ (.eq (iter zero a h) r)) : VPrf Γ (.eq r t)
  | evalSucc {n : ℕ} {Γ : List (UCl n)} {c a : Tm n} {h : Tm (n + 1)} {t r : Tm n}
      (h₁ : VPrf Γ (.eq (iter c a h) t)) (h₂ : VPrf Γ (.eq (iter (succ c) a h) r)) :
      VPrf Γ (.eq r (Syn.subst (inst t) h))
  | elim {n : ℕ} {Γ : List (UCl n)} {B : NFm (n + 2)} {A : NFm n} (h₁ : VPrf Γ (.D B))
      (h₂ : VPrf (⟨some (B.subst (inst zero)), B⟩ :: Γ.map UCl.shift) A.shift) : VPrf Γ A
  | intro {n : ℕ} {Γ : List (UCl n)} (B : NFm (n + 2)) (t : Tm n) (hB : B.QFree)
      (h : VPrf (UCl.asm ((B.subst (up (inst t))).subst (repl (NFm.start B t)))
          :: Γ.map UCl.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      VPrf Γ (.D B)

/-- The invariant of the translation into the five-rule calculus, under one
more variable and one more clause. -/
theorem UCl.liftToCl {Δ : List (UCl n)} {Γ : List (Cl n)}
    (s : ∀ c ∈ Δ, c = UCl.refl ∨ c.toCl ∈ Γ) (d : UCl (n + 1)) :
    ∀ c ∈ d :: Δ.map UCl.shift, c = UCl.refl ∨ c.toCl ∈ d.toCl :: Γ.map Cl.shift := by
  intro c hc
  rcases List.mem_cons.1 hc with rfl | hc
  · exact .inr List.mem_cons_self
  · obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    rcases s c₀ hc₀ with rfl | h
    · exact .inl UCl.refl_shift
    · exact .inr (List.mem_cons_of_mem _ (by
        rw [UCl.toCl_shift]; exact List.mem_map_of_mem h))

/-- Every derivation with uniform clauses is a derivation of the five-rule
calculus, a use of the reflexivity clause being the reflexivity rule. -/
theorem VPrf.toCPrf {Δ : List (UCl n)} {A : NFm n} (h : VPrf Δ A) :
    ∀ {Γ : List (Cl n)}, (∀ c ∈ Δ, c = UCl.refl ∨ c.toCl ∈ Γ) → CPrf Γ A := by
  induction h with intro Γ s
  | @use _ Δ c t hc _ ih =>
    rcases s c hc with rfl | hm
    · exact .refl t
    · obtain ⟨a, b⟩ := c
      cases a with
      | none => exact .use (c := ⟨.eq zero zero, b⟩) t hm (.refl zero)
      | some A => exact .use (c := ⟨A, b⟩) t hm (ih A rfl s)
  | evalZero h _ _ ih₁ ih₂ => exact .evalZero h (ih₁ s) (ih₂ s)
  | evalSucc _ _ ih₁ ih₂ => exact .evalSucc (ih₁ s) (ih₂ s)
  | elim _ _ ih₁ ih₂ => exact .elim (ih₁ s) (ih₂ (UCl.liftToCl s _))
  | intro B t hB _ ih => exact .intro B t hB (ih (UCl.liftToCl s _))

/-- The invariant of the converse translation, under one more variable and one
more clause. -/
theorem UCl.liftOfCl {Γ : List (Cl n)} {Δ : List (UCl n)}
    (s : ∀ c ∈ Γ, ∃ d ∈ Δ, d.cons = c.cons ∧ ∀ A, d.ante = some A → A = c.ante)
    (c' : Cl (n + 1)) (d' : UCl (n + 1)) (hcons : d'.cons = c'.cons)
    (hante : ∀ A, d'.ante = some A → A = c'.ante) :
    ∀ c ∈ c' :: Γ.map Cl.shift,
      ∃ d ∈ d' :: Δ.map UCl.shift, d.cons = c.cons ∧ ∀ A, d.ante = some A → A = c.ante := by
  intro c hc
  rcases List.mem_cons.1 hc with rfl | hc
  · exact ⟨d', List.mem_cons_self, hcons, hante⟩
  · obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    obtain ⟨d, hd, hdc, hda⟩ := s c₀ hc₀
    refine ⟨d.shift, List.mem_cons_of_mem _ (List.mem_map_of_mem hd), ?_, ?_⟩
    · show d.cons.subst _ = c₀.cons.subst _
      rw [hdc]
    · intro A hA
      obtain ⟨A₀, hA₀, rfl⟩ := Option.map_eq_some_iff.1 hA
      show A₀.shift = c₀.ante.shift
      rw [hda A₀ hA₀]

/-- Every derivation of the five-rule calculus is a derivation with uniform
clauses, once the reflexivity clause is in the context. -/
theorem CPrf.toVPrf {Γ : List (Cl n)} {A : NFm n} (h : CPrf Γ A) :
    ∀ {Δ : List (UCl n)}, UCl.refl ∈ Δ →
      (∀ c ∈ Γ, ∃ d ∈ Δ, d.cons = c.cons ∧ ∀ A, d.ante = some A → A = c.ante) → VPrf Δ A := by
  induction h with
  | refl t =>
    intro Δ hr _
    exact VPrf.use (c := UCl.refl) t hr (fun A hA => by cases hA)
  | evalZero h _ _ ih₁ ih₂ => intro Δ hr s; exact .evalZero h (ih₁ hr s) (ih₂ hr s)
  | evalSucc _ _ ih₁ ih₂ => intro Δ hr s; exact .evalSucc (ih₁ hr s) (ih₂ hr s)
  | @use _ Γ c t hc _ ih =>
    intro Δ hr s
    obtain ⟨d, hd, hdc, hda⟩ := s c hc
    rw [← hdc]
    exact .use t hd (fun A hA => by rw [hda A hA]; exact ih hr s)
  | elim _ _ ih₁ ih₂ =>
    intro Δ hr s
    refine .elim (ih₁ hr s) (ih₂ (List.mem_cons_of_mem _ ?_) (UCl.liftOfCl s _ _ rfl ?_))
    · rw [← UCl.refl_shift]; exact List.mem_map_of_mem hr
    · intro A hA; exact (Option.some.inj hA).symm
  | intro B t hB _ ih =>
    intro Δ hr s
    refine .intro B t hB (ih (List.mem_cons_of_mem _ ?_) (UCl.liftOfCl s _ _ rfl ?_))
    · rw [← UCl.refl_shift]; exact List.mem_map_of_mem hr
    · intro A hA; cases hA

variable {Γ : List (NFm n)} {A : NFm n}

/-- **Uniform clause use and the five-rule clause calculus.**  With the
reflexivity clause in the context they derive the same formulas from the same
assumptions. -/
theorem vprf_iff_cprf :
    VPrf (UCl.refl :: Γ.map UCl.asm) A ↔ CPrf (Γ.map Cl.asm) A := by
  constructor
  · intro h
    refine h.toCPrf fun c hc => ?_
    rcases List.mem_cons.1 hc with rfl | hc
    · exact .inl rfl
    · obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hc
      exact .inr (List.mem_map_of_mem (f := Cl.asm) hX)
  · intro h
    refine h.toVPrf List.mem_cons_self fun c hc => ?_
    obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hc
    exact ⟨UCl.asm X, List.mem_cons_of_mem _ (List.mem_map_of_mem hX), rfl,
      fun A hA => by cases hA⟩

/-- On `Q`-free sequents the calculus with uniform clauses derives exactly what
the kernel derives. -/
theorem vprf_iff_nprf_of_qfree (hΓ : ∀ X ∈ Γ, X.QFree) (hA : A.QFree) :
    VPrf (UCl.refl :: Γ.map UCl.asm) A ↔ NPrf Γ A :=
  vprf_iff_cprf.trans (cprf_iff_nprf_of_qfree hΓ hA)

end LeanProofs.ConciseIPRA
