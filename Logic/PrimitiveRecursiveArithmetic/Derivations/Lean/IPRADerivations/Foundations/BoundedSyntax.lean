import IPRADerivations.Foundations.BooleanizationCorollaries

/-!
# Arity-indexed bounded syntax and its checked Boolean compiler

Source: FIBER `thm:boolean-reflection`, including its proposed `BFm n` frontend.
Unlike the packed backend syntax, the atoms here are terms in the original
variables and bounded binders extend that variable context. `formula` is the
literal first-order interpretation. `compile` translates it into the existing
packed backend; `compile_correct` proves the translation by object derivations,
including the pairing equations at every binder. No formula-equivalence premise
is required from a client.

The effective construction is external recursion on one fixed finite formula.
It introduces no internal universal evaluator and uses the backend's checked
quantifier-free fold/search proofs for bounded quantifiers.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Foundations.BoundedSyntax

open_ipra exports

/-- Bounded formulas with their actual free-variable arity. -/
inductive BFm : ℕ → Type
  | eq {n : ℕ} (s t : PTm n) : BFm n
  | and {n : ℕ} (A B : BFm n) : BFm n
  | or {n : ℕ} (A B : BFm n) : BFm n
  | imp {n : ℕ} (A B : BFm n) : BFm n
  | not {n : ℕ} (A : BFm n) : BFm n
  | all {n : ℕ} (bound : PTm n) (A : BFm (n + 1)) : BFm n
  | ex {n : ℕ} (bound : PTm n) (A : BFm (n + 1)) : BFm n

/-- Order atoms use the literal monus definition of object order. -/
def BFm.le {n : ℕ} (s t : PTm n) : BFm n := .eq (monus s t) zero
def BFm.lt {n : ℕ} (s t : PTm n) : BFm n := .le (succ s) t

/-- The source formula, before any packing or compilation. -/
def formula : {n : ℕ} → BFm n → Fm PTm n
  | _, .eq s t => s ≐ t
  | _, .and A B => formula A ⋏ formula B
  | _, .or A B => formula A ⋎ formula B
  | _, .imp A B => formula A ⟶ formula B
  | _, .not A => neg (formula A)
  | _, .all b A => Fm.all (lt (var 0) (Syn.shift b) ⟶ formula A)
  | _, .ex b A => Fm.ex (lt (var 0) (Syn.shift b) ⋏ formula A)

/-- Capture-avoiding substitution in the original arity-indexed syntax. -/
def BFm.subst : {n m : ℕ} → BFm n → (Fin n → PTm m) → BFm m
  | _, _, .eq s t, σ => .eq (Syn.subst σ s) (Syn.subst σ t)
  | _, _, .and A B, σ => .and (A.subst σ) (B.subst σ)
  | _, _, .or A B, σ => .or (A.subst σ) (B.subst σ)
  | _, _, .imp A B, σ => .imp (A.subst σ) (B.subst σ)
  | _, _, .not A, σ => .not (A.subst σ)
  | _, _, .all b A, σ => .all (Syn.subst σ b) (A.subst (Syn.up σ))
  | _, _, .ex b A, σ => .ex (Syn.subst σ b) (A.subst (Syn.up σ))

theorem formula_subst {n m : ℕ} (A : BFm n) (σ : Fin n → PTm m) :
    formula (A.subst σ) = (formula A).subst σ := by
  induction A generalizing m with
  | eq s t => rfl
  | and A B ihA ihB => simp only [BFm.subst, formula, Fm.subst_and, ihA, ihB]
  | or A B ihA ihB => simp only [BFm.subst, formula, Fm.subst_or, ihA, ihB]
  | imp A B ihA ihB => simp only [BFm.subst, formula, Fm.subst_imp, ihA, ihB]
  | not A ih => simp only [BFm.subst, formula, subst_neg, ih]
  | all b A ih =>
    simp only [BFm.subst, formula, Fm.subst_all, Fm.subst_imp, subst_lt,
      Syn.subst_var, Syn.up_zero, BoundedFormulas.subst_up_shift', ih]
  | ex b A ih =>
    simp only [BFm.subst, formula, Fm.subst_ex, Fm.subst_and, subst_lt,
      Syn.subst_var, Syn.up_zero, BoundedFormulas.subst_up_shift', ih]

/-- A tuple always has an explicit zero tail, including the empty tuple. -/
def pack {m : ℕ} : {n : ℕ} → (Fin n → PTm m) → PTm m
  | 0, _ => zero
  | n + 1, xs => pairT (xs 0) (pack (fun i : Fin n => xs i.succ))

/-- Projection terms for the tuple representation. -/
def projections : (n : ℕ) → Fin n → PTm 1
  | 0, i => Fin.elim0 i
  | n + 1, i => Fin.cases (fstT (var 0))
      (fun j => Syn.subst ![sndT (var 0)] (projections n j)) i

/-- Extend an embedding at a binder: the fresh variable is the first projection. -/
def extend {n : ℕ} (ρ : Fin n → PTm 1) : Fin (n + 1) → PTm 1 :=
  Fin.cases (fstT (var 0)) (fun i => Syn.subst ![sndT (var 0)] (ρ i))

/-- Translation to the packed backend at an explicitly supplied embedding. -/
def compile : {n : ℕ} → BFm n → (Fin n → PTm 1) → BoundedFormulas.BF
  | _, .eq s t, ρ => .eq (Syn.subst ρ s) (Syn.subst ρ t)
  | _, .and A C, ρ => .and (compile A ρ) (compile C ρ)
  | _, .or A C, ρ => .or (compile A ρ) (compile C ρ)
  | _, .imp A C, ρ => BooleanizationCorollaries.imp (compile A ρ) (compile C ρ)
  | _, .not A, ρ => .not (compile A ρ)
  | _, .all b A, ρ => .all (Syn.subst ρ b) (compile A (extend ρ))
  | _, .ex b A, ρ => .ex (Syn.subst ρ b) (compile A (extend ρ))

variable {n m k : ℕ} {Γ : List (Fm PTm m)}

@[simp] theorem subst_pack (σ : Fin m → PTm k) (xs : Fin n → PTm m) :
    Syn.subst σ (pack xs) = pack (fun i => Syn.subst σ (xs i)) := by
  induction n with
  | zero => exact ConciseIPRA.PTm.subst_zero _
  | succ n ih => simp only [pack, subst_pairT, ih]

theorem at_subst (t : PTm n) (ρ : Fin n → PTm 1) (y : PTm m) :
    BoundedFormulas.at1 (Syn.subst ρ t) y = Syn.subst (fun i => BoundedFormulas.at1 (ρ i) y) t := by
  exact Syn.subst_subst _ _ _

theorem projections_pack (xs : Fin n → PTm m) (i : Fin n) :
    Γ ⊢[PRAAx] BoundedFormulas.at1 (projections n i) (pack xs) ≐ xs i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero => simpa only [projections, Fin.cases_zero, BoundedFormulas.at1, subst_fstT,
        Syn.subst_var, Matrix.cons_val_zero, pack] using fst_pair (xs 0) (pack (fun j => xs j.succ))
    | succ i =>
      have h := Prf.eqCongr (Γ := Γ) (projections n i)
        (σ := fun _ => sndT (pack xs)) (σ' := ![pack (fun j => xs j.succ)])
        (fun j => by fin_cases j; exact snd_pair _ _)
      have e : Γ ⊢[PRAAx] BoundedFormulas.at1 (projections (n + 1) i.succ) (pack xs) ≐
          BoundedFormulas.at1 (projections n i) (pack (fun j => xs j.succ)) := by
        simpa [projections, BoundedFormulas.at1, Syn.subst_subst] using h
      exact e.eqTrans (ih (fun j => xs j.succ) i)

private theorem iff_and {a b c d : Fm PTm m}
    (h : Γ ⊢[PRAAx] Fm.iff a b) (j : Γ ⊢[PRAAx] Fm.iff c d) :
    Γ ⊢[PRAAx] Fm.iff (a ⋏ c) (b ⋏ d) :=
  .iffI (.impI (.andI (.iffMp h.wk (.andE₁ Prf.hyp0)) (.iffMp j.wk (.andE₂ Prf.hyp0))))
    (.impI (.andI (.iffMpr h.wk (.andE₁ Prf.hyp0)) (.iffMpr j.wk (.andE₂ Prf.hyp0))))

private theorem iff_or {a b c d : Fm PTm m}
    (h : Γ ⊢[PRAAx] Fm.iff a b) (j : Γ ⊢[PRAAx] Fm.iff c d) :
    Γ ⊢[PRAAx] Fm.iff (a ⋎ c) (b ⋎ d) :=
  .iffI (.impI (.orE Prf.hyp0 (.orI₁ (.iffMp h.wk.wk Prf.hyp0))
      (.orI₂ (.iffMp j.wk.wk Prf.hyp0))))
    (.impI (.orE Prf.hyp0 (.orI₁ (.iffMpr h.wk.wk Prf.hyp0))
      (.orI₂ (.iffMpr j.wk.wk Prf.hyp0))))

private theorem iff_imp {a b c d : Fm PTm m}
    (h : Γ ⊢[PRAAx] Fm.iff a b) (j : Γ ⊢[PRAAx] Fm.iff c d) :
    Γ ⊢[PRAAx] Fm.iff (a ⟶ c) (b ⟶ d) :=
  .iffI (.impI (.impI (.iffMp j.wk.wk (.impE Prf.hyp1 (.iffMpr h.wk.wk Prf.hyp0)))))
    (.impI (.impI (.iffMpr j.wk.wk (.impE Prf.hyp1 (.iffMp h.wk.wk Prf.hyp0)))))

private theorem iff_all {a b : Fm PTm (m + 1)}
    (h : Γ.map Fm.shift ⊢[PRAAx] Fm.iff a b) :
    Γ ⊢[PRAAx] Fm.iff (Fm.all a) (Fm.all b) := by
  refine .iffI (.impI (.allI ?_)) (.impI (.allI ?_))
  · exact .iffMp h.wk (Prf.hyp0 (Γ := Γ) (φ := Fm.all a)).allOpen
  · exact .iffMpr h.wk (Prf.hyp0 (Γ := Γ) (φ := Fm.all b)).allOpen

private theorem iff_ex {a b : Fm PTm (m + 1)}
    (h : Γ.map Fm.shift ⊢[PRAAx] Fm.iff a b) :
    Γ ⊢[PRAAx] Fm.iff (Fm.ex a) (Fm.ex b) := by
  refine .iffI (.impI (.exE Prf.hyp0 ?_)) (.impI (.exE Prf.hyp0 ?_))
  · have hb : (a :: (Fm.ex a).shift :: Γ.map Fm.shift) ⊢[PRAAx] b :=
      Prf.iffMp h.wk.wk Prf.hyp0
    exact .exI (var 0) (by simpa only [Fm.shift, Fm.subst_ex,
      Fm.subst_up_succ_inst, List.map_cons] using hb)
  · have ha : (b :: (Fm.ex b).shift :: Γ.map Fm.shift) ⊢[PRAAx] a :=
      Prf.iffMpr h.wk.wk Prf.hyp0
    exact .exI (var 0) (by simpa only [Fm.shift, Fm.subst_ex,
      Fm.subst_up_succ_inst, List.map_cons] using ha)

private theorem formula_congr (φ : Fm PTm n) {σ τ : Fin n → PTm m}
    (h : ∀ i, Γ ⊢[PRAAx] σ i ≐ τ i) :
    Γ ⊢[PRAAx] Fm.iff (φ.subst σ) (φ.subst τ) :=
  .iffI (.impI (.eqSubst φ σ τ (fun i => (h i).wk) Prf.hyp0))
    (.impI (.eqSubst φ τ σ (fun i => (h i).eqSymm.wk) Prf.hyp0))

private theorem extend_correct (ρ : Fin n → PTm 1) (y : PTm m)
    (σ : Fin n → PTm m) (h : ∀ i, Γ ⊢[PRAAx] BoundedFormulas.at1 (ρ i) y ≐ σ i)
    (i : Fin (n + 1)) :
    Γ.map Fm.shift ⊢[PRAAx]
      BoundedFormulas.at1 (extend ρ i) (pairT (var 0) (Syn.shift y)) ≐ Syn.up σ i := by
  cases i using Fin.cases with
  | zero => simpa only [extend, Fin.cases_zero, BoundedFormulas.at1, subst_fstT,
      Syn.subst_var, Matrix.cons_val_zero, Syn.up_zero] using fst_pair (var 0) (Syn.shift y)
  | succ i =>
    have e := Prf.eqCongr (Γ := Γ.map Fm.shift) (ρ i) (σ := fun _ => sndT (pairT (var 0) (Syn.shift y)))
      (σ' := ![Syn.shift y]) (fun j => by fin_cases j; exact snd_pair _ _)
    have hs := (h i).shift
    simp only [Fm.shift, Fm.subst_eq, BoundedFormulas.at1_subst] at hs
    have ee : Γ.map Fm.shift ⊢[PRAAx]
        BoundedFormulas.at1 (extend ρ i.succ) (pairT (var 0) (Syn.shift y)) ≐
          BoundedFormulas.at1 (ρ i) (Syn.shift y) := by
      simpa [extend, BoundedFormulas.at1, Syn.subst_subst] using e
    exact ee.eqTrans hs

/-- Translation correctness for any embedding whose decoded variables agree
with the original substitution. The agreement itself is a proved object fact. -/
theorem compile_correct (A : BFm n) : ∀ {m : ℕ} {Γ : List (Fm PTm m)}
    (ρ : Fin n → PTm 1) (y : PTm m) (σ : Fin n → PTm m),
    (∀ i, Γ ⊢[PRAAx] BoundedFormulas.at1 (ρ i) y ≐ σ i) →
    (Γ ⊢[PRAAx] Fm.iff (BoundedFormulas.fmAt (compile A ρ) m y) ((formula A).subst σ)) := by
  induction A with
  | eq s t =>
    intro m Γ ρ y σ h
    simpa only [compile, BoundedFormulas.fmAt, at_subst, formula, Fm.subst_eq] using formula_congr (s ≐ t) h
  | and A C ihA ihC =>
    intro m Γ ρ y σ h
    exact iff_and (ihA ρ y σ h) (ihC ρ y σ h)
  | or A C ihA ihC =>
    intro m Γ ρ y σ h
    exact iff_or (ihA ρ y σ h) (ihC ρ y σ h)
  | imp A C ihA ihC =>
    intro m Γ ρ y σ h
    exact (BooleanizationCorollaries.imp_iff (compile A ρ) (compile C ρ) y).iffTrans
      (iff_imp (ihA ρ y σ h) (ihC ρ y σ h))
  | not A ih =>
    intro m Γ ρ y σ h
    exact iff_imp (ih ρ y σ h) (Prf.iffRefl Fm.bot)
  | @all n b A ih =>
    intro m Γ ρ y σ h
    have he := extend_correct ρ y σ h
    have body := ih (extend ρ) (pairT (var 0) (Syn.shift y)) (Syn.up σ) he
    have hb' := LeanProofs.IPRA.Order.shift_eq (Prf.eqCongr b h)
    have hbound : Γ.map Fm.shift ⊢[PRAAx]
        Syn.shift (BoundedFormulas.at1 (Syn.subst ρ b) y) ≐ Syn.shift (Syn.subst σ b) := by
      simpa only [at_subst, Syn.shift] using hb'
    have hlt : Γ.map Fm.shift ⊢[PRAAx]
        Fm.iff (lt (var 0) (Syn.shift (BoundedFormulas.at1 (Syn.subst ρ b) y)))
          (lt (var 0) (Syn.shift (Syn.subst σ b))) :=
      .iffI (.impI (lt_congr (.eqRefl _) hbound.wk Prf.hyp0))
        (.impI (lt_congr (.eqRefl _) hbound.eqSymm.wk Prf.hyp0))
    simpa only [compile, BoundedFormulas.fmAt, formula, Fm.subst_all, Fm.subst_imp,
      subst_lt, Syn.subst_var, Syn.up_zero, BoundedFormulas.subst_up_shift' ] using iff_all (iff_imp hlt body)
  | @ex n b A ih =>
    intro m Γ ρ y σ h
    have he := extend_correct ρ y σ h
    have body := ih (extend ρ) (pairT (var 0) (Syn.shift y)) (Syn.up σ) he
    have hb' := LeanProofs.IPRA.Order.shift_eq (Prf.eqCongr b h)
    have hbound : Γ.map Fm.shift ⊢[PRAAx]
        Syn.shift (BoundedFormulas.at1 (Syn.subst ρ b) y) ≐ Syn.shift (Syn.subst σ b) := by
      simpa only [at_subst, Syn.shift] using hb'
    have hlt : Γ.map Fm.shift ⊢[PRAAx]
        Fm.iff (lt (var 0) (Syn.shift (BoundedFormulas.at1 (Syn.subst ρ b) y)))
          (lt (var 0) (Syn.shift (Syn.subst σ b))) :=
      .iffI (.impI (lt_congr (.eqRefl _) hbound.wk Prf.hyp0))
        (.impI (lt_congr (.eqRefl _) hbound.eqSymm.wk Prf.hyp0))
    simpa only [compile, BoundedFormulas.fmAt, formula, Fm.subst_ex, Fm.subst_and,
      subst_lt, Syn.subst_var, Syn.up_zero, BoundedFormulas.subst_up_shift' ] using iff_ex (iff_and hlt body)

/-- The actual PR term computed by the frontend at any original terms. -/
def bit (A : BFm n) (xs : Fin n → PTm m) : PTm m :=
  BoundedFormulas.bitAt (compile A (projections n)) m (pack xs)

/-- The actual n-ary primitive-recursive symbol for a fixed source formula. -/
def bitF (A : BFm n) : PR n := PTm.toPR (bit A var)

theorem bit_subst (A : BFm n) (xs : Fin n → PTm m) (σ : Fin m → PTm k) :
    Syn.subst σ (bit A xs) = bit A (fun i => Syn.subst σ (xs i)) := by
  simp only [bit, BoundedFormulas.bitAt_subst, subst_pack]

/-- Reflection states the original source formula, with its original variables. -/
theorem bounded_reflection (A : BFm n) (xs : Fin n → PTm m) :
    Γ ⊢[PRAAx] Fm.iff (bit A xs ≐ one) ((formula A).subst xs) :=
  (BooleanizationCorollaries.bit_one_iff _ _).iffTrans
    (compile_correct A (projections n) (pack xs) xs (projections_pack xs))

theorem bit_cases (A : BFm n) (xs : Fin n → PTm m) :
    Γ ⊢[PRAAx] (bit A xs ≐ zero) ⋎ (bit A xs ≐ one) := BoundedFormulas.bf_cases _ _

theorem bit_zero_iff (A : BFm n) (xs : Fin n → PTm m) :
    Γ ⊢[PRAAx] Fm.iff (bit A xs ≐ zero) (neg ((formula A).subst xs)) :=
  (BooleanizationCorollaries.bit_zero_iff _ _).iffTrans
    (iff_imp (compile_correct A (projections n) (pack xs) xs (projections_pack xs))
      (Prf.iffRefl Fm.bot))

theorem bounded_decidable (A : BFm n) (xs : Fin n → PTm m) :
    Γ ⊢[PRAAx] ((formula A).subst xs) ⋎ neg ((formula A).subst xs) :=
  .orE (bit_cases A xs) (.orI₂ (.iffMp (bit_zero_iff A xs) Prf.hyp0))
    (.orI₁ (.iffMp (bounded_reflection A xs) Prf.hyp0))

theorem program_correct (A : BFm n) (xs : Fin n → PTm m) :
    Γ ⊢[PRAAx] app (bitF A) xs ≐ bit A xs := by
  have e := toPR_eq (bit A var) xs (Γ := Γ)
  simpa only [bitF, bit_subst, Syn.subst_var] using e

theorem boolean_reflection_closed (A : BFm n) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx]
      univ n (Fm.iff (app (bitF A) var ≐ one) (formula A)) := by
  apply closeUniv n
  have h := bounded_reflection (Γ := ([] : List (Fm PTm n))) A var
  rw [Fm.subst_id] at h
  have e : ([] : List (Fm PTm n)) ⊢[PRAAx]
      Fm.iff (app (bitF A) var ≐ one) (bit A var ≐ one) := by
    simpa using formula_congr (Γ := ([] : List (Fm PTm n))) (var 0 ≐ (one : PTm 1))
      (σ := ![app (bitF A) var]) (τ := ![bit A var])
      (fun i => by fin_cases i; exact program_correct A var)
  exact e.iffTrans h

/-- The generated symbol also has a closed object-level Boolean contract. -/
theorem boolean_program_closed (A : BFm n) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx]
      univ n ((app (bitF A) var ≐ zero) ⋎ (app (bitF A) var ≐ one)) := by
  apply closeUniv n
  have c := bit_cases (Γ := ([] : List (Fm PTm n))) A var
  have h := formula_congr (Γ := ([] : List (Fm PTm n)))
    ((var 0 ≐ (zero : PTm 1)) ⋎ (var 0 ≐ one))
    (σ := ![bit A var]) (τ := ![app (bitF A) var])
    (fun i => by fin_cases i; exact (program_correct A var).eqSymm)
  simpa using h.iffMp (by simpa using c)

#print axioms formula_subst
#print axioms projections_pack
#print axioms compile_correct
#print axioms bounded_reflection
#print axioms bit_zero_iff
#print axioms bounded_decidable
#print axioms program_correct
#print axioms boolean_reflection_closed
#print axioms boolean_program_closed

end LeanProofs.IPRA.Foundations.BoundedSyntax

