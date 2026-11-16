import IPRABridge.Syntax
import IPRABridge.ConciseToFoundationLogic

/-! Object-level extensional equality of a Foundation code and its round trip
through ConciseIPRA. All proofs use the equality-only reference theory. -/

set_option autoImplicit false
noncomputable section

namespace IPRABridge

open LO LO.FirstOrder LO.Entailment LO.Entailment.FiniteContext
open scoped LO.FirstOrder
open DiophantineConsistency.PRAFiniteFunctionCodes (Code Codes pack)
open DiophantineConsistency.PRATheory (getCode)
open DiophantineConsistency.IPRAEqualityOnlyReference
open DiophantineConsistency.IPRAReferenceEqualityTools (eqAt)
open DiophantineConsistency.IPRATheoryHilbertBridge (extended)
open DiophantineConsistency.IPRATheoryInstantiation (instantiateTheory)
open ConciseToFoundationLogic (atEnv atEnv_subst atEnv_specialize atEnv_lift liftEnv eqReflAt replaceEnv)

local instance codeNormalizationLanguageDecidableEq : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (EqualityRel k); infer_instance

local notation "Λ" => extended referenceTheory
local notation "T" => Term language ℕ

private theorem atEnv_eq {n : ℕ} (v : Fin n → T) (t u : TermN n) :
    atEnv v (.rel EqualityRel.eq ![t, u]) = eqAt (Rew.embSubsts v t) (Rew.embSubsts v u) := by
  rw [atEnv, Semiformulaᵢ.rew_rel, eqAt]
  congr 1
  exact funext (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))

private theorem rew_cases {n m : ℕ} {ξ ζ : Type} (R : Rew language ξ n ζ m)
    {k : ℕ} (t : Semiterm language ξ n) (us : Fin k → Semiterm language ξ n) :
    (fun i => R (Fin.cases t us i)) = Fin.cases (R t) (fun i => R (us i)) :=
  funext (Fin.cases rfl (fun _ => rfl))

/-- Symmetry of reference equality in any finite context. -/
theorem referenceEqSymm {Γ : List (Propositionᵢ language)} {a b : T}
    (h : Γ ⊢[Λ] eqAt a b) : Γ ⊢[Λ] eqAt b a := by
  let p : Semisentenceᵢ language 2 := .rel EqualityRel.eq ![#0, #1]
  have hEq (i : Fin 2) : Γ ⊢[Λ] eqAt (![a, a] i) (![b, a] i) := by
    refine Fin.cases h (fun j => ?_) i
    exact Fin.cases ⟨of (eqReflAt a)⟩ (fun i => Fin.elim0 i) j
  have hBody : Γ ⊢[Λ] atEnv ![a, a] p := by
    dsimp only [p]
    rw [atEnv_eq]
    exact ⟨of (eqReflAt a)⟩
  have h' := replaceEnv p ![a, a] ![b, a] hEq hBody
  dsimp only [p] at h'
  rw [atEnv_eq] at h'
  exact h'

/-- Transitivity of reference equality in any finite context. -/
theorem referenceEqTrans {Γ : List (Propositionᵢ language)} {a b c : T}
    (hab : Γ ⊢[Λ] eqAt a b) (hbc : Γ ⊢[Λ] eqAt b c) : Γ ⊢[Λ] eqAt a c := by
  let p : Semisentenceᵢ language 2 := .rel EqualityRel.eq ![#0, #1]
  have hEq (i : Fin 2) : Γ ⊢[Λ] eqAt (![a, b] i) (![a, c] i) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨of (eqReflAt a)⟩
    · exact Fin.cases hbc (fun i => Fin.elim0 i) j
  have hBody : Γ ⊢[Λ] atEnv ![a, b] p := by
    dsimp only [p]
    rw [atEnv_eq]
    exact hab
  have h' := replaceEnv p ![a, b] ![a, c] hEq hBody
  dsimp only [p] at h'
  rw [atEnv_eq] at h'
  exact h'

/-- A reference function application respects pointwise provable equality of
its arguments in any finite context. -/
theorem referenceFuncCongr {Γ : List (Propositionᵢ language)} {n : ℕ} (c : Code n)
    (xs ys : Fin n → T) (h : ∀ i, Γ ⊢[Λ] eqAt (xs i) (ys i)) :
    Γ ⊢[Λ] eqAt (.func c xs) (.func c ys) := by
  let t : T := .func c xs
  let p : Semisentenceᵢ language (n + 1) :=
    .rel EqualityRel.eq ![#0, .func c (fun i => #i.succ)]
  have hEq (i : Fin (n + 1)) :
      Γ ⊢[Λ] eqAt (Fin.cases t xs i) (Fin.cases t ys i) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨of (eqReflAt t)⟩
    · simpa only [Fin.cases_succ] using h j
  have hEnv (v : Fin n → T) :
      atEnv (Fin.cases t v) p = eqAt t (.func c v) := by
    dsimp only [p]
    rw [atEnv_eq, Rew.func']
    simp only [Rew.embSubsts_bvar, Fin.cases_zero, Fin.cases_succ]
  have hBody : Γ ⊢[Λ] atEnv (Fin.cases t xs) p := by
    rw [hEnv]
    exact ⟨of (eqReflAt t)⟩
  simpa only [hEnv] using replaceEnv p (Fin.cases t xs) (Fin.cases t ys) hEq hBody


private theorem rew_zero {n m : ℕ} {ξ ζ : Type} (R : Rew language ξ n ζ m) :
    R (.func (.zero 0) Fin.elim0) = .func (.zero 0) Fin.elim0 := by
  rw [Rew.func']
  congr 1
  exact funext (fun i => Fin.elim0 i)

private def instantiateEquality {n : ℕ} (t u : TermN n)
    (h : referenceTheory ⊢! equalClosure t u) (v : Fin n → T) :
    Λ ⊢! eqAt (Rew.embSubsts v t) (Rew.embSubsts v u) := by
  rw [← atEnv_eq]
  exact instantiateTheory _ h v

private def zeroAt {n : ℕ} (v : Fin n → T) :
    Λ ⊢! eqAt (.func (.zero n) v) (.func (.zero 0) Fin.elim0) := by
  have h := instantiateEquality (applyCode (.zero n) (vars n)) (applyCode (.zero 0) Fin.elim0)
    (Axiomatized.prfAxm (ReferenceAxiom.defining (.zero n))) v
  simp only [applyCode] at h
  simpa only [vars, ↓rew_zero, Rew.func', Rew.embSubsts_bvar] using h

private def compAt {n m : ℕ} (f : Code m) (g : Codes n m) (v : Fin n → T) :
    Λ ⊢! eqAt (.func (.comp f g) v) (.func f (fun i => .func (getCode g i) v)) := by
  have h := instantiateEquality (applyCode (.comp f g) (vars n))
    (applyCode f (fun i => applyCode (getCode g i) (vars n)))
    (Axiomatized.prfAxm (ReferenceAxiom.defining (.composition f g))) v
  simpa only [applyCode, vars, Rew.func', Rew.embSubsts_bvar] using h

private def precBaseAt {n : ℕ} (f : Code n) (g : Code (n + 2)) (v : Fin n → T) :
    Λ ⊢! eqAt (.func (.prec f g) (Fin.cases (.func (.zero 0) Fin.elim0) v)) (.func f v) := by
  let lhs : TermN n := applyCode (.prec f g) (Fin.cases (applyCode (.zero 0) Fin.elim0) (vars n))
  let rhs : TermN n := applyCode f (vars n)
  have ha : referenceTheory ⊢! recursionBaseEquation f g :=
    Axiomatized.prfAxm (ReferenceAxiom.defining (.recursionBase f g))
  have h := instantiateEquality lhs rhs ha v
  simp only [lhs, rhs, applyCode] at h
  simpa only [vars, ↓rew_zero, Rew.func', rew_cases, Rew.embSubsts_bvar] using h

private def precStepAt {n : ℕ} (f : Code n) (g : Code (n + 2)) (x : T) (v : Fin n → T) :
    Λ ⊢! eqAt (.func (.prec f g) (Fin.cases (.func .succ (fun _ => x)) v))
      (.func g (Fin.cases x (Fin.cases (.func (.prec f g) (Fin.cases x v)) v))) := by
  let params : Fin n → TermN (n + 1) := fun i => #i.succ
  let previous := applyCode (.prec f g) (Fin.cases #0 params)
  let lhs : TermN (n + 1) := applyCode (.prec f g) (Fin.cases (applyCode .succ (fun _ => #0)) params)
  let rhs : TermN (n + 1) := applyCode g (Fin.cases #0 (Fin.cases previous params))
  have ha : referenceTheory ⊢! recursionStepEquation f g :=
    Axiomatized.prfAxm (ReferenceAxiom.defining (.recursionStep f g))
  have h := instantiateEquality lhs rhs ha (Fin.cases x v)
  simpa only [lhs, rhs, applyCode, previous, params, Rew.func', rew_cases, Rew.embSubsts_bvar,
    Fin.cases_zero, Fin.cases_succ] using h


private theorem env_atZero {n : ℕ} (v : Fin n → T) (φ : Semisentenceᵢ language (n + 1)) :
    atEnv v (atZero φ) = atEnv (Fin.cases (.func (.zero 0) Fin.elim0) v) φ := by
  rw [atZero, atEnv_subst]
  congr 1
  exact funext (Fin.cases (rew_zero _) (fun i => Rew.embSubsts_bvar v i))

private theorem env_atSucc {n : ℕ} (v : Fin n → T) (x : T)
    (φ : Semisentenceᵢ language (n + 1)) :
    atEnv (Fin.cases x v) (atSucc φ) = atEnv (Fin.cases (.func .succ (fun _ => x)) v) φ := by
  rw [atSucc, atEnv_subst]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cases_zero, applyCode, Rew.func', Rew.embSubsts_bvar]
  · simp only [Fin.cases_succ, Rew.embSubsts_bvar]

private def referenceInductionAt {n : ℕ} (φ : Semisentenceᵢ language (n + 1))
    (hφ : DiophantineConsistency.IPRAQuantifierFree.OpenI φ) (v : Fin n → T) (x : T)
    (hbase : Λ ⊢! atEnv (Fin.cases (.func (.zero 0) Fin.elim0) v) φ)
    (hstep : [atEnv (liftEnv v) φ] ⊢[Λ]!
      atEnv (Fin.cases (.func .succ (fun _ => &0)) (fun i => Rew.shift (v i))) φ) :
    Λ ⊢! atEnv (Fin.cases x v) φ := by
  have hstep' : Λ ⊢! atEnv v (∀⁰ (φ 🡒 atSucc φ)) := by
    change Λ ⊢! ∀⁰ ((Rew.embSubsts v).q ▹ (φ 🡒 atSucc φ))
    apply HilbertProofᵢ.gen
    rw [atEnv_lift]
    change Λ ⊢! atEnv (liftEnv v) φ 🡒 atEnv (liftEnv v) (atSucc φ)
    have heq := env_atSucc (fun i => Rew.shift (v i)) (&0) φ
    change atEnv (liftEnv v) (atSucc φ) = _ at heq
    rw [heq]
    exact emptyPrf (deduct hstep)
  have hi : referenceTheory ⊢! inductionAxiom φ :=
    Axiomatized.prfAxm (ReferenceAxiom.induction φ hφ)
  have hind := instantiateTheory (atZero φ 🡒 (∀⁰ (φ 🡒 atSucc φ)) 🡒 ∀⁰ φ) hi v
  have hbase' : Λ ⊢! atEnv v (atZero φ) := by
    rwa [env_atZero]
  have hall : Λ ⊢! ∀⁰ ((Rew.embSubsts v).q ▹ φ) := hind ⨀ hbase' ⨀ hstep'
  rw [← atEnv_specialize]
  exact HilbertProofᵢ.all₁ _ x ⨀ hall


private def precExt {n : ℕ} (f f' : Code n) (g g' : Code (n + 2))
    (hf : ∀ args, Λ ⊢! eqAt (.func f args) (.func f' args))
    (hg : ∀ args, Λ ⊢! eqAt (.func g args) (.func g' args))
    (x : T) (v : Fin n → T) :
    Λ ⊢! eqAt (.func (.prec f g) (Fin.cases x v)) (.func (.prec f' g') (Fin.cases x v)) := by
  let φ : Semisentenceᵢ language (n + 1) := .rel EqualityRel.eq
    ![applyCode (.prec f g) (vars (n + 1)), applyCode (.prec f' g') (vars (n + 1))]
  have hAt (w : Fin (n + 1) → T) :
      atEnv w φ = eqAt (.func (.prec f g) w) (.func (.prec f' g') w) := by
    dsimp only [φ]
    rw [atEnv_eq]
    simp only [applyCode, vars, Rew.func', Rew.embSubsts_bvar]
  rw [← hAt]
  apply referenceInductionAt φ (show DiophantineConsistency.IPRAQuantifierFree.OpenI φ from trivial)
  · rw [hAt]
    exact (referenceEqTrans ⟨of (precBaseAt f g v)⟩
      (referenceEqTrans ⟨of (hf v)⟩ (referenceEqSymm ⟨of (precBaseAt f' g' v)⟩))).some
      |> emptyPrf
  · rw [hAt, hAt]
    let t : T := &0
    let args : Fin n → T := fun i => Rew.shift (v i)
    let a : T := .func (.prec f g) (Fin.cases t args)
    let b : T := .func (.prec f' g') (Fin.cases t args)
    let xs : Fin (n + 2) → T := Fin.cases t (Fin.cases a args)
    let ys : Fin (n + 2) → T := Fin.cases t (Fin.cases b args)
    have he : [eqAt a b] ⊢[Λ] eqAt a b := ⟨byAxm₀⟩
    have hc : [eqAt a b] ⊢[Λ] eqAt (.func g' xs) (.func g' ys) := by
      apply referenceFuncCongr
      intro i
      cases i using Fin.cases with
      | zero => exact ⟨of (eqReflAt t)⟩
      | succ j =>
        cases j using Fin.cases with
        | zero => exact he
        | succ k =>
          simp only [xs, ys, Fin.cases_succ]
          exact ⟨of (eqReflAt (args k))⟩
    exact (referenceEqTrans ⟨of (precStepAt f g t args)⟩
      (referenceEqTrans ⟨of (hg xs)⟩ (referenceEqTrans hc
        (referenceEqSymm ⟨of (precStepAt f' g' t args)⟩)))).some


private def eqTransAt {a b c : T} (ab : Λ ⊢! eqAt a b) (bc : Λ ⊢! eqAt b c) :
    Λ ⊢! eqAt a c :=
  emptyPrf (referenceEqTrans ⟨of ab⟩ ⟨of bc⟩ : [] ⊢[Λ] eqAt a c).some

private def eqSymmAt {a b : T} (ab : Λ ⊢! eqAt a b) : Λ ⊢! eqAt b a :=
  emptyPrf (referenceEqSymm ⟨of ab⟩ : [] ⊢[Λ] eqAt b a).some

private def normalizeComp_eq {n m : ℕ} (f : Code m) (g : Codes n m)
    (hf : ∀ args, Λ ⊢! eqAt (.func f args) (.func (normalizeCode f) args))
    (hg : ∀ (v : Fin n → T) (i : Fin m), Λ ⊢!
      eqAt (.func (getCode g i) v) (.func (toFoundationCode (toConciseCodes g i)) v))
    (v : Fin n → T) :
    Λ ⊢! eqAt (.func (.comp f g) v) (.func (normalizeCode (.comp f g)) v) := by
  let g' := pack m (fun i => toFoundationCode (toConciseCodes g i))
  let oldArgs : Fin m → T := fun i => .func (getCode g i) v
  let newArgs : Fin m → T := fun i => .func (getCode g' i) v
  have hc : Λ ⊢! eqAt (.func (normalizeCode f) oldArgs) (.func (normalizeCode f) newArgs) := by
    apply emptyPrf
    refine (referenceFuncCongr (Γ := []) (normalizeCode f) oldArgs newArgs ?_).some
    intro i
    simpa only [oldArgs, newArgs, g', getCode_pack] using
      (show [] ⊢[Λ] eqAt (.func (getCode g i) v) (.func (toFoundationCode (toConciseCodes g i)) v)
        from ⟨of (hg v i)⟩)
  change Λ ⊢! eqAt (.func (.comp f g) v) (.func (.comp (normalizeCode f) g') v)
  exact eqTransAt (compAt f g v)
    (eqTransAt (hf oldArgs) (eqTransAt hc (eqSymmAt (compAt (normalizeCode f) g' v))))

/-- Every Foundation code and its normalized code are provably equal at
arbitrary terms in the reference theory. -/
def normalizeCode_eq {n : ℕ} (c : Code n) (args : Fin n → T) :
    Λ ⊢! eqAt (.func c args) (.func (normalizeCode c) args) := by
  refine Code.rec (motive_1 := fun n c =>
      ∀ v : Fin n → T, Λ ⊢! eqAt (.func c v) (.func (normalizeCode c) v))
    (motive_2 := fun n m g => ∀ (v : Fin n → T) (i : Fin m),
      Λ ⊢! eqAt (.func (getCode g i) v) (.func (toFoundationCode (toConciseCodes g i)) v))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ c args
  · intro k v
    cases k with
    | zero => exact eqReflAt _
    | succ k =>
      change Λ ⊢! eqAt (.func (.zero (k + 1)) v) (.func (.comp (.zero 0) (.nil (k + 1))) v)
      have h := compAt (.zero 0) (.nil (k + 1)) v
      have hArgs : (fun i : Fin 0 => (.func (getCode (.nil (k + 1)) i) v : T)) = Fin.elim0 :=
        funext (fun i => Fin.elim0 i)
      rw [hArgs] at h
      exact eqTransAt (zeroAt v) (eqSymmAt h)
  · intro v
    exact eqReflAt _
  · intro k i v
    exact eqReflAt _
  · exact fun f g hf hg v => normalizeComp_eq f g hf hg v
  · intro k f g hf hg v
    have hv : Fin.cases (v 0) (fun i : Fin k => v i.succ) = v :=
      funext (Fin.cases rfl (fun _ => rfl))
    rw [← hv]
    exact precExt f (normalizeCode f) g (normalizeCode g) hf hg (v 0) (fun i => v i.succ)
  · intro _ _ i
    exact Fin.elim0 i
  · intro n m f fs hf hfs v i
    cases i using Fin.cases with
    | zero => exact hf v
    | succ j =>
      simpa only [getCode, toConciseCodes, Fin.cases_succ] using hfs v j

end IPRABridge
