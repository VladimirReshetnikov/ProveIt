import IPRABridge.OrderSymbols
import IPRADerivations.Core.SearchParameters
import DiophantineConsistency.PRABoundedSearchCode

/-! Compare the existing Foundation search code with the ordinary iPRA
search on the same finite family of parameters. -/

set_option autoImplicit false

namespace IPRABridge

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open scoped Fm
open LeanProofs.ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (pred)
open Syn
open DiophantineConsistency.PRAFiniteFunctionCodes (Code Codes)
open DiophantineConsistency.PRASelectCode (selectCode selectAmong)
open DiophantineConsistency.PRABoundedSearchCode

variable {n k : ℕ} {Γ : List (Fm PTm n)}

private theorem translatedComp {p q : ℕ} (f : Code p) (gs : Codes q p) (xs : Fin q → PTm n) :
    Γ ⊢[PRAAx] translatedApp (.comp f gs) xs ≐
      translatedApp f (fun j => app (toConciseCodes gs j) xs) :=
  PRA.comp (toConciseCode f) (toConciseCodes gs) xs

private theorem translatedZero (xs : Fin k → PTm n) :
    Γ ⊢[PRAAx] translatedApp (.zero k) xs ≐ zero := by
  cases k with
  | zero => exact congrApp .zero (fun i => Fin.elim0 i)
  | succ k => exact zeroK_eq xs

private abbrev selectTerm (test yes no : PTm n) : PTm n :=
  translatedApp selectCode (Fin.cases test ![yes, no])

private theorem selectZero (a b : PTm n) : Γ ⊢[PRAAx] selectTerm zero a b ≐ b := by
  simpa only [selectTerm, translatedApp, selectCode, toConciseCode, Matrix.cons_val_one,
    Matrix.cons_val_zero] using
    (PRA.precZero (Γ := Γ) (.proj (1 : Fin 2)) (.proj (2 : Fin 4)) ![a, b]).eqTrans
      (PRA.proj 1 ![a, b])

private theorem selectSucc (d a b : PTm n) : Γ ⊢[PRAAx] selectTerm (succ d) a b ≐ a := by
  let base : PR 2 := .proj 1
  let step : PR 4 := .proj 2
  let args : Fin 4 → PTm n := Fin.cases d (Fin.cases (app (.prec base step) (Fin.cases d ![a, b])) ![a, b])
  exact (PRA.precSucc base step d ![a, b]).eqTrans (PRA.proj 2 args)

/-- The Foundation symbol with its original bound and parameter order. -/
abbrev translatedSearch (good : Code (k + 1)) (N : PTm n) (xs : Fin k → PTm n) : PTm n :=
  translatedApp (searchCode good) (Fin.cases N xs)

private abbrev testAt (good : Code (k + 1)) (i : PTm n) (xs : Fin k → PTm n) : PTm n :=
  translatedApp good (Fin.cases i xs)

private theorem previousTest (good : Code (k + 1)) (N r : PTm n) (xs : Fin k → PTm n) :
    Γ ⊢[PRAAx] translatedApp (goodAtPrevious good) (Fin.cases N (Fin.cases r xs)) ≐ testAt good r xs := by
  let args : Fin (k + 2) → PTm n := Fin.cases N (Fin.cases r xs)
  unfold goodAtPrevious
  refine (translatedComp _ _ args).eqTrans (congrApp (toConciseCode good) ?_)
  intro j
  cases j using Fin.cases with
  | zero => exact PRA.proj 1 args
  | succ j =>
    simp only [toConciseCodes, Fin.cases_succ, toConciseCodes_pack, toConciseCode, args]
    exact PRA.proj j.succ.succ args

private theorem advanceCounter (N r : PTm n) (xs : Fin k → PTm n) :
    Γ ⊢[PRAAx] translatedApp nextCounter (Fin.cases N (Fin.cases r xs)) ≐ succ N := by
  let args : Fin (k + 2) → PTm n := Fin.cases N (Fin.cases r xs)
  unfold nextCounter
  refine (translatedComp _ _ args).eqTrans (congrApp .succ ?_)
  intro j
  fin_cases j
  exact PRA.proj 0 args

theorem translatedSearch_zero (good : Code (k + 1)) (xs : Fin k → PTm n) :
    Γ ⊢[PRAAx] translatedSearch good zero xs ≐ zero :=
  (PRA.precZero (toConciseCode (.zero k)) (toConciseCode (searchStep good)) xs).eqTrans
    (translatedZero xs)

private theorem translatedSearch_succ (good : Code (k + 1)) (N : PTm n) (xs : Fin k → PTm n) :
    let r := translatedSearch good N xs
    Γ ⊢[PRAAx] translatedSearch good (succ N) xs ≐ selectTerm (testAt good r xs) (succ N) r := by
  dsimp only
  let r := translatedSearch good N xs
  let args : Fin (k + 2) → PTm n := Fin.cases N (Fin.cases r xs)
  have h := PRA.precSucc (Γ := Γ) (toConciseCode (.zero k)) (toConciseCode (searchStep good)) N xs
  change Γ ⊢[PRAAx] translatedSearch good (succ N) xs ≐ translatedApp (searchStep good) args at h
  refine h.eqTrans ((translatedComp selectCode _ args).eqTrans (congrApp (toConciseCode selectCode) ?_))
  intro j
  fin_cases j
  · exact previousTest good N r xs
  · exact advanceCounter N r xs
  · exact PRA.proj 1 args

/-- The original predicate code as an ordinary iPRA search body. -/
def translatedSearchBody (good : Code (k + 1)) : PTm (k + 1) :=
  translatedApp good var

@[simp] theorem translatedSearchBody_apply (good : Code (k + 1)) (i : PTm n)
    (xs : Fin k → PTm n) :
    Search.Finite.applyBody (translatedSearchBody good) i xs = translatedApp good (Fin.cases i xs) := by
  simp [Search.Finite.applyBody, translatedSearchBody, translatedApp, PTm.subst_app]

private theorem testCongr (good : Code (k + 1)) (xs : Fin k → PTm n) {a b : PTm n}
    (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] testAt good a xs ≐ testAt good b xs := by
  apply congrApp
  intro i
  cases i using Fin.cases with
  | zero => exact h
  | succ i => exact .eqRefl _

private theorem selectTestCongr {a b yes no : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    Γ ⊢[PRAAx] selectTerm a yes no ≐ selectTerm b yes no := by
  apply congrApp
  intro i
  fin_cases i
  · exact h
  · exact .eqRefl _
  · exact .eqRefl _

private theorem signCongr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] sg a ≐ sg b :=
  congrMonus (.eqRefl _) (congrMonus (.eqRefl _) h)

private theorem searchStep_agrees (good : Code (k + 1)) (N : PTm n) (xs : Fin k → PTm n)
    (h : Γ ⊢[PRAAx] translatedSearch good N xs ≐ Search.Finite.mu (translatedSearchBody good) N xs) :
    Γ ⊢[PRAAx] translatedSearch good (succ N) xs ≐
      Search.Finite.mu (translatedSearchBody good) (succ N) xs := by
  let F := translatedSearch good N xs
  let μ := Search.Finite.mu (translatedSearchBody good) N xs
  have leftStep := translatedSearch_succ (Γ := Γ) good N xs
  have rightStep := Search.Finite.mu_succ (Γ := Γ) (translatedSearchBody good) N xs
  rw [translatedSearchBody_apply] at rightStep
  have spec := Search.Finite.search_spec (Γ := Γ) (translatedSearchBody good) N N xs
  rw [translatedSearchBody_apply] at spec
  refine .orE (lt_or_eq_of_le (Prf.andE₁ spec)) ?_ ?_
  · have hlt : (lt μ N :: Γ) ⊢[PRAAx] lt μ N := Prf.hyp0
    have hn : (lt μ N :: Γ) ⊢[PRAAx] neg (μ ≐ N) :=
      .impI (lt_irrefl N _ (lt_congr Prf.hyp0 (.eqRefl _) Prf.hyp1))
    have testZero : (lt μ N :: Γ) ⊢[PRAAx] testAt good F xs ≐ zero :=
      (testCongr good xs h.wk).eqTrans (.impE (Prf.andE₁ (Prf.andE₂ spec)).wk hlt)
    have left := leftStep.wk.eqTrans ((selectTestCongr testZero).eqTrans (selectZero _ _))
    have right := rightStep.wk.eqTrans ((congrAdd (.eqRefl _)
      ((congrMul (eqb_of_ne hn) (.eqRefl _)).eqTrans (zero_mul _))).eqTrans (add_zero _))
    exact left.eqTrans (h.wk.eqTrans right.eqSymm)
  · have heq : ((μ ≐ N) :: Γ) ⊢[PRAAx] μ ≐ N := Prf.hyp0
    have testEq := testCongr good xs (h.wk.eqTrans heq)
    let x := testAt good N xs
    refine .orE (zero_or_succ x) ?_ ?_
    · have hz : ((x ≐ zero) :: (μ ≐ N) :: Γ) ⊢[PRAAx] x ≐ zero := Prf.hyp0
      have testZero := testEq.wk.eqTrans hz
      have left := leftStep.wk.wk.eqTrans ((selectTestCongr testZero).eqTrans (selectZero _ _))
      have s := (signCongr hz).eqTrans sg_zero
      have right := rightStep.wk.wk.eqTrans ((congrAdd (.eqRefl _)
        ((congrMul (.eqRefl _) s).eqTrans (mul_zero _))).eqTrans (add_zero _))
      exact left.eqTrans (h.wk.wk.eqTrans right.eqSymm)
    · have hs : ((x ≐ succ (pred x)) :: (μ ≐ N) :: Γ) ⊢[PRAAx] x ≐ succ (pred x) := Prf.hyp0
      have testSucc := testEq.wk.eqTrans hs
      have left := leftStep.wk.wk.eqTrans ((selectTestCongr testSucc).eqTrans (selectSucc _ _ _))
      have s := (signCongr hs).eqTrans (sg_succ _)
      have right := rightStep.wk.wk.eqTrans
        ((congrAdd heq.wk ((congrMul (eqb_of_eq heq.wk) s).eqTrans (one_mul _))).eqTrans
          (succ_eq_add_one N).eqSymm)
      exact left.eqTrans right.eqSymm

private theorem subst_translatedSearch {m : ℕ} (σ : Fin n → PTm m) (good : Code (k + 1))
    (N : PTm n) (xs : Fin k → PTm n) :
    Syn.subst σ (translatedSearch good N xs) =
      translatedSearch good (Syn.subst σ N) (fun i => Syn.subst σ (xs i)) := by
  change app _ _ = app _ _
  congr 1
  funext i
  cases i using Fin.cases <;> rfl

private theorem searchAgrees_variables (good : Code (k + 1)) :
    ([] : List (Fm PTm (k + 1))) ⊢[PRAAx]
      translatedSearch good (var 0) (fun j => var j.succ) ≐
        Search.Finite.mu (translatedSearchBody good) (var 0) (fun j => var j.succ) := by
  let p : Fm PTm (k + 1) := translatedSearch good (var 0) (fun j => var j.succ) ≐
    Search.Finite.mu (translatedSearchBody good) (var 0) (fun j => var j.succ)
  refine ind p trivial ?_ ?_
  · simp only [p, Fm.subst_eq, subst_translatedSearch, Search.Finite.subst_mu, Syn.subst_var,
      Syn.inst_zero, Syn.inst_succ]
    exact (translatedSearch_zero good var).eqTrans (Search.Finite.mu_zero (translatedSearchBody good) var).eqSymm
  · simp only [p, Fm.subst_eq, subst_translatedSearch, Search.Finite.subst_mu, Syn.subst_var,
      Syn.repl_zero, Syn.repl_succ]
    exact searchStep_agrees good (var 0) (fun j => var j.succ) Prf.hyp0

/-- The two search codes give equal results at arbitrary object-language
terms, including zero bounds and failed searches. -/
theorem translatedSearch_eq (good : Code (k + 1)) (N : PTm n) (xs : Fin k → PTm n) :
    Γ ⊢[PRAAx] translatedSearch good N xs ≐ Search.Finite.mu (translatedSearchBody good) N xs := by
  have proof := inst (Γ := Γ) (searchAgrees_variables good) (Fin.cases N xs)
  simpa only [Fm.subst_eq, subst_translatedSearch, Search.Finite.subst_mu, Syn.subst_var,
    Fin.cases_zero, Fin.cases_succ] using proof

/-- A witness below the bound forces the original Foundation search code
to return a witness below the same bound. -/
theorem translatedSearch_found {good : Code (k + 1)} {N i : PTm n} {xs : Fin k → PTm n}
    (hf : Γ ⊢[PRAAx] translatedApp good (Fin.cases i xs) ≐ zero) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] lt (translatedSearch good N xs) N ⋏
      (translatedApp good (Fin.cases (translatedSearch good N xs) xs) ≐ zero) := by
  have hbody : Γ ⊢[PRAAx] Search.Finite.applyBody (translatedSearchBody good) i xs ≐ zero := by
    rwa [translatedSearchBody_apply]
  have result := Search.Finite.search_found hbody hi
  rw [translatedSearchBody_apply] at result
  have comparison := translatedSearch_eq (Γ := Γ) good N xs
  exact .andI (lt_congr comparison.eqSymm (.eqRefl _) (.andE₁ result))
    ((testCongr good xs comparison).eqTrans (.andE₁ (.andE₂ result)))

end IPRABridge
