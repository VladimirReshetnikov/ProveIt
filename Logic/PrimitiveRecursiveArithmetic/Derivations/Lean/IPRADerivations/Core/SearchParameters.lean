import IPRADerivations.Core.Search

/-! Bounded search for a body with any finite family of parameters, using
the ordinary search invariant at a single packed parameter. -/

set_option autoImplicit false

namespace LeanProofs.IPRA.Search.Finite

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA.Signum (sg)
open Syn
open scoped Fm
open LeanProofs.ConciseIPRA.PTm (zero succ)

variable {n k : ℕ} {Γ : List (Fm PTm n)}

private def pack : {k : ℕ} → (Fin k → PTm n) → PTm n
  | 0, _ => zero
  | 1, xs => xs 0
  | k + 2, xs => pairT (xs 0) (pack (fun i : Fin (k + 1) => xs i.succ))

private def unpack : (k : ℕ) → PTm n → Fin k → PTm n
  | 0, _, i => Fin.elim0 i
  | 1, x, _ => x
  | k + 2, x, i => Fin.cases (fstT x) (unpack (k + 1) (sndT x)) i

private theorem unpackCongr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) (i : Fin k) :
    Γ ⊢[PRAAx] unpack k a i ≐ unpack k b i := by
  induction k generalizing a b with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    cases k with
    | zero => exact h
    | succ k =>
      cases i using Fin.cases with
      | zero => exact congrFst h
      | succ i => exact ih (congrSnd h) i

private theorem unpackPack (xs : Fin k → PTm n) (i : Fin k) :
    Γ ⊢[PRAAx] unpack k (pack xs) i ≐ xs i := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    cases k with
    | zero =>
      fin_cases i
      exact .eqRefl _
    | succ k =>
      cases i using Fin.cases with
      | zero => exact fst_pair _ _
      | succ i => exact (unpackCongr (snd_pair _ _) i).eqTrans (ih (fun j => xs j.succ) i)

private theorem substUnpack {m : ℕ} (σ : Fin n → PTm m) (t : PTm n) (i : Fin k) :
    Syn.subst σ (unpack k t i) = unpack k (Syn.subst σ t) i := by
  induction k generalizing t with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    cases k with
    | zero => rfl
    | succ k =>
      cases i using Fin.cases with
      | zero => exact subst_fstT σ t
      | succ i =>
        simp only [unpack, Fin.cases_succ]
        rw [ih, subst_sndT]

private theorem substPack {m : ℕ} (σ : Fin n → PTm m) (xs : Fin k → PTm n) :
    Syn.subst σ (pack xs) = pack (fun i => Syn.subst σ (xs i)) := by
  induction k with
  | zero => exact PTm.subst_zero _
  | succ k ih =>
    cases k with
    | zero => rfl
    | succ k => simp only [pack, subst_pairT, ih]

/-- Apply the search body to a candidate and the parameter family. -/
def applyBody (f : PTm (k + 1)) (x : PTm n) (xs : Fin k → PTm n) : PTm n :=
  Syn.subst (Fin.cases x xs) f

private def packedBody (f : PTm (k + 1)) : PTm 2 :=
  applyBody f (var 0) (unpack k (var 1))

private theorem packedValue (f : PTm (k + 1)) (i : PTm n) (xs : Fin k → PTm n) :
    Γ ⊢[PRAAx] inst2 (packedBody f) i (pack xs) ≐ applyBody f i xs := by
  simp only [inst2, packedBody, applyBody, Syn.subst_subst]
  apply Prf.eqCongr
  intro j
  cases j using Fin.cases with
  | zero => exact .eqRefl _
  | succ j => simpa only [Fin.cases_succ, substUnpack, Syn.subst_var,
      Matrix.cons_val_one, Matrix.cons_val_zero] using
      (unpackPack (Γ := Γ) xs j)

/-- Find the first zero strictly below `N`, or return `N` if there is none. -/
def mu (f : PTm (k + 1)) (N : PTm n) (xs : Fin k → PTm n) : PTm n :=
  Search.mu (packedBody f) N (pack xs)

@[simp] theorem subst_mu {m : ℕ} (σ : Fin n → PTm m) (f : PTm (k + 1))
    (N : PTm n) (xs : Fin k → PTm n) :
    Syn.subst σ (mu f N xs) = mu f (Syn.subst σ N) (fun i => Syn.subst σ (xs i)) := by
  simp only [mu, Search.mu, subst_ap2, substPack]

/-- A singleton parameter gives the original search symbol and argument. -/
theorem mu_single (f : PTm 2) (N x : PTm n) :
    mu f N ![x] = Search.mu f N x := by
  have args : (Fin.cases (var 0) (unpack 1 (var 1)) : Fin 2 → PTm 2) = var := by
    funext i
    fin_cases i <;> rfl
  simp only [mu, pack, Matrix.cons_val_zero, packedBody, applyBody, args, Syn.subst_id]

theorem mu_zero (f : PTm (k + 1)) (xs : Fin k → PTm n) :
    Γ ⊢[PRAAx] mu f zero xs ≐ zero :=
  Search.mu_zero (pack xs)

theorem mu_succ (f : PTm (k + 1)) (N : PTm n) (xs : Fin k → PTm n) :
    Γ ⊢[PRAAx] mu f (succ N) xs ≐ mu f N xs + eqb (mu f N xs) N * sg (applyBody f N xs) :=
  (Search.mu_succ (f := packedBody f) N (pack xs)).eqTrans
    (congrAdd (.eqRefl _) (congrMul (.eqRefl _)
      (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (packedValue f N xs)))))

theorem search_spec (f : PTm (k + 1)) (N i : PTm n) (xs : Fin k → PTm n) :
    Γ ⊢[PRAAx] le (mu f N xs) N ⋏ ((lt (mu f N xs) N ⟶ (applyBody f (mu f N xs) xs ≐ zero)) ⋏
      (lt i (mu f N xs) ⟶ neg (applyBody f i xs ≐ zero))) := by
  have spec := Search.search_spec (Γ := Γ) (f := packedBody f) N i (pack xs)
  refine .andI (.andE₁ spec) (.andI ?_ ?_)
  · exact .impI ((packedValue f (mu f N xs) xs).eqSymm.eqTrans
      (.impE (Prf.andE₁ (Prf.andE₂ spec)).wk Prf.hyp0))
  · exact .impI (.impI (.impE
      (.impE (Prf.andE₂ (Prf.andE₂ spec)).wk.wk Prf.hyp1)
      ((packedValue f i xs).eqTrans Prf.hyp0)))

theorem search_found {f : PTm (k + 1)} {N i : PTm n} {xs : Fin k → PTm n}
    (hf : Γ ⊢[PRAAx] applyBody f i xs ≐ zero) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] lt (mu f N xs) N ⋏ ((applyBody f (mu f N xs) xs ≐ zero) ⋏ le (mu f N xs) i) := by
  have found := Search.search_found (f := packedBody f) ((packedValue f i xs).eqTrans hf) hi
  exact .andI (.andE₁ found) (.andI
    ((packedValue f (mu f N xs) xs).eqSymm.eqTrans (.andE₁ (.andE₂ found))) (.andE₂ (.andE₂ found)))

theorem search_failed (f : PTm (k + 1)) (N : PTm n) (xs : Fin k → PTm n)
    (noWitness : ∀ i : PTm n, Γ ⊢[PRAAx] lt i N ⟶ neg (applyBody f i xs ≐ zero)) :
    Γ ⊢[PRAAx] mu f N xs ≐ N := by
  have spec := search_spec (Γ := Γ) f N (mu f N xs) xs
  refine .orE (lt_or_eq_of_le (Prf.andE₁ spec)) ?_ Prf.hyp0
  exact .botE _ (.impE (.impE (noWitness (mu f N xs)).wk Prf.hyp0)
    (.impE (Prf.andE₁ (Prf.andE₂ spec)).wk Prf.hyp0))

end LeanProofs.IPRA.Search.Finite
