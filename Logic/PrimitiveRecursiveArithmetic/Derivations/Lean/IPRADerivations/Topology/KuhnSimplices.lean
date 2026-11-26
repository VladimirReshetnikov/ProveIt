import IPRADerivations.Foundations.GridSumsContext
import IPRADerivations.Foundations.BoundedDecision
import Mathlib.GroupTheory.Perm.Fin

/-!
# Kuhn simplices of a cube in every dimension (`dimension_invariance_ipra`)

Packet: `topology/dimension_invariance_ipra`, Section "A complete finite cubical Sperner argument":
the Kuhn simplex `(a, π)` of the grid `[0, N]^d` has the vertices `v_t = a + e_{π_1} + ⋯ + e_{π_t}`
(`0 ≤ t ≤ d`). Points are the packed lists of `Foundations/GridSums`; entry `q` (from the top) is
coordinate `d − 1 − q`, so the top entry is the last coordinate.

* `incr k b x`: the list `x` with the entries `q < k` selected by `b` incremented (`bump`); its
  entries (`proj_incr`) and tail (`tl_incr`), incrementing one more entry (`incr_upd`), a top entry
  `0` (`incr_pair_zero`), and the canonical repacking `canon k b` over a base `b` (`incr_canon`);
* `vbit π t`: entry `q` is incremented in `v_t` iff `π⁻¹(q) < t`; `vert π t x`. Defined entry by
  entry, so that two permutations with the same vertex sets give the same vertex terms;
* `exactPat k`: the term in `k` colour variables "each colour `j < k` occurs exactly once";
  `ev_exactPat`;
* `simplex_count` (in Lean): for colours `c_0, …, c_d ≤ d`, with `door_t` = the facet without `v_t`
  has the colours `0, …, d − 1` once each, `Σ_t [door_t] + [full] = 2 [some door]`: one door if the
  simplex is full, else none or two. This is the counting step "the parity of the number of door
  occurrences equals the parity of the number of full `d`-simplices";
* `simplex_identity`: its iPRA form, by `Foundations/BoundedDecision.bounded_decide`, for colour terms
  provably `≤ d`;
* the permutation facts behind the facet pairing rules (1)–(3) of the packet: `vbit_swap` (an
  interior facet is shared by `π` and `π ∘ (t − 1, t)`), `vbit_rot`, `vbit_rot_self` (the first
  facet of `(a, π)` is the last facet of `(a + e_{π_1}, π ∘ rotation)`), `vbit_rot_decomp` (on the
  lower face of the top coordinate the last facets are the Kuhn simplices one dimension down);
  `sum_even_of_invol` (a sum invariant under a fixed-point-free involution is even).
-/


set_option autoImplicit false

namespace LeanProofs.IPRA.Topology.KuhnSimplices

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm BigOperators
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)
open LeanProofs.IPRA.Foundations.GridSums
open LeanProofs.IPRA.Foundations.TermSums
open Equiv

variable {n : ℕ}

/-! ## Incrementing a set of entries -/

/-- `t` or `t + 1`. -/
def bump : Bool → PTm n → PTm n
  | true, t => succ t
  | false, t => t

@[simp] theorem subst_bump {m : ℕ} (σ : Fin n → PTm m) (c : Bool) (t : PTm n) :
    Syn.subst σ (bump c t) = bump c (Syn.subst σ t) := by cases c <;> rfl

theorem congrBump {Γ : List (Fm PTm n)} (c : Bool) {t t' : PTm n} (h : Γ ⊢[PRAAx] t ≐ t') :
    Γ ⊢[PRAAx] bump c t ≐ bump c t' := by
  cases c
  · exact h
  · exact congrSucc h

/-- The list `x` with the entries `q < k` with `b q` incremented. -/
def incr : ℕ → (ℕ → Bool) → PTm n → PTm n
  | 0, _, x => x
  | k + 1, b, x => pairT (bump (b 0) (fstT x)) (incr k (fun q => b (q + 1)) (sndT x))

@[simp] theorem subst_incr {m : ℕ} (σ : Fin n → PTm m) :
    ∀ (k : ℕ) (b : ℕ → Bool) (x : PTm n), Syn.subst σ (incr k b x) = incr k b (Syn.subst σ x)
  | 0, _, _ => rfl
  | k + 1, b, x => by simp [incr, subst_incr σ k]

theorem congrIncr {Γ : List (Fm PTm n)} :
    ∀ (k : ℕ) (b : ℕ → Bool) {x x' : PTm n}, (Γ ⊢[PRAAx] x ≐ x') →
      (Γ ⊢[PRAAx] incr k b x ≐ incr k b x')
  | 0, _, _, _, h => h
  | k + 1, _, _, _, h => congrPairT (congrBump _ (congrFst h)) (congrIncr k _ (congrSnd h))

theorem proj_incr {Γ : List (Fm PTm n)} :
    ∀ (k : ℕ) (b : ℕ → Bool) (q : ℕ) (x : PTm n), q < k →
      (Γ ⊢[PRAAx] proj q (incr k b x) ≐ bump (b q) (proj q x))
  | k + 1, b, 0, x, _ => fst_pair _ _
  | k + 1, b, q + 1, x, h => (proj_pair_succ q _ _).eqTrans (proj_incr k _ q (sndT x) (by omega))

theorem tl_incr {Γ : List (Fm PTm n)} :
    ∀ (k : ℕ) (b : ℕ → Bool) (x : PTm n), Γ ⊢[PRAAx] tl k (incr k b x) ≐ tl k x
  | 0, _, _ => .eqRefl _
  | k + 1, _, x => (tl_pair_succ k _ _).eqTrans (tl_incr k _ (sndT x))

/-- Incrementing one more entry `c` (not yet selected). -/
theorem incr_upd {Γ : List (Fm PTm n)} :
    ∀ (k : ℕ) (b : ℕ → Bool) (c : ℕ) (x : PTm n), c < k → b c = false →
      (Γ ⊢[PRAAx] incr k b (upd c x) ≐ incr k (Function.update b c true) x)
  | k + 1, b, 0, x, _, hb => by
    have e : (fun q => Function.update b 0 true (q + 1)) = fun q => b (q + 1) :=
      funext fun q => Function.update_of_ne (by omega) _ _
    simp only [incr, upd, hb, Function.update_self, e, bump]
    exact congrPairT (fst_pair _ _) (congrIncr k _ (snd_pair _ _))
  | k + 1, b, c + 1, x, hc, hb => by
    have e₀ : Function.update b (c + 1) true 0 = b 0 := Function.update_of_ne (by omega) _ _
    have e : (fun q => Function.update b (c + 1) true (q + 1)) =
        Function.update (fun q => b (q + 1)) c true := by
      funext q
      by_cases hq : q = c
      · subst hq; simp
      · rw [Function.update_of_ne (show q + 1 ≠ c + 1 by omega), Function.update_of_ne hq]
    simp only [incr, upd, e₀, e]
    exact congrPairT (congrBump _ (fst_pair _ _))
      ((congrIncr k _ (snd_pair _ _)).eqTrans (incr_upd k _ c (sndT x) (by omega) hb))

/-- A top entry `0` that is not incremented. -/
theorem incr_pair_zero {Γ : List (Fm PTm n)} (k : ℕ) (b : ℕ → Bool) (y : PTm n) (hb : b 0 = false) :
    Γ ⊢[PRAAx] incr (k + 1) b (pairT zero y) ≐ pairT zero (incr k (fun q => b (q + 1)) y) := by
  simp only [incr, hb, bump]
  exact congrPairT (fst_pair _ _) (congrIncr k _ (snd_pair _ _))

/-- The canonical packed list over the base `b` with the first `k` entries of `v`. -/
def canon : ℕ → PTm n → PTm n → PTm n
  | 0, b, _ => b
  | k + 1, b, v => pairT (fstT v) (canon k b (sndT v))

@[simp] theorem subst_canon {m : ℕ} (σ : Fin n → PTm m) :
    ∀ (k : ℕ) (b v : PTm n), Syn.subst σ (canon k b v) = canon k (Syn.subst σ b) (Syn.subst σ v)
  | 0, _, _ => rfl
  | k + 1, b, v => by simp [canon, subst_canon σ k]

theorem congrCanon {Γ : List (Fm PTm n)} :
    ∀ (k : ℕ) (b : PTm n) {v v' : PTm n}, (Γ ⊢[PRAAx] v ≐ v') → (Γ ⊢[PRAAx] canon k b v ≐ canon k b v')
  | 0, _, _, _, _ => .eqRefl _
  | k + 1, b, _, _, h => congrPairT (congrFst h) (congrCanon k b (congrSnd h))

/-- An incremented list is canonical over the base of the original list. -/
theorem incr_canon {Γ : List (Fm PTm n)} :
    ∀ (k : ℕ) (bits : ℕ → Bool) (y b : PTm n), (Γ ⊢[PRAAx] tl k y ≐ b) →
      (Γ ⊢[PRAAx] incr k bits y ≐ canon k b (incr k bits y))
  | 0, _, _, _, h => h
  | k + 1, bits, y, b, h => by
    simp only [incr, canon]
    exact congrPairT (fst_pair _ _).eqSymm
      ((incr_canon k _ (sndT y) b h).eqTrans (congrCanon k b (snd_pair _ _).eqSymm))

/-- The bound defect `Σ_q (x_q ∸ N)` of the first `k` entries over the base `b`. -/
def bsum (k : ℕ) (v b : PTm n) : PTm n := fsum k (fun q => monus (proj q.val v) (fstT b))

ipra_subst bsum

/-- The vertices of a Kuhn simplex in an admissible position are grid points over the base. -/
theorem incr_grid {Γ : List (Fm PTm n)} (k : ℕ) (bits : ℕ → Bool) (y b : PTm n)
    (hb : Γ ⊢[PRAAx] tl k y ≐ b) (hle : ∀ q, q < k → (Γ ⊢[PRAAx] le (proj q y) (fstT b)))
    (hlt : ∀ q, q < k → bits q = true → (Γ ⊢[PRAAx] lt (proj q y) (fstT b))) :
    (Γ ⊢[PRAAx] incr k bits y ≐ canon k b (incr k bits y)) ∧
      (Γ ⊢[PRAAx] bsum k (incr k bits y) b ≐ zero) := by
  refine ⟨incr_canon k bits y b hb, fsum_eq_zero (fun q => ?_)⟩
  refine (congrMonus (proj_incr k bits q.val y q.isLt) (.eqRefl _)).eqTrans ?_
  cases h : bits q.val
  · exact hle q.val q.isLt
  · exact hlt q.val q.isLt h

/-! ## The vertices of a Kuhn simplex -/

variable (d : ℕ)

/-- Entry `q` of the vertex `v_t` of the simplex `π` is incremented iff `π⁻¹(q) < t`. -/
def vbit (π : Perm (Fin d)) (t : ℕ) : ℕ → Bool := fun q =>
  if h : q < d then decide ((π.symm ⟨q, h⟩ : ℕ) < t) else false

/-- The vertex `v_t` of the Kuhn simplex `π` with base list `x`. -/
def vert (π : Perm (Fin d)) (t : ℕ) (x : PTm n) : PTm n := incr d (vbit d π t) x

@[simp] theorem subst_vert {m : ℕ} (σ : Fin n → PTm m) (π : Perm (Fin d)) (t : ℕ) (x : PTm n) :
    Syn.subst σ (vert d π t x) = vert d π t (Syn.subst σ x) := by simp [vert]

/-! ## The colour pattern -/

/-- Each colour `j < k` occurs exactly once among the `k` colour variables. -/
def exactPat (k : ℕ) : PTm k :=
  fprod k (fun j => eqb (fsum k (fun s => eqb (Syn.var s) (num j.val))) one)

/-- The number of `s` with `c s = j`. -/
def cntV {k : ℕ} (c : Fin k → ℕ) (j : ℕ) : ℕ := ∑ s, if c s = j then 1 else 0

/-- `[each colour j < k occurs exactly once]`. -/
def exactV (k : ℕ) (c : Fin k → ℕ) : ℕ := ∏ j : Fin k, if cntV c j.val = 1 then 1 else 0

theorem ev_exactPat (k : ℕ) (ρ : Fin k → ℕ) : PTm.ev ρ (exactPat k) = exactV k ρ := by
  simp [exactPat, exactV, cntV]

theorem exactV_eq (k : ℕ) (c : Fin k → ℕ) :
    exactV k c = if ∀ j : Fin k, cntV c j.val = 1 then 1 else 0 := by
  simp [exactV, Finset.prod_boole]

/-! ## The door count of one simplex (in the metatheory) -/

section Count

variable {d}

theorem cnt_split (c : Fin (d + 1) → ℕ) (t : Fin (d + 1)) (j : ℕ) :
    cntV (c ∘ t.succAbove) j + (if c t = j then 1 else 0) = cntV c j := by
  simp only [cntV, Fin.sum_univ_succAbove _ t, Function.comp_apply]; ring_nf

theorem cnt_total (c : Fin (d + 1) → ℕ) (hc : ∀ s, c s ≤ d) :
    ∑ j : Fin (d + 1), cntV c j.val = d + 1 := by
  simp only [cntV]
  rw [Finset.sum_comm]
  have h : ∀ s, (∑ j : Fin (d + 1), if c s = j.val then 1 else 0) = 1 := by
    intro s
    rw [Finset.sum_eq_single (⟨c s, by have := hc s; omega⟩ : Fin (d + 1))]
    · simp
    · intro j _ hj; rw [if_neg]; intro h; exact hj (Fin.ext h.symm)
    · simp
  simp [h]

theorem cnt_pos (c : Fin (d + 1) → ℕ) (t : Fin (d + 1)) : 1 ≤ cntV c (c t) := by
  have := cnt_split c t (c t); simp at this; omega

theorem cnt_last (c : Fin (d + 1) → ℕ) (hc : ∀ s, c s ≤ d) :
    (∑ j : Fin d, cntV c j.val) + cntV c d = d + 1 := by
  have h := cnt_total c hc
  rw [Fin.sum_univ_castSucc] at h
  simpa using h

/-- `cntV` counts a filter. -/
theorem cnt_card (c : Fin (d + 1) → ℕ) (j : ℕ) :
    cntV c j = (Finset.univ.filter (fun s => c s = j)).card := by
  simp [cntV, Finset.sum_boole]

/-- The door count of one simplex: `Σ_t [door_t] + [full] = 2 [some door]` for colours `≤ d`. -/
theorem simplex_count (c : Fin (d + 1) → ℕ) (hc : ∀ s, c s ≤ d) :
    (∑ t : Fin (d + 1), exactV d (c ∘ t.succAbove)) + exactV (d + 1) c =
      2 * (if ∑ t : Fin (d + 1), exactV d (c ∘ t.succAbove) = 0 then 0 else 1) := by
  simp only [exactV_eq]
  rw [Finset.sum_boole]
  set door : Fin (d + 1) → Prop := fun t => ∀ j : Fin d, cntV (c ∘ t.succAbove) j.val = 1 with hdoor
  have hsplit := cnt_split c
  by_cases hD : ∃ t₀, door t₀
  · obtain ⟨t₀, h₀⟩ := hD
    have hm : ∀ j : ℕ, j < d → cntV c j = 1 + (if c t₀ = j then 1 else 0) := by
      intro j hj; have := hsplit t₀ j; have := h₀ ⟨j, hj⟩; simp at *; omega
    have hlast := cnt_last c hc
    by_cases hj : c t₀ = d
    · -- the simplex is full and its only door is opposite the vertex of colour `d`
      have hsum : ∑ j : Fin d, cntV c j.val = d := by
        rw [Finset.sum_congr rfl (fun j _ => by rw [hm j.val j.isLt, if_neg (by omega)])]; simp
      have hmd : cntV c d = 1 := by omega
      have hfull : ∀ j : Fin (d + 1), cntV c j.val = 1 := by
        intro j
        by_cases hjd : j.val = d
        · rw [hjd, hmd]
        · rw [hm j.val (by omega), if_neg (by omega)]
      have hdset : Finset.univ.filter door = Finset.univ.filter (fun s => c s = d) := by
        ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro ht
          by_contra hne
          have hlt : c t < d := by have := hc t; omega
          have e₁ := hsplit t (c t)
          have e₂ : cntV (c ∘ t.succAbove) (c t) = 1 := ht ⟨c t, hlt⟩
          rw [hm (c t) hlt, if_neg (show ¬ c t₀ = c t by omega), if_pos rfl] at e₁; omega
        · intro ht j
          have e₁ := hsplit t j.val
          rw [hm j.val j.isLt, if_neg (by omega), if_neg (by omega)] at e₁; omega
      rw [hdset, ← cnt_card, hmd, if_pos hfull]; simp
    · -- one colour `j₀ < d` is repeated, colour `d` is absent: two doors
      have hj₀ : c t₀ < d := by have := hc t₀; omega
      have hsum : ∑ j : Fin d, cntV c j.val = d + 1 := by
        have : ∀ j : Fin d, cntV c j.val = 1 + (if (⟨c t₀, hj₀⟩ : Fin d) = j then 1 else 0) := by
          intro j; rw [hm j.val j.isLt]; congr 1
          by_cases h : (⟨c t₀, hj₀⟩ : Fin d) = j
          · rw [if_pos h, if_pos (by rw [← h])]
          · rw [if_neg h, if_neg (fun h' => h (Fin.ext h'))]
        rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_add_distrib]; simp
      have hmd : cntV c d = 0 := by omega
      have hnf : ¬ ∀ j : Fin (d + 1), cntV c j.val = 1 := by
        intro h; have := h (Fin.last d); simp [hmd] at this
      have hdset : Finset.univ.filter door = Finset.univ.filter (fun s => c s = c t₀) := by
        ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro ht
          have hne : c t ≠ d := by have := cnt_pos c t; intro h; rw [h] at this; omega
          have hlt : c t < d := by have := hc t; omega
          by_contra hne'
          have e₁ := hsplit t (c t); have e₂ := ht ⟨c t, hlt⟩
          rw [hm (c t) hlt, if_neg (Ne.symm hne')] at e₁; simp at e₁ e₂; omega
        · intro ht j
          have e₁ := hsplit t j.val
          rw [hm j.val j.isLt, ht] at e₁
          by_cases h : c t₀ = j.val
          · rw [if_pos h] at e₁; omega
          · rw [if_neg h] at e₁; omega
      have hm₀ : cntV c (c t₀) = 2 := by rw [hm _ hj₀, if_pos rfl]
      rw [hdset, ← cnt_card, hm₀, if_neg hnf]; simp
  · -- no door: the simplex is not full either
    have hempty : Finset.univ.filter door = ∅ := by
      ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact fun h => hD ⟨t, h⟩
    have hnf : ¬ ∀ j : Fin (d + 1), cntV c j.val = 1 := by
      intro hfull
      have hmd : cntV c d = 1 := by simpa using hfull (Fin.last d)
      obtain ⟨t, ht⟩ : ∃ t, c t = d := by
        by_contra h; simp only [not_exists] at h
        have : cntV c d = 0 := by simp [cntV, h]
        omega
      refine hD ⟨t, fun j => ?_⟩
      have e₁ := hsplit t j.val
      rw [hfull ⟨j.val, by omega⟩, if_neg (by rw [ht]; omega)] at e₁; omega
    rw [hempty, if_neg hnf]; simp

end Count

/-! ## The door count in iPRA -/

/-- The facet pattern without vertex `t`. -/
def doorPat (t : Fin (d + 1)) : PTm (d + 1) :=
  Syn.subst (fun s : Fin d => Syn.var (t.succAbove s)) (exactPat d)

/-- `Σ_t door_t + full`. -/
def cellPat : PTm (d + 1) := fsum (d + 1) (doorPat d) + exactPat (d + 1)

/-- `2 sg(Σ_t door_t)`. -/
def evenPat : PTm (d + 1) := two * Signum.sg (fsum (d + 1) (doorPat d))

theorem subst_doorPat {m : ℕ} (σ : Fin (d + 1) → PTm m) (t : Fin (d + 1)) :
    Syn.subst σ (doorPat d t) = Syn.subst (fun s => σ (t.succAbove s)) (exactPat d) := by
  rw [doorPat, Syn.subst_subst]; congr 1

/-- The door count of one simplex, for colour terms provably `≤ d`. -/
theorem simplex_identity {Γ : List (Fm PTm n)} (σ : Fin (d + 1) → PTm n)
    (hσ : ∀ s, Γ ⊢[PRAAx] le (σ s) (num d)) :
    Γ ⊢[PRAAx] Syn.subst σ (cellPat d) ≐ Syn.subst σ (evenPat d) := by
  refine Foundations.BoundedDecision.bounded_decide d _ _ (fun ρ hρ => ?_) σ hσ
  have hd : ∀ t, PTm.ev ρ (doorPat d t) = exactV d (ρ ∘ t.succAbove) := by
    intro t; rw [doorPat, ev_subst, ev_exactPat]; rfl
  simp only [cellPat, evenPat, ev_add, ev_mul, ev_sg, ev_fsum, hd, ev_exactPat, ev_succ, ev_zero]
  rw [simplex_count ρ hρ]

/-! ## Permutations and the facet pairing -/

section Pairing

variable {d}

theorem vbit_eq (π : Perm (Fin d)) (t q : ℕ) (hq : q < d) :
    vbit d π t q = decide ((π.symm ⟨q, hq⟩ : ℕ) < t) := by simp [vbit, hq]

theorem vbit_ge (π : Perm (Fin d)) (t q : ℕ) (hq : d ≤ q) : vbit d π t q = false := by
  have h : ¬ q < d := by omega
  simp [vbit, h]

/-- Rule (1): exchanging the positions `t − 1` and `t` changes only the vertex `v_t`. -/
theorem vbit_swap (π : Perm (Fin d)) (a b : Fin d) (hab : b.val = a.val + 1) (s : ℕ)
    (hs : s ≠ b.val) : vbit d (π * swap a b) s = vbit d π s := by
  funext q
  by_cases hq : q < d
  · rw [vbit_eq _ _ _ hq, vbit_eq _ _ _ hq, decide_eq_decide]
    have e : (π * swap a b).symm ⟨q, hq⟩ = swap a b (π.symm ⟨q, hq⟩) := by
      simp [Perm.mul_def, Equiv.symm_swap]
    rw [e]
    generalize π.symm ⟨q, hq⟩ = u
    by_cases hua : u = a
    · rw [hua, swap_apply_left]; omega
    · by_cases hub : u = b
      · rw [hub, swap_apply_right]; omega
      · rw [swap_apply_of_ne_of_ne hua hub]
  · rw [vbit_ge (π * swap a b) s q (by omega), vbit_ge π s q (by omega)]

/-- The rotation `π ↦ π ∘ (1 2 ⋯ d)`. -/
def rot (π : Perm (Fin (d + 1))) : Perm (Fin (d + 1)) := π * finRotate (d + 1)

theorem rot_symm_val (π : Perm (Fin (d + 1))) (q : Fin (d + 1)) :
    ((rot π).symm q : ℕ) = if (π.symm q : ℕ) = 0 then d else (π.symm q : ℕ) - 1 := by
  simp only [rot, Perm.mul_def, Equiv.symm_trans_apply]
  set u := π.symm q
  set w := (finRotate (d + 1)).symm u with hw
  have hu : finRotate (d + 1) w = u := by simp [hw]
  by_cases hl : w = Fin.last d
  · rw [hl, finRotate_last] at hu
    rw [hl, if_pos (show (u : ℕ) = 0 by rw [← hu]; rfl)]; simp
  · have := coe_finRotate_of_ne_last hl
    rw [hu] at this
    rw [if_neg (show ¬ (u : ℕ) = 0 by omega)]; omega

/-- The entry `π_1` is not incremented in the first `d + 1` vertices of `rot π`. -/
theorem vbit_rot_self (π : Perm (Fin (d + 1))) (s : ℕ) (hs : s ≤ d) :
    vbit (d + 1) (rot π) s (π 0) = false := by
  rw [vbit_eq _ _ _ (π 0).isLt]
  have : ((rot π).symm ⟨(π 0 : ℕ), (π 0).isLt⟩ : ℕ) = d := by
    rw [rot_symm_val]; simp
  rw [this, decide_eq_false_iff_not]; omega

/-- Rule (2): the vertex `v_{s+1}` of `π` is the vertex `v_s` of `rot π` with entry `π_1`
incremented. -/
theorem vbit_rot (π : Perm (Fin (d + 1))) (s : ℕ) :
    vbit (d + 1) π (s + 1) = Function.update (vbit (d + 1) (rot π) s) (π 0) true := by
  funext q
  by_cases hq : q < d + 1
  · by_cases hc : q = (π 0 : ℕ)
    · subst hc
      rw [Function.update_self, vbit_eq _ _ _ (π 0).isLt]
      simp
    · rw [Function.update_of_ne hc, vbit_eq _ _ _ hq, vbit_eq _ _ _ hq, rot_symm_val]
      have hne : (π.symm ⟨q, hq⟩ : ℕ) ≠ 0 := by
        intro h
        have : π.symm ⟨q, hq⟩ = 0 := Fin.ext h
        apply hc
        rw [← this, Equiv.apply_symm_apply]
      rw [if_neg hne, decide_eq_decide]; omega
  · rw [Function.update_of_ne (show q ≠ (π 0 : ℕ) by have := (π 0).isLt; omega),
      vbit_ge π (s + 1) q (by omega), vbit_ge (rot π) s q (by omega)]

/-- The permutations of `Fin (d + 1)` fixing `0`, from the permutations of `Fin d`. -/
def lift0 (τ : Perm (Fin d)) : Perm (Fin (d + 1)) := Perm.decomposeFin.symm (0, τ)

theorem lift0_symm_zero (τ : Perm (Fin d)) : (lift0 τ).symm 0 = 0 := by
  rw [Equiv.symm_apply_eq]; simp [lift0]

theorem lift0_symm_succ (τ : Perm (Fin d)) (q : Fin d) : (lift0 τ).symm q.succ = (τ.symm q).succ := by
  rw [Equiv.symm_apply_eq]; simp [lift0, Perm.decomposeFin_symm_apply_succ]

theorem lift0_zero (τ : Perm (Fin d)) : lift0 τ 0 = 0 := by simp [lift0]

/-- Rule (3) on the lower face of the top coordinate: the vertices `v_s` (`s ≤ d`) of
`rot (lift0 τ)` do not increment the top entry, and below it they are the vertices of `τ`. -/
theorem vbit_rot_lift0_zero (τ : Perm (Fin d)) (s : ℕ) (hs : s ≤ d) :
    vbit (d + 1) (rot (lift0 τ)) s 0 = false := by
  have h := vbit_rot_self (lift0 τ) s hs
  rwa [lift0_zero] at h

theorem vbit_rot_lift0_succ (τ : Perm (Fin d)) (s : ℕ) :
    (fun q => vbit (d + 1) (rot (lift0 τ)) s (q + 1)) = vbit d τ s := by
  funext q
  by_cases hq : q < d
  · rw [vbit_eq (rot (lift0 τ)) s (q + 1) (by omega), vbit_eq τ s q hq, rot_symm_val]
    have e : (⟨q + 1, by omega⟩ : Fin (d + 1)) = (⟨q, hq⟩ : Fin d).succ := rfl
    rw [e, lift0_symm_succ]
    simp
  · rw [vbit_ge (rot (lift0 τ)) s (q + 1) (by omega), vbit_ge τ s q (by omega)]

end Pairing

/-! ## Sums invariant under an involution -/

theorem sum_even_of_invol {α M : Type} [Fintype α] [DecidableEq α] [AddCommMonoid M]
    (f : α → M) (ι : α → α) (hι : ∀ a, ι (ι a) = a) (hfix : ∀ a, ι a ≠ a)
    (hf : ∀ a, f (ι a) = f a) : ∃ X, ∑ a, f a = X + X := by
  classical
  have hlt : ∀ a, ¬ (Fintype.equivFin α a < Fintype.equivFin α (ι a)) →
      Fintype.equivFin α (ι a) < Fintype.equivFin α a := by
    intro a ha
    have hne : Fintype.equivFin α (ι a) ≠ Fintype.equivFin α a :=
      fun h => hfix a ((Fintype.equivFin α).injective h)
    exact lt_of_le_of_ne (not_lt.mp ha) hne
  refine ⟨∑ a ∈ Finset.univ.filter (fun a => Fintype.equivFin α a < Fintype.equivFin α (ι a)), f a, ?_⟩
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun a => Fintype.equivFin α a < Fintype.equivFin α (ι a))]
  congr 1
  refine Finset.sum_nbij' ι ι ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_filter] at ha ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hι]; exact hlt a ha.2
  · intro a ha
    rw [Finset.mem_filter] at ha ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hι]; exact not_lt.mpr (_root_.le_of_lt ha.2)
  · intro a _; exact hι a
  · intro a _; exact hι a
  · intro a _; exact (hf a).symm

end LeanProofs.IPRA.Topology.KuhnSimplices
