import IPRADerivations.Core.SumLemmas
import IPRADerivations.Core.Pairing
import IPRADerivations.Core.Fubini
import IPRADerivations.Core.Tactic
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.Header

/-!
# Sums over a cubical grid in any fixed dimension

A reusable piece of the embedding framework: sums `∑_{a ∈ [0, N)^d} F(a, p)` with the dimension `d`
a parameter of the Lean statements (each instance one iPRA derivation), built from the one-index
sums `sumF` of `Core/Definitions` by packing the coordinates into one parameter. Motivated by the
cubical Sperner lemma `thm:sperner` of `topology/dimension_invariance_ipra` in every dimension.

**Packed lists.** A point is a packed list `⟨a_{e−1}, ⟨a_{e−2}, …, ⟨a_0, B⟩⟩⟩` above a base `B`
(for the grid, `B = ⟨N, p⟩`); `proj j x` is the `j`-th entry from the top and `tl j x` the list
after `j` entries (`proj_pair_zero`, `proj_pair_succ`, `tl_pair_succ`, `congrProj`, `congrTl`).

**Grid sums.** A summand is a term `F : PTm 1` whose variable is the full packed list. With the
current list `x` of depth `e` (coordinates chosen so far) the bound is `N = fst (tl e x)`, and

`gs e 0 F = F`, `gs e (k + 1) F = ∑_{i < N} gs (e + 1) k F [x ↦ ⟨i, x⟩]`,

so `gs 0 d F` at the base `⟨N, p⟩` is `∑_{a_0 < N} ⋯ ∑_{a_{d−1} < N} F(⟨a_{d−1}, …, ⟨a_0, ⟨N, p⟩⟩⟩)`.

* `gs_succ`: the unfolding of one level;
* `gs_congr`: summands that are provably equal at every argument (in every context) have
  provably equal grid sums;
* `gs_add`: the grid sum of `F + G` is the sum of the grid sums;
* `gs_bound`: the bound read at depth `e + 1` inside the body is the bound at depth `e`.

The hypotheses of `gs_congr` are unconditional (every argument, every context); this is the
form used when the pointwise identities are polynomial or follow from universally stated
hypotheses.
-/

namespace LeanProofs.IPRA.Foundations.GridSums

open_ipra

variable {n : ℕ}

/-! ## Packed lists -/

/-- The `j`-th entry of a packed list `⟨x_0, ⟨x_1, …⟩⟩`. -/
def proj : ℕ → PTm n → PTm n
  | 0, x => fstT x
  | j + 1, x => proj j (sndT x)

/-- The list after `j` entries. -/
def tl : ℕ → PTm n → PTm n
  | 0, x => x
  | j + 1, x => tl j (sndT x)

@[simp] theorem subst_proj {m : ℕ} (σ : Fin n → PTm m) :
    ∀ (j : ℕ) (x : PTm n), Syn.subst σ (proj j x) = proj j (Syn.subst σ x)
  | 0, x => by simp [proj]
  | j + 1, x => by simp [proj, subst_proj σ j]

@[simp] theorem subst_tl {m : ℕ} (σ : Fin n → PTm m) :
    ∀ (j : ℕ) (x : PTm n), Syn.subst σ (tl j x) = tl j (Syn.subst σ x)
  | 0, x => rfl
  | j + 1, x => by simp [tl, subst_tl σ j]

theorem congrProj {Γ : List (Fm PTm n)} :
    ∀ (j : ℕ) {x x' : PTm n}, (Γ ⊢[PRAAx] x ≐ x') → (Γ ⊢[PRAAx] proj j x ≐ proj j x')
  | 0, _, _, h => congrFst h
  | j + 1, _, _, h => congrProj j (congrSnd h)

theorem congrTl {Γ : List (Fm PTm n)} :
    ∀ (j : ℕ) {x x' : PTm n}, (Γ ⊢[PRAAx] x ≐ x') → (Γ ⊢[PRAAx] tl j x ≐ tl j x')
  | 0, _, _, h => h
  | j + 1, _, _, h => congrTl j (congrSnd h)

theorem proj_pair_zero {Γ : List (Fm PTm n)} (u x : PTm n) :
    Γ ⊢[PRAAx] proj 0 (pairT u x) ≐ u := fst_pair u x

theorem proj_pair_succ {Γ : List (Fm PTm n)} (j : ℕ) (u x : PTm n) :
    Γ ⊢[PRAAx] proj (j + 1) (pairT u x) ≐ proj j x := congrProj j (snd_pair u x)

theorem tl_pair_succ {Γ : List (Fm PTm n)} (j : ℕ) (u x : PTm n) :
    Γ ⊢[PRAAx] tl (j + 1) (pairT u x) ≐ tl j x := congrTl j (snd_pair u x)

/-! ## Grid sums -/

/-- The body of one level: the summand with the list `x` extended by the index. -/
def gsBody (G : PTm 1) : PTm 2 := Syn.subst ![pairT (var 0) (var 1)] G

/-- The grid sum over `k` more coordinates, the current list having depth `e`. -/
def gs (e : ℕ) : ℕ → PTm 1 → PTm 1
  | 0, F => F
  | k + 1, F => ap2 (sumF (gsBody (gs (e + 1) k F))) (fstT (tl e (var 0))) (var 0)

theorem inst2_gsBody (G : PTm 1) (i x : PTm n) :
    inst2 (gsBody G) i x = Syn.subst ![pairT i x] G := by
  simp only [inst2, gsBody, Syn.subst_subst]
  congr 1; funext j; fin_cases j; simp

/-- One level of the grid sum. -/
theorem gs_succ (e k : ℕ) (F : PTm 1) (x : PTm n) :
    Syn.subst ![x] (gs e (k + 1) F) = ap2 (sumF (gsBody (gs (e + 1) k F))) (fstT (tl e x)) x := by
  simp [gs]

/-- The bound read at depth `e + 1` inside the body is the bound at depth `e`. -/
theorem gs_bound {Γ : List (Fm PTm n)} (e : ℕ) (i x : PTm n) :
    Γ ⊢[PRAAx] fstT (tl (e + 1) (pairT i x)) ≐ fstT (tl e x) := congrFst (tl_pair_succ e i x)

/-- Grid sums of summands that agree at every argument agree. -/
theorem gs_congr {F G : PTm 1}
    (H : ∀ (m : ℕ) (Δ : List (Fm PTm m)) (x : PTm m), Δ ⊢[PRAAx] Syn.subst ![x] F ≐ Syn.subst ![x] G) :
    ∀ (e k : ℕ) (m : ℕ) (Δ : List (Fm PTm m)) (x : PTm m),
      Δ ⊢[PRAAx] Syn.subst ![x] (gs e k F) ≐ Syn.subst ![x] (gs e k G)
  | _, 0, m, Δ, x => H m Δ x
  | e, k + 1, m, Δ, x => by
    rw [gs_succ, gs_succ]
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_gsBody, inst2_gsBody]
    exact gs_congr H (e + 1) k _ _ _

/-- The grid sum of `F + G` is the sum of the grid sums. -/
theorem gs_add (F G : PTm 1) :
    ∀ (e k : ℕ) (m : ℕ) (Δ : List (Fm PTm m)) (x : PTm m),
      Δ ⊢[PRAAx] Syn.subst ![x] (gs e k (F + G)) ≐ Syn.subst ![x] (gs e k F) + Syn.subst ![x] (gs e k G)
  | _, 0, _, _, _ => by simp only [gs, PTm.subst_add]; exact .eqRefl _
  | e, k + 1, m, Δ, x => by
    rw [gs_succ, gs_succ, gs_succ]
    refine (sum_congr_bounded _ (addBody (gsBody (gs (e + 1) k F)) (gsBody (gs (e + 1) k G))) _ _ _
      (.allI (.impI ?_))).eqTrans (sum_add _ _ _ _)
    rw [inst2_gsBody, inst2_addBody, inst2_gsBody, inst2_gsBody]
    exact gs_add F G (e + 1) k _ _ _

/-! ## Summands read through a list map -/

/-- The summand `F` read at the list `T`, a term in the list variable. -/
def comp (F T : PTm 1) : PTm 1 := Syn.subst ![T] F

theorem subst_comp (F T : PTm 1) (y : PTm n) :
    Syn.subst ![y] (comp F T) = Syn.subst ![Syn.subst ![y] T] F := by
  simp only [comp, Syn.subst_subst]
  congr 1; funext j; fin_cases j; rfl

/-- A summand is a congruence in its list variable. -/
theorem congr1 {Γ : List (Fm PTm n)} (F : PTm 1) {y y' : PTm n} (h : Γ ⊢[PRAAx] y ≐ y') :
    Γ ⊢[PRAAx] Syn.subst ![y] F ≐ Syn.subst ![y'] F :=
  Prf.eqCongr F (σ := ![y]) (σ' := ![y']) (fun j => by fin_cases j; exact h)

/-- The grid sum of `gs e 0 F` is the summand itself. -/
theorem gs_zero_levels (e : ℕ) (F : PTm 1) : gs e 0 F = F := rfl

/-- `gs e (j + k) F = gs e j (gs (e + j) k F)`. -/
theorem gs_comp (F : PTm 1) : ∀ (j e k : ℕ), gs e (j + k) F = gs e j (gs (e + j) k F)
  | 0, e, k => by simp [gs]
  | j + 1, e, k => by
    rw [show j + 1 + k = (j + k) + 1 by omega]
    simp only [gs]
    rw [gs_comp F j (e + 1) k, show e + 1 + j = e + (j + 1) by omega]

/-- A summand that vanishes at every argument has a vanishing grid sum. -/
theorem gs_zero {F : PTm 1}
    (H : ∀ (m : ℕ) (Δ : List (Fm PTm m)) (x : PTm m), Δ ⊢[PRAAx] Syn.subst ![x] F ≐ zero) :
    ∀ (e k : ℕ) (m : ℕ) (Δ : List (Fm PTm m)) (x : PTm m), Δ ⊢[PRAAx] Syn.subst ![x] (gs e k F) ≐ zero
  | _, 0, m, Δ, x => H m Δ x
  | e, k + 1, m, Δ, x => by
    rw [gs_succ]
    refine (sum_congr_bounded _ (zero : PTm 2) x x _ (.allI (.impI ?_))).eqTrans (sum_zeroB _ x)
    rw [inst2_gsBody]
    have e₀ : inst2 (zero : PTm 2) (var 0) (Syn.shift x) = (zero : PTm (m + 1)) := by
      simp [inst2]
    rw [e₀]
    exact gs_zero H (e + 1) k _ _ _

/-! ## Incrementing one entry -/

/-- The list with entry `c` incremented. -/
def upd : ℕ → PTm n → PTm n
  | 0, x => pairT (succ (fstT x)) (sndT x)
  | c + 1, x => pairT (fstT x) (upd c (sndT x))

@[simp] theorem subst_upd {m : ℕ} (σ : Fin n → PTm m) :
    ∀ (c : ℕ) (x : PTm n), Syn.subst σ (upd c x) = upd c (Syn.subst σ x)
  | 0, x => by simp [upd]
  | c + 1, x => by simp [upd, subst_upd σ c]

theorem shift_upd (c : ℕ) (x : PTm n) : Syn.shift (upd c x) = upd c (Syn.shift x) := by
  simp [Syn.shift]

theorem congrUpd {Γ : List (Fm PTm n)} :
    ∀ (c : ℕ) {x x' : PTm n}, (Γ ⊢[PRAAx] x ≐ x') → (Γ ⊢[PRAAx] upd c x ≐ upd c x')
  | 0, _, _, h => congrPairT (congrSucc (congrFst h)) (congrSnd h)
  | c + 1, _, _, h => congrPairT (congrFst h) (congrUpd c (congrSnd h))

theorem upd_cons {Γ : List (Fm PTm n)} (c : ℕ) (j y : PTm n) :
    Γ ⊢[PRAAx] upd (c + 1) (pairT j y) ≐ pairT j (upd c y) :=
  congrPairT (fst_pair j y) (congrUpd c (snd_pair j y))

theorem upd_zero_pair {Γ : List (Fm PTm n)} (i y : PTm n) :
    Γ ⊢[PRAAx] upd 0 (pairT i y) ≐ pairT (succ i) y :=
  congrPairT (congrSucc (fst_pair i y)) (snd_pair i y)

theorem tl_upd {Γ : List (Fm PTm n)} :
    ∀ (c e : ℕ) (y : PTm n), c < e → (Γ ⊢[PRAAx] tl e (upd c y) ≐ tl e y)
  | _, 0, _, h => absurd h (Nat.not_lt_zero _)
  | 0, e + 1, y, _ => congrTl e (snd_pair _ _)
  | c + 1, e + 1, y, h => (congrTl e (snd_pair _ _)).eqTrans (tl_upd c e (sndT y) (by omega))

/-- Incrementing entry `c` of the list commutes with the inner sums; inside, the entry has `k`
more entries above it. -/
theorem gs_upd (F : PTm 1) :
    ∀ (k e c : ℕ) (m : ℕ) (Δ : List (Fm PTm m)) (y : PTm m), c < e →
      (Δ ⊢[PRAAx] Syn.subst ![upd c y] (gs e k F) ≐
        Syn.subst ![y] (gs e k (comp F (upd (c + k) (var 0)))))
  | 0, e, c, m, Δ, y, _ => by
    show Δ ⊢[PRAAx] Syn.subst ![upd c y] F ≐ Syn.subst ![y] (comp F (upd (c + 0) (var 0)))
    rw [subst_comp]
    simp only [subst_upd, Syn.subst_var, Matrix.cons_val_zero, Nat.add_zero]
    exact .eqRefl _
  | k + 1, e, c, m, Δ, y, hc => by
    rw [gs_succ, gs_succ]
    refine (congrAp2 _ (congrFst (tl_upd c e y hc)) (.eqRefl _)).eqTrans ?_
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_gsBody, inst2_gsBody, shift_upd]
    have h₁ := congr1 (gs (e + 1) k F) (upd_cons (Γ := lt (var 0) (Syn.shift (fstT (tl e y))) ::
      Δ.map Fm.shift) c (var 0) (Syn.shift y)).eqSymm
    have h₂ := gs_upd F k (e + 1) (c + 1) _ (lt (var 0) (Syn.shift (fstT (tl e y))) :: Δ.map Fm.shift)
      (pairT (var 0) (Syn.shift y)) (by omega)
    rw [show c + 1 + k = c + (k + 1) by omega] at h₂
    exact h₁.eqTrans h₂

/-- One level of telescoping: `∑_{i<N} H(i + 1) + H(0) = H(N) + ∑_{i<N} H(i)`, where `H(i)` is the
inner grid sum at the list `⟨i, x⟩` and the shifted sum is the grid sum of the summand with its
entry `k` incremented. -/
theorem gs_telescope (F : PTm 1) (e k : ℕ) {m : ℕ} (Δ : List (Fm PTm m)) (x : PTm m) :
    Δ ⊢[PRAAx] Syn.subst ![x] (gs e (k + 1) (comp F (upd k (var 0)))) +
        Syn.subst ![pairT zero x] (gs (e + 1) k F) ≐
      Syn.subst ![pairT (fstT (tl e x)) x] (gs (e + 1) k F) + Syn.subst ![x] (gs e (k + 1) F) := by
  rw [gs_succ, gs_succ]
  have hs : Δ ⊢[PRAAx] ap2 (sumF (gsBody (gs (e + 1) k (comp F (upd k (var 0)))))) (fstT (tl e x)) x ≐
      ap2 (sumF (shiftBody (gsBody (gs (e + 1) k F)))) (fstT (tl e x)) x := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_gsBody, inst2_shiftBody, inst2_gsBody]
    have h₂ := gs_upd F k (e + 1) 0 _ (lt (var 0) (Syn.shift (fstT (tl e x))) :: Δ.map Fm.shift)
      (pairT (var 0) (Syn.shift x)) (by omega)
    rw [Nat.zero_add] at h₂
    exact h₂.eqSymm.eqTrans (congr1 _ (upd_zero_pair _ _))
  have e₂ := natEq (sum_shift (Γ := Δ) (gsBody (gs (e + 1) k F)) (fstT (tl e x)) x)
  have e₃ := natEq (sum_succ' (Γ := Δ) (gsBody (gs (e + 1) k F)) (fstT (tl e x)) x)
  rw [inst2_gsBody] at e₂ e₃
  ipra_lc natEq hs - e₂ + e₃

/-! ## Setting one entry -/

/-- The list with entry `c` set to `u`. -/
def setE : ℕ → PTm n → PTm n → PTm n
  | 0, u, x => pairT u (sndT x)
  | c + 1, u, x => pairT (fstT x) (setE c u (sndT x))

@[simp] theorem subst_setE {m : ℕ} (σ : Fin n → PTm m) :
    ∀ (c : ℕ) (u x : PTm n), Syn.subst σ (setE c u x) = setE c (Syn.subst σ u) (Syn.subst σ x)
  | 0, u, x => by simp [setE]
  | c + 1, u, x => by simp [setE, subst_setE σ c]

theorem shift_setE (c : ℕ) (u x : PTm n) :
    Syn.shift (setE c u x) = setE c (Syn.shift u) (Syn.shift x) := by
  simp [Syn.shift]

theorem congrSetE {Γ : List (Fm PTm n)} :
    ∀ (c : ℕ) {u u' x x' : PTm n}, (Γ ⊢[PRAAx] u ≐ u') → (Γ ⊢[PRAAx] x ≐ x') →
      (Γ ⊢[PRAAx] setE c u x ≐ setE c u' x')
  | 0, _, _, _, _, hu, hx => congrPairT hu (congrSnd hx)
  | c + 1, _, _, _, _, hu, hx => congrPairT (congrFst hx) (congrSetE c hu (congrSnd hx))

theorem setE_cons {Γ : List (Fm PTm n)} (c : ℕ) (u j y : PTm n) :
    Γ ⊢[PRAAx] setE (c + 1) u (pairT j y) ≐ pairT j (setE c u y) :=
  congrPairT (fst_pair j y) (congrSetE c (.eqRefl u) (snd_pair j y))

theorem setE_idem {Γ : List (Fm PTm n)} :
    ∀ (c : ℕ) (u y : PTm n), Γ ⊢[PRAAx] setE c u (setE c u y) ≐ setE c u y
  | 0, u, _ => congrPairT (.eqRefl u) (snd_pair u _)
  | c + 1, u, y => congrPairT (fst_pair _ _)
      ((congrSetE c (.eqRefl u) (snd_pair _ _)).eqTrans (setE_idem c u (sndT y)))

theorem tl_setE {Γ : List (Fm PTm n)} :
    ∀ (c e : ℕ) (u y : PTm n), c < e → (Γ ⊢[PRAAx] tl e (setE c u y) ≐ tl e y)
  | _, 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | 0, e + 1, _, y, _ => congrTl e (snd_pair _ _)
  | c + 1, e + 1, u, y, h => (congrTl e (snd_pair _ _)).eqTrans (tl_setE c e u (sndT y) (by omega))

/-- Setting entry `c` to `0` commutes with the inner sums. -/
theorem gs_set0 (F : PTm 1) :
    ∀ (k e c : ℕ) (m : ℕ) (Δ : List (Fm PTm m)) (y : PTm m),
      Δ ⊢[PRAAx] Syn.subst ![setE c zero y] (gs e k F) ≐
        Syn.subst ![setE c zero y] (gs e k (comp F (setE (c + k) zero (var 0))))
  | 0, e, c, m, Δ, y => by
    show Δ ⊢[PRAAx] Syn.subst ![setE c zero y] F ≐
      Syn.subst ![setE c zero y] (comp F (setE (c + 0) zero (var 0)))
    rw [subst_comp]
    simp only [subst_setE, Syn.subst_var, Matrix.cons_val_zero, Nat.add_zero,
      ConciseIPRA.PTm.subst_zero]
    exact congr1 F (setE_idem c zero y).eqSymm
  | k + 1, e, c, m, Δ, y => by
    rw [gs_succ, gs_succ]
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_gsBody, inst2_gsBody, shift_setE]
    have z : Syn.shift (zero : PTm m) = zero := by simp [Syn.shift]
    rw [z]
    have h₁ := congr1 (gs (e + 1) k F) (setE_cons (Γ := lt (var 0) (Syn.shift (fstT (tl e (setE c zero y)))) ::
      Δ.map Fm.shift) c zero (var 0) (Syn.shift y)).eqSymm
    have h₁' := congr1 (gs (e + 1) k (comp F (setE (c + (k + 1)) zero (var 0))))
      (setE_cons (Γ := lt (var 0) (Syn.shift (fstT (tl e (setE c zero y)))) :: Δ.map Fm.shift)
        c zero (var 0) (Syn.shift y)).eqSymm
    have h₂ := gs_set0 F k (e + 1) (c + 1) _
      (lt (var 0) (Syn.shift (fstT (tl e (setE c zero y)))) :: Δ.map Fm.shift) (pairT (var 0) (Syn.shift y))
    rw [show c + 1 + k = c + (k + 1) by omega] at h₂
    exact h₁.eqTrans (h₂.eqTrans h₁'.eqSymm)

/-! ## Telescoping along one coordinate of the grid -/

/-- The lower face of coordinate `k` (outer depth `j`): the inner sums at the list `⟨0, x⟩`. -/
def face0 (F : PTm 1) (j k : ℕ) : PTm 1 := Syn.subst ![pairT zero (var 0)] (gs (j + 1) k F)

/-- The upper face of coordinate `k` (outer depth `j`): the inner sums at the list `⟨N, x⟩`. -/
def faceN (F : PTm 1) (j k : ℕ) : PTm 1 := Syn.subst ![pairT (fstT (tl j (var 0))) (var 0)] (gs (j + 1) k F)

theorem subst_face0 (F : PTm 1) (j k : ℕ) (x : PTm n) :
    Syn.subst ![x] (face0 F j k) = Syn.subst ![pairT zero x] (gs (j + 1) k F) := by
  simp only [face0, Syn.subst_subst]
  congr 1; funext i; fin_cases i; simp

theorem subst_faceN (F : PTm 1) (j k : ℕ) (x : PTm n) :
    Syn.subst ![x] (faceN F j k) = Syn.subst ![pairT (fstT (tl j x)) x] (gs (j + 1) k F) := by
  simp only [faceN, Syn.subst_subst]
  congr 1; funext i; fin_cases i; simp

/-- Telescoping along coordinate `k` of a grid of dimension `j + (k + 1)`:
`∑ F(a + e_k) + ∑_{face a_k = 0} F = ∑_{face a_k = N} F + ∑ F`. -/
theorem grid_telescope (F : PTm 1) (j k : ℕ) {m : ℕ} (Δ : List (Fm PTm m)) (x : PTm m) :
    Δ ⊢[PRAAx] Syn.subst ![x] (gs 0 (j + (k + 1)) (comp F (upd k (var 0)))) +
        Syn.subst ![x] (gs 0 j (face0 F j k)) ≐
      Syn.subst ![x] (gs 0 j (faceN F j k)) + Syn.subst ![x] (gs 0 (j + (k + 1)) F) := by
  rw [gs_comp _ j 0 (k + 1), gs_comp F j 0 (k + 1), Nat.zero_add]
  have pt : ∀ (m' : ℕ) (Δ' : List (Fm PTm m')) (x' : PTm m'),
      Δ' ⊢[PRAAx] Syn.subst ![x'] (gs j (k + 1) (comp F (upd k (var 0))) + face0 F j k) ≐
        Syn.subst ![x'] (faceN F j k + gs j (k + 1) F) := by
    intro m' Δ' x'
    simp only [PTm.subst_add, subst_face0, subst_faceN]
    exact gs_telescope F j k Δ' x'
  have h := gs_congr pt 0 j m Δ x
  exact (gs_add _ _ 0 j m Δ x).eqSymm.eqTrans (h.eqTrans (gs_add _ _ 0 j m Δ x))

/-- The lower face of coordinate `k` vanishes when the summand vanishes whenever entry `k` is
`0`. -/
theorem face0_vanish {F : PTm 1} (j k : ℕ)
    (H : ∀ (m : ℕ) (Δ : List (Fm PTm m)) (y : PTm m), Δ ⊢[PRAAx] Syn.subst ![setE k zero y] F ≐ zero)
    {m : ℕ} (Δ : List (Fm PTm m)) (x : PTm m) :
    Δ ⊢[PRAAx] Syn.subst ![x] (gs 0 j (face0 F j k)) ≐ zero := by
  refine gs_zero (fun m' Δ' x' => ?_) 0 j m Δ x
  rw [subst_face0]
  have h₀ : Δ' ⊢[PRAAx] pairT zero x' ≐ setE 0 zero (pairT zero x') :=
    (congrPairT (.eqRefl zero) (snd_pair zero x')).eqSymm
  refine (congr1 _ h₀).eqTrans ((gs_set0 F k (j + 1) 0 m' Δ' (pairT zero x')).eqTrans ?_)
  refine gs_zero (fun m'' Δ'' y => ?_) (j + 1) k m' Δ' _
  rw [subst_comp]
  simp only [subst_setE, Syn.subst_var, Matrix.cons_val_zero, Nat.zero_add, ConciseIPRA.PTm.subst_zero]
  exact H m'' Δ'' y

end LeanProofs.IPRA.Foundations.GridSums
