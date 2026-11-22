import IPRADerivations.Foundations.GridSums
import IPRADerivations.Foundations.TermSums

/-!
# Grid sums with information carried into the inner sums

A reusable piece of the embedding framework, extending `Foundations/GridSums`. The congruence
`gs_congr` there needs summands that agree at every argument in every context. Here the summands
need only agree at the lists that actually occur, in the contexts that actually occur:

* `gs_congr_gen`: for any family `P e Δ x` of facts about a list `x` of depth `e` in context `Δ`
  that is preserved by one summation level (`hstep`: from `x` to `⟨i, x⟩` under the hypothesis
  `i < N`), summands that agree whenever `P` holds at full depth have equal grid sums whenever `P`
  holds at the start. Typical facts: hypotheses of the theorem (shifted), the base of the list, and
  bounds on the entries;
* `gs_zero_gen`: the same for a vanishing summand;
* `face0_gen`, `faceN_gen`: the face sums of `GridSums.grid_telescope` vanish when the summand
  vanishes at the lists of the face, with the face value (`0` or `N`) recorded by `P`;
* `mk_gs_lsum`, `mk_gs_fsum`, `mk_gs_ftsum`, `mk_gs_two`: the grid sum is additive over finite sums
  indexed in the metatheory (`Foundations/TermSums`), as identities in the quotient semiring.
-/


set_option autoImplicit false

namespace LeanProofs.IPRA.Foundations.GridSumsContext

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm BigOperators
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)
open LeanProofs.IPRA.Foundations.GridSums
open LeanProofs.IPRA.Foundations.TermSums

/-- A family of facts about a list of depth `e` in a context. -/
abbrev ListFacts := ℕ → (m : ℕ) → List (Fm PTm m) → PTm m → Prop

/-- The facts are preserved by one summation level, at the depths `lo ≤ e < hi`. -/
def Steps (P : ListFacts) (lo hi : ℕ) : Prop :=
  ∀ (e : ℕ), lo ≤ e → e < hi → ∀ (m : ℕ) (Δ : List (Fm PTm m)) (x : PTm m), P e m Δ x →
    P (e + 1) (m + 1) (lt (var 0) (Syn.shift (fstT (tl e x))) :: Δ.map Fm.shift) (pairT (var 0) (Syn.shift x))

/-- Summands that agree wherever the facts hold at full depth have equal grid sums. -/
theorem gs_congr_gen {P : ListFacts} {lo D : ℕ} (hP : Steps P lo D) {F G : PTm 1}
    (H : ∀ (m : ℕ) (Δ : List (Fm PTm m)) (x : PTm m), P D m Δ x →
      (Δ ⊢[PRAAx] Syn.subst ![x] F ≐ Syn.subst ![x] G)) :
    ∀ (k e : ℕ), e + k = D → lo ≤ e → ∀ (m : ℕ) (Δ : List (Fm PTm m)) (x : PTm m), P e m Δ x →
      (Δ ⊢[PRAAx] Syn.subst ![x] (gs e k F) ≐ Syn.subst ![x] (gs e k G))
  | 0, e, he, _, m, Δ, x, hx => by
    have : e = D := by omega
    subst this
    exact H m Δ x hx
  | k + 1, e, he, hlo, m, Δ, x, hx => by
    rw [gs_succ, gs_succ]
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_gsBody, inst2_gsBody]
    exact gs_congr_gen hP H k (e + 1) (by omega) (by omega) _ _ _ (hP e hlo (by omega) m Δ x hx)

/-- The grid sum of the zero summand vanishes. -/
theorem gs_zero_term (e k : ℕ) {m : ℕ} (Δ : List (Fm PTm m)) (x : PTm m) :
    Δ ⊢[PRAAx] Syn.subst ![x] (gs e k (zero : PTm 1)) ≐ zero :=
  gs_zero (fun _ _ _ => by simp; exact .eqRefl _) e k m Δ x

/-- A summand that vanishes wherever the facts hold at full depth has a vanishing grid sum. -/
theorem gs_zero_gen {P : ListFacts} {lo D : ℕ} (hP : Steps P lo D) {F : PTm 1}
    (H : ∀ (m : ℕ) (Δ : List (Fm PTm m)) (x : PTm m), P D m Δ x →
      (Δ ⊢[PRAAx] Syn.subst ![x] F ≐ zero))
    (k e : ℕ) (he : e + k = D) (hlo : lo ≤ e) {m : ℕ} (Δ : List (Fm PTm m)) (x : PTm m)
    (hx : P e m Δ x) : Δ ⊢[PRAAx] Syn.subst ![x] (gs e k F) ≐ zero :=
  (gs_congr_gen hP (G := zero) (fun m Δ x h => by simpa using H m Δ x h) k e he hlo m Δ x hx).eqTrans
    (gs_zero_term e k Δ x)

/-- The lower face of coordinate `k` vanishes when the summand vanishes at the lists of the face;
`hface` records the face value `0` in the facts. The summation levels outside the face are the
depths `e < j` and `j < e < j + 1 + k`. -/
theorem face0_gen {P : ListFacts} {F : PTm 1} (j k : ℕ) (hout : Steps P 0 j)
    (hin : Steps P (j + 1) (j + 1 + k))
    (hface : ∀ (m : ℕ) (Δ : List (Fm PTm m)) (x : PTm m), P j m Δ x → P (j + 1) m Δ (pairT zero x))
    (H : ∀ (m : ℕ) (Δ : List (Fm PTm m)) (x : PTm m), P (j + 1 + k) m Δ x →
      (Δ ⊢[PRAAx] Syn.subst ![x] F ≐ zero))
    {m : ℕ} (Δ : List (Fm PTm m)) (x : PTm m) (hx : P 0 m Δ x) :
    Δ ⊢[PRAAx] Syn.subst ![x] (gs 0 j (face0 F j k)) ≐ zero :=
  gs_zero_gen hout (fun m' Δ' x' h => by
      rw [subst_face0]
      exact gs_zero_gen hin H k (j + 1) rfl le_rfl Δ' _ (hface m' Δ' x' h))
    j 0 (by omega) le_rfl Δ x hx

/-- The upper face of coordinate `k` vanishes when the summand vanishes at the lists of the face;
`hface` records the face value `N` in the facts. -/
theorem faceN_gen {P : ListFacts} {F : PTm 1} (j k : ℕ) (hout : Steps P 0 j)
    (hin : Steps P (j + 1) (j + 1 + k))
    (hface : ∀ (m : ℕ) (Δ : List (Fm PTm m)) (x : PTm m), P j m Δ x →
      P (j + 1) m Δ (pairT (fstT (tl j x)) x))
    (H : ∀ (m : ℕ) (Δ : List (Fm PTm m)) (x : PTm m), P (j + 1 + k) m Δ x →
      (Δ ⊢[PRAAx] Syn.subst ![x] F ≐ zero))
    {m : ℕ} (Δ : List (Fm PTm m)) (x : PTm m) (hx : P 0 m Δ x) :
    Δ ⊢[PRAAx] Syn.subst ![x] (gs 0 j (faceN F j k)) ≐ zero :=
  gs_zero_gen hout (fun m' Δ' x' h => by
      rw [subst_faceN]
      exact gs_zero_gen hin H k (j + 1) rfl le_rfl Δ' _ (hface m' Δ' x' h))
    j 0 (by omega) le_rfl Δ x hx

/-- The lower face of the top coordinate: the inner part is the summand at `⟨0, x⟩`. -/
theorem face0_congr_gen {P : ListFacts} {F G : PTm 1} (j : ℕ) (hout : Steps P 0 j)
    (H : ∀ (m : ℕ) (Δ : List (Fm PTm m)) (x : PTm m), P j m Δ x →
      (Δ ⊢[PRAAx] Syn.subst ![pairT zero x] F ≐ Syn.subst ![x] G))
    {m : ℕ} (Δ : List (Fm PTm m)) (x : PTm m) (hx : P 0 m Δ x) :
    Δ ⊢[PRAAx] Syn.subst ![x] (gs 0 j (face0 F j 0)) ≐ Syn.subst ![x] (gs 0 j G) :=
  gs_congr_gen hout (fun m' Δ' x' h => by rw [subst_face0]; exact H m' Δ' x' h) j 0 (by omega) le_rfl
    m Δ x hx

/-! ## Additivity over finite sums of summands -/

section Additive

variable {m : ℕ} (Δ : List (Fm PTm m)) (x : PTm m)

theorem mk_gs_lsum (e k : ℕ) :
    ∀ l : List (PTm 1), Q.mk Δ (Syn.subst ![x] (gs e k (lsum l))) =
      (l.map (fun F => Q.mk Δ (Syn.subst ![x] (gs e k F)))).sum
  | [] => by simp only [lsum, List.map_nil, List.sum_nil]; rw [Q.sound (gs_zero_term e k Δ x), Q.mk_zero]
  | F :: l => by
    simp only [lsum, List.map_cons, List.sum_cons]
    rw [Q.sound (gs_add F (lsum l) e k m Δ x), Q.mk_add, mk_gs_lsum e k l]

theorem mk_gs_fsum (e k r : ℕ) (f : Fin r → PTm 1) :
    Q.mk Δ (Syn.subst ![x] (gs e k (fsum r f))) = ∑ i, Q.mk Δ (Syn.subst ![x] (gs e k (f i))) := by
  rw [fsum, mk_gs_lsum, List.map_ofFn, List.sum_ofFn]; rfl

theorem mk_gs_ftsum {ι : Type} [Fintype ι] (e k : ℕ) (f : ι → PTm 1) :
    Q.mk Δ (Syn.subst ![x] (gs e k (ftsum f))) = ∑ i, Q.mk Δ (Syn.subst ![x] (gs e k (f i))) := by
  rw [ftsum, mk_gs_lsum, List.map_map]
  exact Finset.sum_map_toList _ _

theorem mk_gs_two (e k : ℕ) (F : PTm 1) :
    Q.mk Δ (Syn.subst ![x] (gs e k (two * F))) = 2 * Q.mk Δ (Syn.subst ![x] (gs e k F)) := by
  have h₁ := gs_congr (F := two * F) (G := F + F) (fun m' Δ' y => by
    apply of_mk; simp only [PTm.subst_mul, PTm.subst_add, Q.mk_mul, Q.mk_add]
    rw [show Syn.subst ![y] (two : PTm 1) = two by simp, mk_two]; ring) e k m Δ x
  rw [Q.sound h₁, Q.sound (gs_add F F e k m Δ x), Q.mk_add]; ring

end Additive

end LeanProofs.IPRA.Foundations.GridSumsContext
