import GowersSzemeredi.Proofs16ClaimNineFour
import GowersSzemeredi.Proofs16CommonValueSharp

/-! Milićević's Claim 9.5 in `ℤ/N` (arXiv:2601.01682, printed p. 67), the
12-tuple version of Claim 9.4.

**Coordinates.** A 12-tuple `(x[4], y[4], a[4])` with `a₀ + a₁ = a₂ + a₃` is
stored by its eleven free coordinates `u : Fin 11 → ZMod N`:
* `x_j = u_j` and `y_j = u_{4+j}`;
* `a_0 = u_8`, `a_1 = u_9`, `a_2 = u_10`, and `a_3 = u_8 + u_9 − u_10`.

These are `twelveX`, `twelveY` and `twelveA`. For each `j`,
`twelveRest j u : Fin 9 → ZMod N` keeps the nine coordinates other than
`x_j` and one `a`-coordinate. `a_j` and `twelveRest j u` together determine
`u` off `x_j` (`twelve_agree_off`), and this is checked by `decide`.

**The claim** (`claim_9_5`). Prescribe frequencies `ξ_{j,k}` in the span
balls at the 16 points `x_j + a_j, x_j, y_j + a_j, y_j`, with
`∑_j (ξ_{j,0} − ξ_{j,1}) = ∑_j (ξ_{j,2} − ξ_{j,3})`, such that some
`ξ_{j,0} − ξ_{j,1}` avoids the forbidden set `S(x_j, a_j)`.
1. Select 16 maps, by the `n`-point version of the selection lemma
   (`exists_good_selection_indexed_le`), at a loss `K^(−16)`.
2. Pigeonhole a coordinate `j` that escapes on a quarter of the tuples.
3. On those tuples `F_j(x_j, a_j) = ∑_k G_k − ∑_{k≠j} F_k` is determined
   by `(a_j, twelveRest j u)`. So `exists_common_value_det`, with the
   sharp bound `|A|·|X|·|Y| = N·N·N⁹`, gives `Θ(a_j)`.
4. `freiman_common_value` finishes as in Claim 9.4.

The output has exactly the shape of `claim_9_4`'s output, so the
iteration can append `Θ` in either case. Milićević's version applies
Lemma 9.2 to all 16 maps. Here only one coordinate needs a common value,
because a sum of forbidden elements is excluded only if some summand
escapes. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

section Selection
variable {X Y : Type} [Fintype X] [DecidableEq X] [DecidableEq Y]

/-- **Selection averaging with `n` fixed points per requirement.** -/
theorem exists_good_selection_indexed_le (U : X → Finset Y) (hne : ∀ x, (U x).Nonempty)
    {K n : Nat} (hK1 : 1 ≤ K) (hK : ∀ x, (U x).card ≤ K) {ι : Type*} (Tr : Finset ι)
    (req : ι → Finset X × (X → Y))
    (hT : ∀ t ∈ Tr, (req t).1.card ≤ n ∧ ∀ x ∈ (req t).1, (req t).2 x ∈ U x) :
    ∃ f ∈ Fintype.piFinset U, Tr.card ≤ K ^ n * (Tr.filter fun t => Meets f (req t)).card := by
  set F := Fintype.piFinset U
  have hFpos : 0 < F.card := by
    rw [Fintype.card_piFinset]
    exact Finset.prod_pos fun x _ => (hne x).card_pos
  have hreq : ∀ t ∈ Tr, F.card ≤ K ^ n * (F.filter fun f => Meets f (req t)).card := by
    intro t ht
    obtain ⟨hS, hv⟩ := hT t ht
    calc F.card ≤ K ^ (req t).1.card * (F.filter fun f => Meets f (req t)).card :=
          card_all_le_mul_meeting U hK (req t) hv
      _ ≤ K ^ n * (F.filter fun f => Meets f (req t)).card :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hK1 hS)
  have hdouble : ∑ f ∈ F, (Tr.filter fun t => Meets f (req t)).card =
      ∑ t ∈ Tr, (F.filter fun f => Meets f (req t)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  by_contra hcon
  push Not at hcon
  have hlt : K ^ n * ∑ f ∈ F, (Tr.filter fun t => Meets f (req t)).card < F.card * Tr.card := by
    rw [Finset.mul_sum]
    calc ∑ f ∈ F, K ^ n * (Tr.filter fun t => Meets f (req t)).card
        < ∑ _f ∈ F, Tr.card := Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp hFpos)
          fun f hf => hcon f hf
      _ = F.card * Tr.card := by rw [Finset.sum_const, smul_eq_mul]
  have hge : F.card * Tr.card ≤ K ^ n * ∑ t ∈ Tr, (F.filter fun f => Meets f (req t)).card := by
    rw [Finset.mul_sum]
    calc F.card * Tr.card = ∑ _t ∈ Tr, F.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ t ∈ Tr, K ^ n * (F.filter fun f => Meets f (req t)).card := Finset.sum_le_sum hreq
  rw [hdouble] at hlt
  omega

end Selection

/-- The coordinate index of `x_j`. -/
def twelveXIndex : Fin 4 → Fin 11 := ![0, 1, 2, 3]

/-- The coordinate index of `y_j`. -/
def twelveYIndex : Fin 4 → Fin 11 := ![4, 5, 6, 7]

/-- `x_j` of a 12-tuple. -/
def twelveX {N : Nat} (u : Fin 11 → ZMod N) (j : Fin 4) : ZMod N := u (twelveXIndex j)

/-- `y_j` of a 12-tuple. -/
def twelveY {N : Nat} (u : Fin 11 → ZMod N) (j : Fin 4) : ZMod N := u (twelveYIndex j)

/-- `a_j` of a 12-tuple; `a₃ = a₀ + a₁ − a₂`. -/
def twelveA {N : Nat} (u : Fin 11 → ZMod N) (j : Fin 4) : ZMod N :=
  ![u 8, u 9, u 10, u 8 + u 9 - u 10] j

theorem twelveA_relation {N : Nat} (u : Fin 11 → ZMod N) :
    twelveA u 0 + twelveA u 1 = twelveA u 2 + twelveA u 3 := by
  simp only [twelveA, Matrix.cons_val]
  ring

/-- The nine coordinates kept for the common value at `j`. -/
def twelveRestIndex : Fin 4 → Fin 9 → Fin 11 :=
  ![![1, 2, 3, 4, 5, 6, 7, 9, 10], ![0, 2, 3, 4, 5, 6, 7, 8, 10],
    ![0, 1, 3, 4, 5, 6, 7, 8, 9], ![0, 1, 2, 4, 5, 6, 7, 9, 10]]

/-- The coordinate other than `x_j` that `twelveRest j` drops. -/
def twelveDropped : Fin 4 → Fin 11 := ![8, 9, 10, 8]

def twelveRest {N : Nat} (j : Fin 4) (u : Fin 11 → ZMod N) : Fin 9 → ZMod N :=
  fun m => u (twelveRestIndex j m)

theorem twelveRestIndex_cover : ∀ j : Fin 4, ∀ k : Fin 11, k ≠ twelveXIndex j →
    k ≠ twelveDropped j → ∃ m, twelveRestIndex j m = k := by
  decide

theorem twelveXIndex_ne : ∀ j k : Fin 4, k ≠ j → twelveXIndex k ≠ twelveXIndex j := by
  decide

theorem twelveYIndex_ne : ∀ j k : Fin 4, twelveYIndex k ≠ twelveXIndex j := by
  decide

theorem twelve_high_ne : ∀ j : Fin 4,
    (8 : Fin 11) ≠ twelveXIndex j ∧ (9 : Fin 11) ≠ twelveXIndex j ∧
      (10 : Fin 11) ≠ twelveXIndex j := by
  decide

/-- `a_j` and the kept coordinates determine the tuple off `x_j`. -/
theorem twelve_agree_off {N : Nat} {j : Fin 4} {u u' : Fin 11 → ZMod N}
    (ha : twelveA u j = twelveA u' j) (hr : twelveRest j u = twelveRest j u') :
    ∀ k : Fin 11, k ≠ twelveXIndex j → u k = u' k := by
  have hkept : ∀ k : Fin 11, k ≠ twelveXIndex j → k ≠ twelveDropped j → u k = u' k := by
    intro k hk hk'
    obtain ⟨m, rfl⟩ := twelveRestIndex_cover j k hk hk'
    exact congrFun hr m
  intro k hk
  by_cases hk' : k = twelveDropped j
  · subst hk'
    fin_cases j
    · simpa [twelveA, twelveDropped] using ha
    · simpa [twelveA, twelveDropped] using ha
    · simpa [twelveA, twelveDropped] using ha
    · have h9 := hkept 9 (by decide) (by decide)
      have h10 := hkept 10 (by decide) (by decide)
      have ha' : u 8 + u 9 - u 10 = u' 8 + u' 9 - u' 10 := ha
      show u 8 = u' 8
      rw [h9, h10] at ha'
      linear_combination ha'
  · exact hkept k hk hk'

/-- Agreement off `x_j` preserves every other coordinate. -/
theorem twelve_coords_of_agree {N : Nat} {j : Fin 4} {u u' : Fin 11 → ZMod N}
    (h : ∀ k : Fin 11, k ≠ twelveXIndex j → u k = u' k) :
    (∀ k, k ≠ j → twelveX u k = twelveX u' k) ∧ (∀ k, twelveY u k = twelveY u' k) ∧
      (∀ k, twelveA u k = twelveA u' k) := by
  obtain ⟨h8, h9, h10⟩ := twelve_high_ne j
  refine ⟨fun k hk => h _ (twelveXIndex_ne j k hk), fun k => h _ (twelveYIndex_ne j k),
    fun k => ?_⟩
  have e8 := h 8 h8
  have e9 := h 9 h9
  have e10 := h 10 h10
  fin_cases k <;> simp [twelveA, e8, e9, e10]

/-- The 16 points of a 12-tuple: `x_j + a_j, x_j, y_j + a_j, y_j`. -/
def twelvePoint {N : Nat} (u : Fin 11 → ZMod N) (j k : Fin 4) : ZMod N :=
  ![twelveX u j + twelveA u j, twelveX u j, twelveY u j + twelveA u j, twelveY u j] k

/-- The pair density of Claim 9.5: `κ(c/2)²` with `c = (ε/(4K¹⁶))²`. -/
def claimNineFiveDensity (ε : Real) (R d : Nat) : Real :=
  let c := (ε / (4 * (((2 * R + 1) ^ d : Nat) : Real) ^ 16)) ^ 2
  (2 : Real) ^ (-(1882 : Real)) * ((c / 2) ^ 4) ^ 1164 * (c / 2) ^ 2

/-- **Claim 9.5.** -/
theorem claim_9_5 {N : Nat} [NeZero N] [Fact N.Prime] (Γ : ZMod N → Finset (ZMod N))
    {d R : Nat} (hΓ : ∀ z, (Γ z).card ≤ d) (Tr : Finset (Fin 11 → ZMod N))
    (ξ : (Fin 11 → ZMod N) → Fin 4 → Fin 4 → ZMod N)
    (hξ : ∀ u ∈ Tr, ∀ j k, ξ u j k ∈ spanBall (Γ (twelvePoint u j k)) R)
    (hdec : ∀ u ∈ Tr, ∑ j, (ξ u j 0 - ξ u j 1) = ∑ j, (ξ u j 2 - ξ u j 3))
    (S : ZMod N → ZMod N → Finset (ZMod N))
    (hS : ∀ u ∈ Tr, ∃ j, ξ u j 0 - ξ u j 1 ∉ S (twelveX u j) (twelveA u j))
    {ε : Real} (hε : 0 < ε) (hTr : ε * (N : Real) ^ 11 ≤ Tr.card) :
    ∃ (Θ : ZMod N → ZMod N) (B : Finset (ZMod N)) (P : Finset (ZMod N × ZMod N)),
      FreimanHom 8 B Θ ∧ claimNineFiveDensity ε R d * (N : Real) ^ 2 ≤ P.card ∧
      ∀ p ∈ P, p.2 ∈ B ∧ Θ p.2 ∈ spanBall (Γ (p.1 + p.2) ∪ Γ p.1) (2 * R) ∧
        Θ p.2 ∉ S p.1 p.2 := by
  set K := (2 * R + 1) ^ d with hKdef
  have hKpos : 0 < K := Nat.pos_of_ne_zero (by positivity)
  have hNpos : (0 : Real) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  -- 1. selection of sixteen maps
  let U : Fin 4 × Fin 4 × ZMod N → Finset (ZMod N) := fun p => spanBall (Γ p.2.2) R
  have hne : ∀ p, (U p).Nonempty := fun p => ⟨0, zero_mem_spanBall _ _⟩
  have hK : ∀ p, (U p).card ≤ K := fun p =>
    (spanBall_card_le _ _).trans (Nat.pow_le_pow_right (by omega) (hΓ p.2.2))
  let req : (Fin 11 → ZMod N) → Finset (Fin 4 × Fin 4 × ZMod N) ×
      (Fin 4 × Fin 4 × ZMod N → ZMod N) := fun u =>
    ((Finset.univ : Finset (Fin 4 × Fin 4)).image fun jk => (jk.1, jk.2, twelvePoint u jk.1 jk.2),
      fun p => ξ u p.1 p.2.1)
  have hT : ∀ u ∈ Tr, (req u).1.card ≤ 16 ∧ ∀ p ∈ (req u).1, (req u).2 p ∈ U p := by
    intro u hu
    refine ⟨Finset.card_image_le.trans (by simp), ?_⟩
    intro p hp
    obtain ⟨jk, -, rfl⟩ := Finset.mem_image.mp hp
    exact hξ u hu jk.1 jk.2
  obtain ⟨f, hfmem, hf⟩ :=
    exists_good_selection_indexed_le U hne (Nat.one_le_pow _ _ (by omega)) hK Tr req hT
  let ψ : Fin 4 → Fin 4 → ZMod N → ZMod N := fun j k z => f (j, k, z)
  have hψ : ∀ j k z, ψ j k z ∈ spanBall (Γ z) R := fun j k z =>
    Fintype.mem_piFinset.mp hfmem (j, k, z)
  let E := Tr.filter fun u => Meets f (req u)
  have hEmeet : ∀ u ∈ E, ∀ j k, ψ j k (twelvePoint u j k) = ξ u j k := by
    intro u hu j k
    exact (Finset.mem_filter.mp hu).2 _ (Finset.mem_image.mpr ⟨(j, k), Finset.mem_univ _, rfl⟩)
  -- 2. pigeonhole the escaping coordinate
  let Ej : Fin 4 → Finset (Fin 11 → ZMod N) := fun j =>
    E.filter fun u => ξ u j 0 - ξ u j 1 ∉ S (twelveX u j) (twelveA u j)
  obtain ⟨j, hj⟩ : ∃ j, E.card ≤ 4 * (Ej j).card := by
    by_contra hcon
    push Not at hcon
    have hcover : E ⊆ Finset.univ.biUnion Ej := by
      intro u hu
      obtain ⟨j, hj⟩ := hS u (Finset.mem_filter.mp hu).1
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hu, hj⟩⟩
    have h1 := (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    have h2 : ∑ j, 4 * (Ej j).card < ∑ _j : Fin 4, E.card :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun j _ => hcon j
    rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul] at h2
    omega
  set T := Ej j with hTdef
  have hTE : ∀ u ∈ T, u ∈ E := fun u hu => (Finset.mem_filter.mp hu).1
  -- 3. the common value at `j`
  let Fj : ZMod N → ZMod N → ZMod N := fun x a => ψ j 0 (x + a) - ψ j 1 x
  have hFj : ∀ u ∈ T, Fj (twelveX u j) (twelveA u j) = ξ u j 0 - ξ u j 1 := by
    intro u hu
    have h0 := hEmeet u (hTE u hu) j 0
    have h1 := hEmeet u (hTE u hu) j 1
    simp only [twelvePoint] at h0 h1
    exact congrArg₂ (· - ·) h0 h1
  -- the other terms, as functions of the 16 points
  let G : (Fin 11 → ZMod N) → ZMod N := fun u =>
    ∑ k, (ψ k 2 (twelvePoint u k 2) - ψ k 3 (twelvePoint u k 3)) -
      ∑ k ∈ Finset.univ.erase j, (ψ k 0 (twelvePoint u k 0) - ψ k 1 (twelvePoint u k 1))
  have hFG : ∀ u ∈ T, Fj (twelveX u j) (twelveA u j) = G u := by
    intro u hu
    have hm := hEmeet u (hTE u hu)
    have hd := hdec u (Finset.mem_filter.mp (hTE u hu)).1
    rw [hFj u hu]
    simp only [G, hm]
    rw [← hd, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    abel
  have hGagree : ∀ u u' : Fin 11 → ZMod N,
      (∀ k : Fin 11, k ≠ twelveXIndex j → u k = u' k) → G u = G u' := by
    intro u u' h
    obtain ⟨hx, hy, ha⟩ := twelve_coords_of_agree h
    simp only [G, twelvePoint]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Matrix.cons_val, hy k, ha k]
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hkj := Finset.ne_of_mem_erase hk
      simp only [Matrix.cons_val, hx k hkj, ha k]
  have hinj : Set.InjOn (fun u => (twelveX u j, twelveA u j, twelveRest j u))
      (T : Set (Fin 11 → ZMod N)) := by
    intro u _ u' _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hx, ha, hr⟩ := h
    have hoff := twelve_agree_off ha hr
    funext k
    by_cases hk : k = twelveXIndex j
    · subst hk; exact hx
    · exact hoff k hk
  have hdet : ∀ u ∈ T, ∀ u' ∈ T, twelveA u j = twelveA u' j →
      twelveRest j u = twelveRest j u' →
      Fj (twelveX u j) (twelveA u j) = Fj (twelveX u' j) (twelveA u' j) := by
    intro u hu u' hu' ha hr
    rw [hFG u hu, hFG u' hu']
    exact hGagree u u' (twelve_agree_off ha hr)
  obtain ⟨Θ, hΘ⟩ := exists_common_value_det (X := ZMod N) (A := ZMod N) (Y := Fin 9 → ZMod N)
    T (fun u => twelveX u j) (fun u => twelveA u j) (twelveRest j) hinj Fj hdet
  simp only [ZMod.card, Fintype.card_fun, Fintype.card_fin] at hΘ
  let T' := T.filter fun u => Fj (twelveX u j) (twelveA u j) = Θ (twelveA u j)
  let P := T'.image fun u => (twelveX u j, twelveA u j)
  -- each pair carries at most `N⁹` tuples
  have hT'P : (T'.card : Real) ≤ (N : Real) ^ 9 * P.card := by
    have h := Finset.card_le_mul_card_image (f := fun u => (twelveX u j, twelveA u j)) T' (N ^ 9)
      (by
        intro p _
        have : (T'.filter fun u => (twelveX u j, twelveA u j) = p).card ≤
            (Finset.univ : Finset (Fin 9 → ZMod N)).card := by
          refine Finset.card_le_card_of_injOn (twelveRest j) (fun _ _ => by simp) ?_
          intro u hu u' hu' hr
          have h1 := (Finset.mem_filter.mp hu).2
          have h2 := (Finset.mem_filter.mp hu').2
          rw [← h2] at h1
          simp only [Prod.mk.injEq] at h1
          exact hinj (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).1
            (Finset.mem_filter.mp (Finset.mem_filter.mp hu').1).1
            (Prod.ext h1.1 (Prod.ext h1.2 hr))
        rwa [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card] at this)
    exact_mod_cast h
  set c : Real := (ε / (4 * (K : Real) ^ 16)) ^ 2 with hc
  have hc0 : 0 < c := by positivity
  have hK16 : (0 : Real) < (K : Real) ^ 16 := by positivity
  have hEcard : ε / (K : Real) ^ 16 * (N : Real) ^ 11 ≤ E.card := by
    have h : (Tr.card : Real) ≤ (K : Real) ^ 16 * E.card := by exact_mod_cast hf
    rw [div_mul_eq_mul_div, div_le_iff₀ hK16]
    nlinarith
  have hTcard : ε / (4 * (K : Real) ^ 16) * (N : Real) ^ 11 ≤ T.card := by
    have h : (E.card : Real) ≤ 4 * T.card := by exact_mod_cast hj
    have : ε / (4 * (K : Real) ^ 16) * (N : Real) ^ 11 =
        (ε / (K : Real) ^ 16 * (N : Real) ^ 11) / 4 := by
      field_simp
    rw [this]
    linarith
  have hPc : c * (N : Real) ^ 2 ≤ P.card := by
    have h1 : (ε / (4 * (K : Real) ^ 16) * (N : Real) ^ 11) ^ 2 ≤ (T.card : Real) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hTcard 2
    have h2 : (T.card : Real) ^ 2 ≤ (N : Real) * ((N : Real) * (N : Real) ^ 9) *
        ((N : Real) ^ 9 * P.card) := by
      refine hΘ.trans ?_
      push_cast
      exact mul_le_mul_of_nonneg_left hT'P (by positivity)
    have h3 : c * (N : Real) ^ 2 * (N : Real) ^ 20 ≤ (P.card : Real) * (N : Real) ^ 20 := by
      calc c * (N : Real) ^ 2 * (N : Real) ^ 20 =
            (ε / (4 * (K : Real) ^ 16) * (N : Real) ^ 11) ^ 2 := by rw [hc]; ring
        _ ≤ (N : Real) * ((N : Real) * (N : Real) ^ 9) * ((N : Real) ^ 9 * P.card) := h1.trans h2
        _ = (P.card : Real) * (N : Real) ^ 20 := by ring
    exact le_of_mul_le_mul_right h3 (by positivity)
  have hP : ∀ p ∈ P, Θ p.2 = ψ j 0 (p.1 + p.2) - ψ j 1 p.1 := by
    intro p hp
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_filter.mp hu).2.symm
  obtain ⟨B, hF, hcnt⟩ := freiman_common_value Θ (ψ j 0) (ψ j 1) P hP hc0 hPc
  refine ⟨Θ, B, P.filter fun p => p.2 ∈ B, hF, ?_, ?_⟩
  · exact hcnt
  · intro p hp
    obtain ⟨hpP, hpB⟩ := Finset.mem_filter.mp hp
    refine ⟨hpB, ?_, ?_⟩
    · rw [hP p hpP]
      exact sub_mem_spanBall_union (hψ j 0 _) (hψ j 1 _)
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hpP
      obtain ⟨huT, huΘ⟩ := Finset.mem_filter.mp hu
      have hesc := (Finset.mem_filter.mp huT).2
      simp only
      rw [← huΘ, hFj u huT]
      exact hesc

end LeanProofs.GowersSzemeredi
