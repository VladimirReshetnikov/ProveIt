import GowersSzemeredi.Proofs14Configurations
import Mathlib.Algebra.Order.Chebyshev

/-!
# Product property and respected parallelepiped pairs

This module proves Corollary 14.6.  We first apply Corollary 14.5 in every
last-coordinate section.  For a fixed reference cube, the product property
then produces additive quadruples of cross-sections and vertex values.  The
resulting auxiliary objects map to respected `2`-arrangements; adjoining the
base of the reference cube makes this map injective.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private def cor146Embed {N k : Nat} (x : Point N k) (r : ZMod N) :
    Point N (k + 1) := Fin.snoc x r

private lemma cor146_embed_eq_append {N k : Nat} (x : Point N k)
    (r : ZMod N) : cor146Embed x r = appendCoordinate x r := by
  funext i
  cases i using Fin.lastCases with
  | last => simp [cor146Embed, appendCoordinate]
  | cast i => simp [cor146Embed, appendCoordinate]

private noncomputable def cor146Section {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (r : ZMod N) : Finset (Point N k) := by
  classical
  exact Finset.univ.filter fun x => cor146Embed x r ∈ B

private def cor146SectionPhi {N k : Nat}
    (phi : Point N (k + 1) → ZMod N) (r : ZMod N) : Point N k → ZMod N :=
  fun x => phi (cor146Embed x r)

private lemma cor146_replace_embed {N k : Nat} (y : Point N k)
    (r x : ZMod N) (j : Fin k) :
    replaceCoordinate (cor146Embed y r) j.castSucc x =
      cor146Embed (replaceCoordinate y j x) r := by
  simp [cor146Embed, replaceCoordinate]

private lemma cor146_section_product_property {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (gamma : Real) (hproduct : HasProductProperty B phi gamma) (r : ZMod N) :
    HasProductProperty (cor146Section B r) (cor146SectionPhi phi r) gamma := by
  intro p j y E theta htheta hmem
  have h := hproduct p j.castSucc (fun i => cor146Embed (y i) r) E theta htheta
  rw [show (fun i => coordinateRestriction phi (cor146Embed (y i) r) j.castSucc) =
      fun i => coordinateRestriction (cor146SectionPhi phi r) (y i) j by
    funext i x
    simp only [coordinateRestriction, cor146SectionPhi, cor146_replace_embed]] at h
  apply h
  intro i x hx
  rw [cor146_replace_embed]
  simpa [cor146Section] using hmem i x hx

private lemma cor146_countWhere_eq_sum_ite {X : Type*} [Fintype X]
    (P : X → Prop) :
    countWhere P = ∑ x : X,
      @ite Nat (P x) (Classical.propDecidable (P x)) 1 0 := by
  classical
  unfold countWhere
  simp

private lemma cor146_countWhere_prod {X Y : Type*} [Fintype X] [Fintype Y]
    (P : X → Y → Prop) :
    countWhere (fun z : X × Y => P z.1 z.2) =
      ∑ x : X, countWhere (P x) := by
  classical
  simp_rw [cor146_countWhere_eq_sum_ite]
  rw [Fintype.sum_prod_type]

private lemma cor146_countWhere_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (P : Y → Prop) :
    countWhere P = countWhere (fun x => P (e x)) := by
  classical
  simp_rw [cor146_countWhere_eq_sum_ite]
  exact (e.sum_comp (fun y => if P y then 1 else 0)).symm

private lemma cor146_sum_section_card {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) :
    ∑ r : ZMod N, (cor146Section B r).card = B.card := by
  classical
  let e : Point N k × ZMod N ≃ Point N (k + 1) :=
    (Equiv.prodComm (Point N k) (ZMod N)).trans
      (Fin.snocEquiv (fun _ : Fin (k + 1) => ZMod N))
  calc
    ∑ r : ZMod N, (cor146Section B r).card =
        ∑ r : ZMod N,
          countWhere (fun x : Point N k => cor146Embed x r ∈ B) := by
      apply Fintype.sum_congr
      intro r
      unfold cor146Section countWhere
      apply congrArg Finset.card
      ext x
      simp
    _ = countWhere (fun z : ZMod N × Point N k =>
        cor146Embed z.2 z.1 ∈ B) := by
      rw [show (∑ r : ZMod N,
          countWhere (fun x : Point N k => cor146Embed x r ∈ B)) =
        countWhere (fun z : ZMod N × Point N k =>
          cor146Embed z.2 z.1 ∈ B) from (cor146_countWhere_prod _).symm]
    _ = countWhere (fun z : Point N k × ZMod N =>
        cor146Embed z.1 z.2 ∈ B) := by
      simpa using (cor146_countWhere_equiv
        (Equiv.prodComm (ZMod N) (Point N k))
        (fun z : Point N k × ZMod N => cor146Embed z.1 z.2 ∈ B)).symm
    _ = countWhere (fun x : Point N (k + 1) => x ∈ B) := by
      symm
      simpa [e, cor146Embed, Fin.snocEquiv] using
        cor146_countWhere_equiv e (fun x : Point N (k + 1) => x ∈ B)
    _ = B.card := by simp [countWhere]

private lemma cor146_sum_section_density {N k : Nat} [NeZero N]
    (beta : Real) (B : Finset (Point N (k + 1)))
    (hcard : (B.card : Real) = beta * (N : Real) ^ (k + 1)) :
    ∑ r : ZMod N, (cor146Section B r).card / (N : Real) ^ k = beta * N := by
  calc
    ∑ r : ZMod N, (cor146Section B r).card / (N : Real) ^ k =
        (∑ r : ZMod N, ((cor146Section B r).card : Real)) /
          (N : Real) ^ k := by rw [Finset.sum_div]
    _ = (B.card : Real) / (N : Real) ^ k := by
      congr 1
      exact_mod_cast cor146_sum_section_card B
    _ = beta * N := by
      have hN : (N : Real) ≠ 0 := by exact_mod_cast (NeZero.ne N)
      rw [hcard, pow_succ]
      field_simp

private def cor146GoodPair {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (K : AxisCube N k) (r : ZMod N) (K' : AxisCube N k) : Prop :=
  K.IsIn (cor146Section B r) ∧ K'.IsIn (cor146Section B r) ∧
    K.IsCongruent K' ∧
      K.value (cor146SectionPhi phi r) = K'.value (cor146SectionPhi phi r)

private noncomputable def cor146GoodSet {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (K : AxisCube N k) (r : ZMod N) : Finset (AxisCube N k) := by
  classical
  exact Finset.univ.filter (cor146GoodPair B phi K r)

private def cor146Theta {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (K : AxisCube N k) (r : ZMod N) : Real :=
  (cor146GoodSet B phi K r).card

private lemma cor146_pair_count_eq_sum {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (r : ZMod N) :
    respectedCubePairCount (cor146Section B r) (cor146SectionPhi phi r) =
      ∑ K : AxisCube N k, (cor146GoodSet B phi K r).card := by
  classical
  unfold respectedCubePairCount
  change countWhere (fun z : AxisCube N k × AxisCube N k =>
    cor146GoodPair B phi z.1 r z.2) = _
  rw [show countWhere (fun z : AxisCube N k × AxisCube N k =>
      cor146GoodPair B phi z.1 r z.2) =
      ∑ K : AxisCube N k, countWhere (fun K' : AxisCube N k =>
        cor146GoodPair B phi K r K') from
    cor146_countWhere_prod (fun K K' => cor146GoodPair B phi K r K')]
  apply Fintype.sum_congr
  intro K
  unfold cor146GoodSet countWhere cor146GoodPair
  apply congrArg Finset.card
  ext K'
  simp

private lemma cor146_axis_cube_card (N k : Nat) [NeZero N] :
    Fintype.card (AxisCube N k) = N ^ (2 * k) := by
  simp only [AxisCube, Point, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, ZMod.card]
  rw [← pow_add]
  congr 1
  omega

private lemma cor146_pair_first_moment {N k : Nat} [NeZero N]
    (beta gamma : Real) (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N)
    (hk : 1 ≤ k) (_hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hgamma_one : gamma ≤ 1)
    (hcard : (B.card : Real) = beta * (N : Real) ^ (k + 1))
    (hproduct : HasProductProperty B phi gamma) :
    beta ^ (4 ^ k) * gamma ^ (2 * k * 4 ^ k) *
        (N : Real) ^ (3 * k + 1) ≤
      ∑ K : AxisCube N k, ∑ r : ZMod N, cor146Theta B phi K r := by
  let a := 4 ^ k
  let d : ZMod N → Real := fun r =>
    (cor146Section B r).card / (N : Real) ^ k
  let G : Real := gamma ^ (2 * k * a) * (N : Real) ^ (3 * k)
  have hN : 0 < (N : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have ha : 1 ≤ a := by
    dsimp only [a]
    have : 0 < 4 ^ k := pow_pos (by omega) k
    omega
  have ha0 : a ≠ 0 := by omega
  have hd_nonneg (r : ZMod N) : 0 ≤ d r := by
    dsimp only [d]
    positivity
  have hsection (r : ZMod N) :
      d r ^ a * G ≤
        respectedCubePairCount (cor146Section B r) (cor146SectionPhi phi r) := by
    by_cases hr : (cor146Section B r).card = 0
    · have hdr : d r = 0 := by simp [d, hr]
      rw [hdr, zero_pow (by omega), zero_mul]
      positivity
    · have hdr : 0 < d r := by
        dsimp only [d]
        exact div_pos (by exact_mod_cast Nat.pos_of_ne_zero hr) (pow_pos hN k)
      have hdcard : ((cor146Section B r).card : Real) =
          d r * (N : Real) ^ k := by
        dsimp only [d]
        field_simp
      simpa only [a, G, mul_assoc] using
        corollary_14_5_holds N k (d r) gamma (cor146Section B r)
          (cor146SectionPhi phi r) hk hdr hgamma hgamma_one hdcard
          (cor146_section_product_property B phi gamma hproduct r)
  have hsections :
      ∑ r : ZMod N, d r ^ a * G ≤
        ∑ r : ZMod N,
          (respectedCubePairCount (cor146Section B r)
            (cor146SectionPhi phi r) : Real) := by
    exact Finset.sum_le_sum fun r _ => hsection r
  have hd_sum : ∑ r : ZMod N, d r = beta * N := by
    simpa only [d] using cor146_sum_section_density beta B hcard
  have hmean0 := pow_sum_div_card_le_sum_pow
    (s := (Finset.univ : Finset (ZMod N))) (f := d)
    (fun r _ => hd_nonneg r) (a - 1)
  rw [Nat.sub_add_cancel ha] at hmean0
  simp only [Finset.card_univ, ZMod.card] at hmean0
  have hmean : beta ^ a * (N : Real) ≤ ∑ r : ZMod N, d r ^ a := by
    calc
      beta ^ a * (N : Real) = (beta * N) ^ a / (N : Real) ^ (a - 1) := by
        apply (eq_div_iff (pow_ne_zero _ hN.ne')).2
        rw [mul_pow]
        calc
          beta ^ a * (N : Real) * (N : Real) ^ (a - 1) =
              beta ^ a * ((N : Real) ^ (a - 1) * N) := by ring
          _ = beta ^ a * (N : Real) ^ a := by rw [pow_sub_one_mul ha0]
      _ = (∑ r : ZMod N, d r) ^ a / (N : Real) ^ (a - 1) := by rw [hd_sum]
      _ ≤ ∑ r : ZMod N, d r ^ a := hmean0
  calc
    beta ^ (4 ^ k) * gamma ^ (2 * k * 4 ^ k) *
        (N : Real) ^ (3 * k + 1) =
      (beta ^ a * (N : Real)) * G := by
        dsimp only [a, G]
        rw [pow_succ]
        ring
    _ ≤ (∑ r : ZMod N, d r ^ a) * G := by
      gcongr
    _ = ∑ r : ZMod N, d r ^ a * G := by rw [Finset.sum_mul]
    _ ≤ ∑ r : ZMod N,
        (respectedCubePairCount (cor146Section B r)
          (cor146SectionPhi phi r) : Real) := hsections
    _ = ∑ K : AxisCube N k, ∑ r : ZMod N, cor146Theta B phi K r := by
      simp_rw [cor146_pair_count_eq_sum]
      simp only [Nat.cast_sum, cor146Theta]
      rw [Finset.sum_comm]

private def cor146Average {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (K : AxisCube N k) : Real :=
  (∑ r : ZMod N, cor146Theta B phi K r) / N

private lemma cor146_average_fourth_moment {N k : Nat} [NeZero N]
    (beta gamma : Real) (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N)
    (_hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hfirst : beta ^ (4 ^ k) * gamma ^ (2 * k * 4 ^ k) *
        (N : Real) ^ (3 * k + 1) ≤
      ∑ K : AxisCube N k, ∑ r : ZMod N, cor146Theta B phi K r) :
    (beta ^ (4 ^ k) * gamma ^ (2 * k * 4 ^ k)) ^ 4 *
        (N : Real) ^ (6 * k) ≤
      ∑ K : AxisCube N k, (cor146Average B phi K) ^ 4 := by
  let A := beta ^ (4 ^ k) * gamma ^ (2 * k * 4 ^ k)
  let x : AxisCube N k → Real := cor146Average B phi
  have hN : 0 < (N : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hx_nonneg (K : AxisCube N k) : 0 ≤ x K := by
    dsimp only [x, cor146Average, cor146Theta]
    positivity
  have hx_sum : ∑ K : AxisCube N k, x K =
      (∑ K : AxisCube N k, ∑ r : ZMod N, cor146Theta B phi K r) / N := by
    dsimp only [x, cor146Average]
    rw [Finset.sum_div]
  have hfirst' : A * (N : Real) ^ (3 * k) ≤
      ∑ K : AxisCube N k, x K := by
    rw [hx_sum]
    apply (le_div_iff₀ hN).2
    calc
      A * (N : Real) ^ (3 * k) * N =
          beta ^ (4 ^ k) * gamma ^ (2 * k * 4 ^ k) *
            (N : Real) ^ (3 * k + 1) := by
        dsimp only [A]
        rw [pow_succ]
        ring
      _ ≤ ∑ K : AxisCube N k, ∑ r : ZMod N,
          cor146Theta B phi K r := hfirst
  have hmean := pow_sum_div_card_le_sum_pow
    (s := (Finset.univ : Finset (AxisCube N k))) (f := x)
    (fun K _ => hx_nonneg K) 3
  simp only [Finset.card_univ, cor146_axis_cube_card, Nat.cast_pow] at hmean
  have hleft : 0 ≤ A * (N : Real) ^ (3 * k) := by
    dsimp only [A]
    positivity
  have hpow : (A * (N : Real) ^ (3 * k)) ^ 4 ≤
      (∑ K : AxisCube N k, x K) ^ 4 := by
    gcongr
  calc
    (beta ^ (4 ^ k) * gamma ^ (2 * k * 4 ^ k)) ^ 4 *
        (N : Real) ^ (6 * k) =
      (A * (N : Real) ^ (3 * k)) ^ 4 /
        ((N : Real) ^ (2 * k)) ^ 3 := by
      dsimp only [A]
      have hNne : (N : Real) ≠ 0 := hN.ne'
      field_simp
      rw [← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      omega
    _ ≤ (∑ K : AxisCube N k, x K) ^ 4 /
        ((N : Real) ^ (2 * k)) ^ 3 := by
      exact div_le_div_of_nonneg_right hpow (by positivity)
    _ ≤ ∑ K : AxisCube N k, x K ^ 4 := hmean
    _ = ∑ K : AxisCube N k, (cor146Average B phi K) ^ 4 := by rfl

private def cor146VertexEquiv (k : Nat) :
    Fin (Fintype.card (Fin k → Bool)) ≃ (Fin k → Bool) :=
  (Fintype.equivFin (Fin k → Bool)).symm

private lemma cor146_vertex_card (k : Nat) :
    Fintype.card (Fin k → Bool) = 2 ^ k := by simp

private noncomputable def cor146ReferenceSection {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (K : AxisCube N k) : Finset (ZMod N) := by
  classical
  exact Finset.univ.filter fun r => K.IsIn (cor146Section B r)

private def cor146Sigma {N k : Nat}
    (phi : Point N (k + 1) → ZMod N) (K : AxisCube N k)
    (i : Fin (Fintype.card (Fin k → Bool))) (r : ZMod N) : ZMod N :=
  phi (cor146Embed (K.vertex (cor146VertexEquiv k i)) r)

private def cor146EnergyCondition {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (K : AxisCube N k) (q : Fin 4 → ZMod N) : Prop :=
  (∀ t, q t ∈ cor146ReferenceSection B K) ∧ IsAdditiveQuadruple q ∧
    ∀ i, IsAdditiveQuadruple (fun t => cor146Sigma phi K i (q t))

private def cor146FiberGood {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (K : AxisCube N k)
    (z : (Fin 4 → ZMod N) × (Fin 4 → AxisCube N k)) : Prop :=
  cor146EnergyCondition B phi K z.1 ∧
    ∀ t, z.2 t ∈ cor146GoodSet B phi K (z.1 t)

private lemma cor146_replace_last {N k : Nat} (y : Point N k) (r x : ZMod N) :
    replaceCoordinate (cor146Embed y r) (Fin.last k) x = cor146Embed y x := by
  simp [cor146Embed, replaceCoordinate, Fin.update_snoc_last]

private lemma cor146_count_choices {I Y : Type*} [Fintype I] [Fintype Y]
    [DecidableEq I]
    (S : I → Finset Y) :
    countWhere (fun f : I → Y => ∀ i, f i ∈ S i) =
      ∏ i : I, (S i).card := by
  classical
  unfold countWhere
  rw [Finset.filter_congr_decidable]
  calc
    (Finset.univ.filter fun f : I → Y => ∀ i, f i ∈ S i).card =
        (Fintype.piFinset S).card := by
      apply congrArg Finset.card
      ext f
      simp [Fintype.mem_piFinset]
    _ = ∏ i : I, (S i).card := Fintype.card_piFinset S

private lemma cor146_energy_eq_fiber_count {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (K : AxisCube N k) :
    weightedSimultaneousAdditiveEnergy (cor146ReferenceSection B K)
        (cor146Theta B phi K) (cor146Sigma phi K) =
      (countWhere (cor146FiberGood B phi K) : Nat) := by
  classical
  unfold weightedSimultaneousAdditiveEnergy
  simp only [cor146Theta]
  rw [show countWhere (cor146FiberGood B phi K) =
      countWhere (fun z : (Fin 4 → ZMod N) ×
        (Fin 4 → AxisCube N k) =>
        ((∀ t, z.1 t ∈ cor146ReferenceSection B K) ∧
            IsAdditiveQuadruple z.1 ∧
            ∀ i, IsAdditiveQuadruple
              (fun t => cor146Sigma phi K i (z.1 t))) ∧
          ∀ t, z.2 t ∈ cor146GoodSet B phi K (z.1 t)) by
    apply countWhere_congr
    intro z
    rfl]
  rw [show countWhere (fun z : (Fin 4 → ZMod N) ×
      (Fin 4 → AxisCube N k) =>
      ((∀ t, z.1 t ∈ cor146ReferenceSection B K) ∧
          IsAdditiveQuadruple z.1 ∧
          ∀ i, IsAdditiveQuadruple
            (fun t => cor146Sigma phi K i (z.1 t))) ∧
        ∀ t, z.2 t ∈ cor146GoodSet B phi K (z.1 t)) =
      ∑ q : Fin 4 → ZMod N,
        countWhere (fun f : Fin 4 → AxisCube N k =>
          ((∀ t, q t ∈ cor146ReferenceSection B K) ∧
              IsAdditiveQuadruple q ∧
              ∀ i, IsAdditiveQuadruple
                (fun t => cor146Sigma phi K i (q t))) ∧
            ∀ t, f t ∈ cor146GoodSet B phi K (q t)) from
    cor146_countWhere_prod
      (X := Fin 4 → ZMod N) (Y := Fin 4 → AxisCube N k)
      (fun q f =>
        ((∀ t, q t ∈ cor146ReferenceSection B K) ∧
            IsAdditiveQuadruple q ∧
            ∀ i, IsAdditiveQuadruple
              (fun t => cor146Sigma phi K i (q t))) ∧
          ∀ t, f t ∈ cor146GoodSet B phi K (q t))]
  simp only [Nat.cast_sum]
  apply Fintype.sum_congr
  intro q
  by_cases hq : (∀ t, q t ∈ cor146ReferenceSection B K) ∧
      IsAdditiveQuadruple q ∧
      ∀ i, IsAdditiveQuadruple (fun t => cor146Sigma phi K i (q t))
  · rw [if_pos hq]
    have hcount : countWhere (fun f : Fin 4 → AxisCube N k =>
        ((∀ t, q t ∈ cor146ReferenceSection B K) ∧
            IsAdditiveQuadruple q ∧
            ∀ i, IsAdditiveQuadruple
              (fun t => cor146Sigma phi K i (q t))) ∧
          ∀ t, f t ∈ cor146GoodSet B phi K (q t)) =
        countWhere (fun f : Fin 4 → AxisCube N k =>
          ∀ t, f t ∈ cor146GoodSet B phi K (q t)) := by
      apply countWhere_congr
      intro f
      exact and_iff_right hq
    rw [hcount, cor146_count_choices]
    norm_cast
  · rw [if_neg hq]
    have hfalse : countWhere (fun f : Fin 4 → AxisCube N k =>
        ((∀ t, q t ∈ cor146ReferenceSection B K) ∧
            IsAdditiveQuadruple q ∧
            ∀ i, IsAdditiveQuadruple
              (fun t => cor146Sigma phi K i (q t))) ∧
          ∀ t, f t ∈ cor146GoodSet B phi K (q t)) = 0 := by
      unfold countWhere
      rw [Finset.filter_congr_decidable]
      simp [hq]
    rw [hfalse]
    norm_num

private lemma cor146_theta_eq_zero_of_not_reference {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (K : AxisCube N k) (r : ZMod N)
    (hr : r ∉ cor146ReferenceSection B K) : cor146Theta B phi K r = 0 := by
  have hr' : ¬ K.IsIn (cor146Section B r) := by
    simpa [cor146ReferenceSection] using hr
  have hempty : cor146GoodSet B phi K r = ∅ := by
    classical
    ext K'
    simp only [cor146GoodSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, iff_false]
    intro hgood
    exact hr' hgood.1
  simp [cor146Theta, hempty]

private lemma cor146_sum_theta_reference {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (K : AxisCube N k) :
    ∑ r ∈ cor146ReferenceSection B K, cor146Theta B phi K r =
      ∑ r : ZMod N, cor146Theta B phi K r := by
  classical
  apply Finset.sum_subset (Finset.subset_univ _)
  intro r _ hr
  exact cor146_theta_eq_zero_of_not_reference B phi K r hr

private lemma cor146_product_lower {N k : Nat} [NeZero N]
    (gamma : Real) (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N)
    (hproduct : HasProductProperty B phi gamma) (K : AxisCube N k) :
    gamma ^ (8 * 2 ^ k) * (N : Real) ^ 3 *
        (cor146Average B phi K) ^ 4 ≤
      ((countWhere (cor146FiberGood B phi K) : Nat) : Real) := by
  let p := Fintype.card (Fin k → Bool)
  let y : Fin p → Point N (k + 1) := fun i =>
    cor146Embed (K.vertex (cor146VertexEquiv k i)) 0
  have h := hproduct p (Fin.last k) y (cor146ReferenceSection B K)
    (cor146Theta B phi K) (fun _ => by
      unfold cor146Theta
      positivity)
  have hmem : ∀ (i : Fin p) x, x ∈ cor146ReferenceSection B K →
      replaceCoordinate (y i) (Fin.last k) x ∈ B := by
    intro i x hx
    have hKin : K.IsIn (cor146Section B x) := by
      simpa [cor146ReferenceSection] using hx
    have hv := hKin (cor146VertexEquiv k i)
    rw [show replaceCoordinate (y i) (Fin.last k) x =
        cor146Embed (K.vertex (cor146VertexEquiv k i)) x by
      simp only [y, cor146_replace_last]]
    simpa [cor146Section] using hv
  specialize h hmem
  have hsigma : (fun i => coordinateRestriction phi (y i) (Fin.last k)) =
      cor146Sigma phi K := by
    funext i x
    simp only [coordinateRestriction, y, cor146_replace_last, cor146Sigma]
  rw [hsigma, cor146_energy_eq_fiber_count,
    cor146_sum_theta_reference] at h
  have hN : (N : Real) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  calc
    gamma ^ (8 * 2 ^ k) * (N : Real) ^ 3 *
        (cor146Average B phi K) ^ 4 =
      gamma ^ (8 * p) * (N : Real)⁻¹ *
        (∑ r : ZMod N, cor146Theta B phi K r) ^ 4 := by
      rw [show p = 2 ^ k by exact cor146_vertex_card k]
      unfold cor146Average
      rw [div_pow]
      have hinv : (N : Real) ^ 3 * ((N : Real) ^ 4)⁻¹ = (N : Real)⁻¹ := by
        field_simp
      rw [div_eq_mul_inv]
      calc
        gamma ^ (8 * 2 ^ k) * (N : Real) ^ 3 *
            ((∑ r : ZMod N, cor146Theta B phi K r) ^ 4 *
              ((N : Real) ^ 4)⁻¹) =
          gamma ^ (8 * 2 ^ k) *
            ((N : Real) ^ 3 * ((N : Real) ^ 4)⁻¹) *
              (∑ r : ZMod N, cor146Theta B phi K r) ^ 4 := by ring
        _ = _ := by rw [hinv]
    _ ≤ ((countWhere (cor146FiberGood B phi K) : Nat) : Real) := h

private lemma cor146_additiveTuple_two_iff {G : Type*} [AddCommMonoid G]
    (q : Fin 4 → G) :
    IsAdditiveTuple (k := 2) q ↔ IsAdditiveQuadruple q := by
  unfold IsAdditiveTuple IsAdditiveQuadruple
  rw [show (Finset.univ.filter (fun i : Fin 4 => (i : Nat) < 2)) =
      {0, 1} by decide]
  rw [show (Finset.univ.filter (fun i : Fin 4 => 2 ≤ (i : Nat))) =
      {2, 3} by decide]
  simp

private def cor146Build {N k : Nat}
    (z : AxisCube N k ×
      ((Fin 4 → ZMod N) × (Fin 4 → AxisCube N k))) :
    GeneralArrangement N k 2 :=
  (z.1.side, fun t => (z.2.2 t).base, z.2.1)

private lemma cor146_build_cube {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (K : AxisCube N k) (q : Fin 4 → ZMod N)
    (f : Fin 4 → AxisCube N k)
    (hgood : ∀ t, f t ∈ cor146GoodSet B phi K (q t)) (t : Fin 4) :
    (cor146Build (K, q, f)).cube t = f t := by
  have ht : K.IsCongruent (f t) := by
    have htgood : cor146GoodPair B phi K (q t) (f t) := by
      simpa [cor146GoodSet] using hgood t
    exact htgood.2.2.1
  apply Prod.ext
  · rfl
  · exact ht

private lemma cor146_reference_values_additive {N k : Nat} [NeZero N]
    (phi : Point N (k + 1) → ZMod N) (K : AxisCube N k)
    (q : Fin 4 → ZMod N)
    (himage : ∀ i, IsAdditiveQuadruple
      (fun t => cor146Sigma phi K i (q t))) :
    IsAdditiveQuadruple
      (fun t => K.value (cor146SectionPhi phi (q t))) := by
  unfold IsAdditiveQuadruple AxisCube.value
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Fintype.sum_congr
  intro e
  let i := (cor146VertexEquiv k).symm e
  have hi := himage i
  have hi' :
      phi (cor146Embed (K.vertex e) (q 0)) +
          phi (cor146Embed (K.vertex e) (q 1)) =
        phi (cor146Embed (K.vertex e) (q 2)) +
          phi (cor146Embed (K.vertex e) (q 3)) := by
    simpa [IsAdditiveQuadruple, cor146Sigma, i] using hi
  unfold cor146SectionPhi
  linear_combination (-1 : ZMod N) ^ boolWeight e * hi'

private lemma cor146_build_cubeValue {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (K : AxisCube N k) (q : Fin 4 → ZMod N)
    (f : Fin 4 → AxisCube N k)
    (hgood : ∀ t, f t ∈ cor146GoodSet B phi K (q t)) (t : Fin 4) :
    (cor146Build (K, q, f)).cubeValue phi t =
      (f t).value (cor146SectionPhi phi (q t)) := by
  unfold GeneralArrangement.cubeValue AxisCube.value
  apply Fintype.sum_congr
  intro e
  congr 1
  unfold GeneralArrangement.vertex
  rw [cor146_build_cube B phi K q f hgood]
  change phi (appendCoordinate ((f t).vertex e) (q t)) =
    phi (cor146Embed ((f t).vertex e) (q t))
  rw [cor146_embed_eq_append]

private lemma cor146_build_good {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (K : AxisCube N k) (q : Fin 4 → ZMod N)
    (f : Fin 4 → AxisCube N k)
    (hsource : cor146FiberGood B phi K (q, f)) :
    (cor146Build (K, q, f)).IsIn B ∧
      (cor146Build (K, q, f)).IsRespected phi := by
  have henergy := hsource.1
  have hgood := hsource.2
  constructor
  · constructor
    · exact (cor146_additiveTuple_two_iff q).2 henergy.2.1
    · intro e t
      have ht : cor146GoodPair B phi K (q t) (f t) := by
        simpa [cor146GoodSet] using hgood t
      have ht' : (f t).IsIn (cor146Section B (q t)) := by
        exact ht.2.1
      have hv := ht' e
      unfold GeneralArrangement.vertex
      rw [cor146_build_cube B phi K q f hgood]
      change appendCoordinate ((f t).vertex e) (q t) ∈ B
      rw [← cor146_embed_eq_append]
      simpa [cor146Section] using hv
  · apply (cor146_additiveTuple_two_iff _).2
    have href := cor146_reference_values_additive phi K q henergy.2.2
    unfold IsAdditiveQuadruple at href ⊢
    have heq (t : Fin 4) :
        (cor146Build (K, q, f)).cubeValue phi t =
          K.value (cor146SectionPhi phi (q t)) := by
      rw [cor146_build_cubeValue B phi K q f hgood]
      have ht : cor146GoodPair B phi K (q t) (f t) := by
        simpa [cor146GoodSet] using hgood t
      exact ht.2.2.2.symm
    simpa only [heq] using href

private def cor146SourceGood {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (z : AxisCube N k ×
      ((Fin 4 → ZMod N) × (Fin 4 → AxisCube N k))) : Prop :=
  cor146FiberGood B phi z.1 z.2

private def cor146AugmentedBuild {N k : Nat}
    (z : AxisCube N k ×
      ((Fin 4 → ZMod N) × (Fin 4 → AxisCube N k))) :
    GeneralArrangement N k 2 × Point N k :=
  (cor146Build z, z.1.base)

private lemma cor146_augmented_injective {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    {K L : AxisCube N k} {q q' : Fin 4 → ZMod N}
    {f g : Fin 4 → AxisCube N k}
    (hf : cor146FiberGood B phi K (q, f))
    (hg : cor146FiberGood B phi L (q', g))
    (h : cor146AugmentedBuild (K, q, f) =
      cor146AugmentedBuild (L, q', g)) :
    (K, q, f) = (L, q', g) := by
  have hR : cor146Build (K, q, f) = cor146Build (L, q', g) :=
    congrArg Prod.fst h
  have hb : K.base = L.base := congrArg Prod.snd h
  have hs : K.side = L.side := by
    have := congrArg GeneralArrangement.side hR
    exact this
  have hK : K = L := Prod.ext hb hs
  have hq : q = q' := by
    have := congrArg GeneralArrangement.crossSection hR
    exact this
  have hbases : (fun t => (f t).base) = fun t => (g t).base := by
    have := congrArg GeneralArrangement.base hR
    exact this
  have hfg : f = g := by
    funext t
    have hft : cor146GoodPair B phi K (q t) (f t) := by
      simpa [cor146GoodSet] using hf.2 t
    have hgt : cor146GoodPair B phi L (q' t) (g t) := by
      simpa [cor146GoodSet] using hg.2 t
    apply Prod.ext
    · exact congrFun hbases t
    · calc
        (f t).side = K.side := hft.2.2.1.symm
        _ = L.side := hs
        _ = (g t).side := hgt.2.2.1
  exact Prod.ext hK (Prod.ext hq hfg)

private lemma cor146_source_count_le {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N) :
    ∑ K : AxisCube N k, countWhere (cor146FiberGood B phi K) ≤
      respectedGeneralArrangementCount 2 B phi * N ^ k := by
  classical
  rw [← show countWhere (cor146SourceGood B phi) =
      ∑ K : AxisCube N k, countWhere (cor146FiberGood B phi K) from
    cor146_countWhere_prod
      (X := AxisCube N k)
      (Y := (Fin 4 → ZMod N) × (Fin 4 → AxisCube N k))
      (fun K z => cor146FiberGood B phi K z)]
  unfold countWhere respectedGeneralArrangementCount
  rw [Finset.filter_congr_decidable, Finset.filter_congr_decidable]
  calc
    (Finset.univ.filter (cor146SourceGood B phi)).card ≤
        ((Finset.univ.filter (fun R : GeneralArrangement N k 2 =>
          R.IsIn B ∧ R.IsRespected phi)) ×ˢ
            (Finset.univ : Finset (Point N k))).card := by
      refine Finset.card_le_card_of_injOn cor146AugmentedBuild ?_ ?_
      · intro z hz
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
          true_and, Finset.mem_product] at hz ⊢
        exact ⟨cor146_build_good B phi z.1 z.2.1 z.2.2 hz, trivial⟩
      · intro z hz w hw hzw
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
          true_and] at hz hw
        exact cor146_augmented_injective B phi hz hw hzw
    _ = (Finset.univ.filter (fun R : GeneralArrangement N k 2 =>
          R.IsIn B ∧ R.IsRespected phi)).card * N ^ k := by
      rw [Finset.card_product]
      simp [Point]
    _ = respectedGeneralArrangementCount 2 B phi * N ^ k := by
      congr 1
      unfold respectedGeneralArrangementCount countWhere
      apply congrArg Finset.card
      ext R
      simp

private lemma cor146_direct_constant_identity {N k : Nat} [NeZero N]
    (beta gamma : Real) :
    (beta ^ (4 ^ (k + 1)) *
        gamma ^ (2 * k * 4 ^ (k + 1) + 8 * 2 ^ k) *
        (N : Real) ^ (5 * k + 3)) * (N : Real) ^ k =
      gamma ^ (8 * 2 ^ k) * (N : Real) ^ 3 *
        ((beta ^ (4 ^ k) * gamma ^ (2 * k * 4 ^ k)) ^ 4 *
          (N : Real) ^ (6 * k)) := by
  have hfour : 4 ^ (k + 1) = 4 ^ k * 4 := by rw [pow_succ]
  have hgamma : 2 * k * 4 ^ (k + 1) + 8 * 2 ^ k =
      (2 * k * 4 ^ k) * 4 + 8 * 2 ^ k := by
    rw [hfour]
    ring
  have hNpow : (N : Real) ^ (5 * k + 3) * (N : Real) ^ k =
      (N : Real) ^ 3 * (N : Real) ^ (6 * k) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [hgamma, hfour, pow_add, pow_mul, pow_mul, mul_pow]
  calc
    (beta ^ 4 ^ k) ^ 4 *
        ((gamma ^ (2 * k * 4 ^ k)) ^ 4 * gamma ^ (8 * 2 ^ k)) *
        (N : Real) ^ (5 * k + 3) * (N : Real) ^ k =
      ((beta ^ 4 ^ k) ^ 4 *
        ((gamma ^ (2 * k * 4 ^ k)) ^ 4 * gamma ^ (8 * 2 ^ k))) *
        ((N : Real) ^ (5 * k + 3) * (N : Real) ^ k) := by ring
    _ = ((beta ^ 4 ^ k) ^ 4 *
        ((gamma ^ (2 * k * 4 ^ k)) ^ 4 * gamma ^ (8 * 2 ^ k))) *
        ((N : Real) ^ 3 * (N : Real) ^ (6 * k)) := by rw [hNpow]
    _ = gamma ^ (8 * 2 ^ k) * (N : Real) ^ 3 *
        ((beta ^ 4 ^ k) ^ 4 * (gamma ^ (2 * k * 4 ^ k)) ^ 4 *
          (N : Real) ^ (6 * k)) := by ring

private lemma cor146_direct_lower {N k : Nat} [NeZero N]
    (beta gamma : Real) (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N)
    (_hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hproduct : HasProductProperty B phi gamma)
    (hfourth :
      (beta ^ (4 ^ k) * gamma ^ (2 * k * 4 ^ k)) ^ 4 *
          (N : Real) ^ (6 * k) ≤
        ∑ K : AxisCube N k, (cor146Average B phi K) ^ 4) :
    beta ^ (4 ^ (k + 1)) *
        gamma ^ (2 * k * 4 ^ (k + 1) + 8 * 2 ^ k) *
        (N : Real) ^ (5 * k + 3) ≤
      respectedGeneralArrangementCount 2 B phi := by
  let H := gamma ^ (8 * 2 ^ k) * (N : Real) ^ 3
  have hH : 0 ≤ H := by
    dsimp only [H]
    positivity
  have hproducts : H *
      (∑ K : AxisCube N k, (cor146Average B phi K) ^ 4) ≤
      ∑ K : AxisCube N k,
        ((countWhere (cor146FiberGood B phi K) : Nat) : Real) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun K _ => cor146_product_lower gamma B phi hproduct K
  have hsource : H *
      ((beta ^ (4 ^ k) * gamma ^ (2 * k * 4 ^ k)) ^ 4 *
        (N : Real) ^ (6 * k)) ≤
      ∑ K : AxisCube N k, countWhere (cor146FiberGood B phi K) := by
    calc
      H * ((beta ^ (4 ^ k) * gamma ^ (2 * k * 4 ^ k)) ^ 4 *
          (N : Real) ^ (6 * k)) ≤
        H * (∑ K : AxisCube N k, (cor146Average B phi K) ^ 4) :=
          mul_le_mul_of_nonneg_left hfourth hH
      _ ≤ ∑ K : AxisCube N k,
          ((countWhere (cor146FiberGood B phi K) : Nat) : Real) := hproducts
      _ = (∑ K : AxisCube N k,
          countWhere (cor146FiberGood B phi K) : Nat) := by norm_cast
  have hupper :
      (∑ K : AxisCube N k,
          countWhere (cor146FiberGood B phi K) : Real) ≤
        (respectedGeneralArrangementCount 2 B phi : Nat) * (N : Real) ^ k := by
    exact_mod_cast cor146_source_count_le B phi
  have hN : 0 < (N : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hNpow : 0 < (N : Real) ^ k := pow_pos hN k
  apply le_of_mul_le_mul_right ?_ hNpow
  exact calc
    (beta ^ (4 ^ (k + 1)) *
        gamma ^ (2 * k * 4 ^ (k + 1) + 8 * 2 ^ k) *
        (N : Real) ^ (5 * k + 3)) * (N : Real) ^ k =
      H * ((beta ^ (4 ^ k) * gamma ^ (2 * k * 4 ^ k)) ^ 4 *
        (N : Real) ^ (6 * k)) := by
          exact cor146_direct_constant_identity beta gamma
    _ ≤ (∑ K : AxisCube N k,
        countWhere (cor146FiberGood B phi K) : Real) := by
          simpa only [Nat.cast_sum] using hsource
    _ ≤ (respectedGeneralArrangementCount 2 B phi : Nat) *
        (N : Real) ^ k := hupper

private lemma cor146_gamma_exponent_le (k : Nat) (hk : 1 ≤ k) :
    2 * k * 4 ^ (k + 1) + 8 * 2 ^ k ≤ 3 * k * 4 ^ (k + 1) := by
  by_cases hk_one : k = 1
  · subst k
    norm_num
  · have hk_two : 2 ≤ k := by omega
    have hpow : 2 ^ k ≤ 4 ^ k := Nat.pow_le_pow_left (by omega) k
    have hfirst : 8 * 2 ^ k ≤ 8 * 4 ^ k := Nat.mul_le_mul_left 8 hpow
    have hsecond : 8 * 4 ^ k ≤ (4 * k) * 4 ^ k :=
      Nat.mul_le_mul_right (4 ^ k) (by omega)
    have hextra : 8 * 2 ^ k ≤ k * 4 ^ (k + 1) := by
      calc
        8 * 2 ^ k ≤ 8 * 4 ^ k := hfirst
        _ ≤ (4 * k) * 4 ^ k := hsecond
        _ = k * 4 ^ (k + 1) := by rw [pow_succ]; ring
    calc
      2 * k * 4 ^ (k + 1) + 8 * 2 ^ k ≤
          2 * k * 4 ^ (k + 1) + k * 4 ^ (k + 1) :=
        Nat.add_le_add_left hextra _
      _ = 3 * k * 4 ^ (k + 1) := by ring

theorem corollary_14_6_holds : corollary_14_6 := by
  intro N k _ beta gamma B phi hk hbeta hgamma hgamma_one hcard hproduct
  have hfirst := cor146_pair_first_moment beta gamma B phi hk hbeta hgamma
    hgamma_one hcard hproduct
  have hfourth := cor146_average_fourth_moment beta gamma B phi hbeta hgamma hfirst
  have hdirect := cor146_direct_lower beta gamma B phi hbeta hgamma hproduct hfourth
  have hexponent := cor146_gamma_exponent_le k hk
  have hgamma_power :
      gamma ^ (3 * k * 4 ^ (k + 1)) ≤
        gamma ^ (2 * k * 4 ^ (k + 1) + 8 * 2 ^ k) :=
    pow_le_pow_of_le_one hgamma.le hgamma_one hexponent
  have hbeta_power : 0 ≤ beta ^ (4 ^ (k + 1)) := pow_nonneg hbeta.le _
  have hN_power : 0 ≤ (N : Real) ^ (5 * k + 3) := by positivity
  calc
    beta ^ (4 ^ (k + 1)) * gamma ^ (3 * k * 4 ^ (k + 1)) *
        (N : Real) ^ (5 * k + 3) ≤
      beta ^ (4 ^ (k + 1)) *
        gamma ^ (2 * k * 4 ^ (k + 1) + 8 * 2 ^ k) *
        (N : Real) ^ (5 * k + 3) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hgamma_power hbeta_power) hN_power
    _ ≤ (respectedGeneralArrangementCount 2 B phi : Real) := hdirect

end LeanProofs.GowersSzemeredi
