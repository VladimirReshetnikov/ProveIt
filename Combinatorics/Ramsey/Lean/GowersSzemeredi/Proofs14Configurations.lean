import GowersSzemeredi.Proofs14Product
import Mathlib.Algebra.Order.Chebyshev

/-!
# Configuration counts from the product property

This module proves Lemma 14.4 and Corollary 14.5.  The induction for Lemma
14.4 splits off the first coordinate, applies the product property to all
vertices of a lower-dimensional configuration, and uses the finite power-mean
inequality twice.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private abbrev prop144VertexIndex (n : Nat) :=
  (Fin n → Bool) × (Fin n → Bool)

private def prop144IndexEquiv (n : Nat) :
    Fin (Fintype.card (prop144VertexIndex n)) ≃ prop144VertexIndex n :=
  (Fintype.equivFin (prop144VertexIndex n)).symm

private lemma prop144_index_card (n : Nat) :
    Fintype.card (prop144VertexIndex n) = 4 ^ n := by
  simp only [prop144VertexIndex, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_bool]
  rw [← mul_pow]
  norm_num

private def prop144Section {N n : Nat} [NeZero N]
    (B : Finset (Point N (n + 1))) (r : ZMod N) : Finset (Point N n) := by
  classical
  exact Finset.univ.filter fun x => Fin.cons r x ∈ B

private def prop144SectionPhi {N n : Nat}
    (phi : Point N (n + 1) → ZMod N) (r : ZMod N) : Point N n → ZMod N :=
  fun x => phi (Fin.cons r x)

private lemma prop144_replace_cons {N n : Nat} (r : ZMod N)
    (y : Point N n) (j : Fin n) (x : ZMod N) :
    replaceCoordinate (Fin.cons r y) j.succ x =
      Fin.cons r (replaceCoordinate y j x) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [replaceCoordinate, Function.update,
      dif_neg (Ne.symm (Fin.succ_ne_zero j)), Fin.cons_zero]
  · simp [replaceCoordinate, Function.update, Fin.succ_inj]

private lemma prop144_section_product_property {N n : Nat} [NeZero N]
    (B : Finset (Point N (n + 1))) (phi : Point N (n + 1) → ZMod N)
    (gamma : Real) (hproduct : HasProductProperty B phi gamma) (r : ZMod N) :
    HasProductProperty (prop144Section B r) (prop144SectionPhi phi r) gamma := by
  intro p j y E theta htheta hmem
  have h := hproduct p j.succ (fun i => Fin.cons r (y i)) E theta htheta
  rw [show (fun i => coordinateRestriction phi (Fin.cons r (y i)) j.succ) =
      fun i => coordinateRestriction (prop144SectionPhi phi r) (y i) j by
    funext i x
    simp only [coordinateRestriction, prop144SectionPhi, prop144_replace_cons]] at h
  apply h
  intro i x hx
  rw [prop144_replace_cons]
  change Fin.cons r (replaceCoordinate (y i) j x) ∈ B
  simpa [prop144Section] using hmem i x hx

private def prop144GoodAt {N n : Nat} [NeZero N]
    (B : Finset (Point N (n + 1))) (phi : Point N (n + 1) → ZMod N)
    (L : CubeConfiguration N n) (r : ZMod N) : Prop :=
  L.IsIn (prop144Section B r) ∧
    L.IsRespected (prop144SectionPhi phi r)

private noncomputable def prop144GoodSet {N n : Nat} [NeZero N]
    (B : Finset (Point N (n + 1))) (phi : Point N (n + 1) → ZMod N)
    (L : CubeConfiguration N n) : Finset (ZMod N) := by
  classical
  exact Finset.univ.filter (prop144GoodAt B phi L)

private def prop144QuadCoordinate {N : Nat}
    (q : Fin 4 → ZMod N) (e u : Bool) : ZMod N :=
  if e then (if u then q 1 else q 2) else (if u then q 3 else q 0)

private def prop144Build {N n : Nat} (L : CubeConfiguration N n)
    (q : Fin 4 → ZMod N) : CubeConfiguration N (n + 1) :=
  (Fin.cons (q 0) L.base,
    Fin.cons (q 2 - q 0) L.firstSide,
    Fin.cons (q 3 - q 0) L.secondSide)

private lemma prop144_build_vertex {N n : Nat} (L : CubeConfiguration N n)
    (q : Fin 4 → ZMod N) (hq : IsAdditiveQuadruple q)
    (e₀ u₀ : Bool) (e u : Fin n → Bool) :
    (prop144Build L q).vertex (Fin.cons e₀ e) (Fin.cons u₀ u) =
      Fin.cons (prop144QuadCoordinate q e₀ u₀) (L.vertex e u) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · cases e₀ <;> cases u₀
    · simp [prop144Build, CubeConfiguration.vertex, CubeConfiguration.base,
        CubeConfiguration.firstSide, CubeConfiguration.secondSide,
        prop144QuadCoordinate]
    · simp [prop144Build, CubeConfiguration.vertex, CubeConfiguration.base,
        CubeConfiguration.firstSide, CubeConfiguration.secondSide,
        prop144QuadCoordinate]
    · simp [prop144Build, CubeConfiguration.vertex, CubeConfiguration.base,
        CubeConfiguration.firstSide, CubeConfiguration.secondSide,
        prop144QuadCoordinate]
    · simp only [prop144Build, CubeConfiguration.vertex,
        CubeConfiguration.base, CubeConfiguration.firstSide,
        CubeConfiguration.secondSide, Fin.cons_zero, if_true,
        prop144QuadCoordinate]
      change q 0 + (q 2 - q 0) + (q 3 - q 0) = q 1
      rw [show q 0 + (q 2 - q 0) + (q 3 - q 0) = q 2 + q 3 - q 0 by abel]
      rw [← hq]
      abel
  · simp [prop144Build, CubeConfiguration.vertex, CubeConfiguration.base,
      CubeConfiguration.firstSide, CubeConfiguration.secondSide,
      prop144QuadCoordinate]

private def prop144Sigma {N n : Nat}
    (phi : Point N (n + 1) → ZMod N) (L : CubeConfiguration N n)
    (i : Fin (Fintype.card (prop144VertexIndex n))) (r : ZMod N) : ZMod N :=
  let eu := prop144IndexEquiv n i
  phi (Fin.cons r (L.vertex eu.1 eu.2))

private def prop144GoodQuad {N n : Nat} [NeZero N]
    (B : Finset (Point N (n + 1))) (phi : Point N (n + 1) → ZMod N)
    (L : CubeConfiguration N n) (q : Fin 4 → ZMod N) : Prop :=
  (∀ t, q t ∈ prop144GoodSet B phi L) ∧ IsAdditiveQuadruple q ∧
    ∀ i, IsAdditiveQuadruple (fun t => prop144Sigma phi L i (q t))

private lemma prop144_good_of_coordinate {N n : Nat} [NeZero N]
    (B : Finset (Point N (n + 1))) (phi : Point N (n + 1) → ZMod N)
    (L : CubeConfiguration N n) (q : Fin 4 → ZMod N)
    (hgood : ∀ t, q t ∈ prop144GoodSet B phi L) (e u : Bool) :
    prop144GoodAt B phi L (prop144QuadCoordinate q e u) := by
  cases e <;> cases u
  · simpa [prop144GoodSet, prop144QuadCoordinate] using hgood 0
  · simpa [prop144GoodSet, prop144QuadCoordinate] using hgood 3
  · simpa [prop144GoodSet, prop144QuadCoordinate] using hgood 2
  · simpa [prop144GoodSet, prop144QuadCoordinate] using hgood 1

private lemma prop144_build_isIn {N n : Nat} [NeZero N]
    (B : Finset (Point N (n + 1))) (phi : Point N (n + 1) → ZMod N)
    (L : CubeConfiguration N n) (q : Fin 4 → ZMod N)
    (hq : prop144GoodQuad B phi L q) : (prop144Build L q).IsIn B := by
  intro e u
  let e₀ := e 0
  let u₀ := u 0
  let e' := Fin.tail e
  let u' := Fin.tail u
  have he : e = Fin.cons e₀ e' := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  have hu : u = Fin.cons u₀ u' := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  rw [he, hu, prop144_build_vertex L q hq.2.1]
  have hgood := prop144_good_of_coordinate B phi L q hq.1 e₀ u₀
  have hin := hgood.1 e' u'
  simpa [prop144Section] using hin

private lemma prop144_build_injective {N n : Nat}
    {L L' : CubeConfiguration N n} {q q' : Fin 4 → ZMod N}
    (hq : IsAdditiveQuadruple q) (hq' : IsAdditiveQuadruple q')
    (h : prop144Build L q = prop144Build L' q') : L = L' ∧ q = q' := by
  have hb := congrArg CubeConfiguration.base h
  have hg := congrArg CubeConfiguration.firstSide h
  have hh := congrArg CubeConfiguration.secondSide h
  have hq0 : q 0 = q' 0 := congrFun hb 0
  have hbase : L.base = L'.base := by
    funext i
    exact congrFun hb i.succ
  have hghead : q 2 - q 0 = q' 2 - q' 0 := congrFun hg 0
  have hfirst : L.firstSide = L'.firstSide := by
    funext i
    exact congrFun hg i.succ
  have hhhead : q 3 - q 0 = q' 3 - q' 0 := congrFun hh 0
  have hsecond : L.secondSide = L'.secondSide := by
    funext i
    exact congrFun hh i.succ
  have hq2 : q 2 = q' 2 := by
    rw [hq0] at hghead
    exact sub_left_injective hghead
  have hq3 : q 3 = q' 3 := by
    rw [hq0] at hhhead
    exact sub_left_injective hhhead
  have hq1 : q 1 = q' 1 := by
    have hleft : q 0 + q 1 = q' 0 + q' 1 := by
      rw [hq, hq', hq2, hq3]
    rw [hq0] at hleft
    exact add_left_cancel hleft
  constructor
  · exact Prod.ext hbase (Prod.ext hfirst hsecond)
  · funext t
    fin_cases t
    · exact hq0
    · exact hq1
    · exact hq2
    · exact hq3

private lemma prop144_update_cons_zero {n : Nat} {X : Type*}
    (a b : X) (f : Fin n → X) :
    Function.update (Fin.cons a f : Fin (n + 1) → X) 0 b =
      (Fin.cons b f : Fin (n + 1) → X) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [Function.update]
  · simp [Function.update]

private lemma prop144_update_cons_succ {n : Nat} {X : Type*}
    (a b : X) (f : Fin n → X) (j : Fin n) :
    Function.update (Fin.cons a f : Fin (n + 1) → X) j.succ b =
      (Fin.cons a (Function.update f j b) : Fin (n + 1) → X) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [Function.update, dif_neg (Ne.symm (Fin.succ_ne_zero j)),
      Fin.cons_zero]
  · simp [Function.update, Fin.succ_inj]

private lemma prop144_build_isRespected {N n : Nat} [NeZero N]
    (B : Finset (Point N (n + 1))) (phi : Point N (n + 1) → ZMod N)
    (L : CubeConfiguration N n) (q : Fin 4 → ZMod N)
    (hq : prop144GoodQuad B phi L q) :
    (prop144Build L q).IsRespected phi := by
  intro j e u
  let e₀ := e 0
  let u₀ := u 0
  let e' := Fin.tail e
  let u' := Fin.tail u
  have he : e = Fin.cons e₀ e' := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  have hu : u = Fin.cons u₀ u' := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  rw [he, hu]
  refine Fin.cases ?_ (fun j => ?_) j
  · rw [prop144_update_cons_zero, prop144_update_cons_zero,
      prop144_update_cons_zero, prop144_update_cons_zero,
      prop144_build_vertex L q hq.2.1,
      prop144_build_vertex L q hq.2.1,
      prop144_build_vertex L q hq.2.1,
      prop144_build_vertex L q hq.2.1]
    let i := (prop144IndexEquiv n).symm (e', u')
    have hi := hq.2.2 i
    simpa [IsAdditiveQuadruple, prop144Sigma, i,
      prop144QuadCoordinate] using hi
  · rw [prop144_update_cons_succ, prop144_update_cons_succ,
      prop144_update_cons_succ, prop144_update_cons_succ,
      prop144_build_vertex L q hq.2.1,
      prop144_build_vertex L q hq.2.1,
      prop144_build_vertex L q hq.2.1,
      prop144_build_vertex L q hq.2.1]
    have hgood := prop144_good_of_coordinate B phi L q hq.1 e₀ u₀
    simpa [prop144SectionPhi] using hgood.2 j e' u'

private lemma prop144_energy_eq_count {N n : Nat} [NeZero N]
    (B : Finset (Point N (n + 1))) (phi : Point N (n + 1) → ZMod N)
    (L : CubeConfiguration N n) :
    weightedSimultaneousAdditiveEnergy (prop144GoodSet B phi L)
        (fun _ => (1 : Real)) (prop144Sigma phi L) =
      (countWhere (prop144GoodQuad B phi L) : Nat) := by
  classical
  unfold weightedSimultaneousAdditiveEnergy prop144GoodQuad
  rw [show
      (∑ q : Fin 4 → ZMod N,
        if (∀ t, q t ∈ prop144GoodSet B phi L) ∧
            IsAdditiveQuadruple q ∧
            ∀ i, IsAdditiveQuadruple
              (fun t => prop144Sigma phi L i (q t)) then
          ∏ _t : Fin 4, (1 : Real) else 0) =
        ∑ q : Fin 4 → ZMod N,
          if (∀ t, q t ∈ prop144GoodSet B phi L) ∧
              IsAdditiveQuadruple q ∧
              ∀ i, IsAdditiveQuadruple
                (fun t => prop144Sigma phi L i (q t)) then
            (1 : Real) else 0 by simp]
  unfold countWhere
  rw [Finset.filter_congr_decidable]
  simp

private lemma prop144_product_lower {N n : Nat} [NeZero N]
    (B : Finset (Point N (n + 1))) (phi : Point N (n + 1) → ZMod N)
    (gamma : Real) (hproduct : HasProductProperty B phi gamma)
    (L : CubeConfiguration N n) :
    gamma ^ (8 * 4 ^ n) * (N : Real)⁻¹ *
        (prop144GoodSet B phi L).card ^ 4 ≤
      (countWhere (prop144GoodQuad B phi L) : Nat) := by
  let p := Fintype.card (prop144VertexIndex n)
  let y : Fin p → Point N (n + 1) := fun i =>
    let eu := prop144IndexEquiv n i
    Fin.cons 0 (L.vertex eu.1 eu.2)
  have h := hproduct p 0 y (prop144GoodSet B phi L) (fun _ => 1)
    (fun _ => by positivity)
  have hmem : ∀ (i : Fin p) x, x ∈ prop144GoodSet B phi L →
      replaceCoordinate (y i) 0 x ∈ B := by
    intro i x hx
    have hgood : prop144GoodAt B phi L x := by
      simpa [prop144GoodSet] using hx
    let eu := prop144IndexEquiv n i
    have hin := hgood.1 eu.1 eu.2
    rw [show replaceCoordinate (y i) 0 x =
        Fin.cons x (L.vertex eu.1 eu.2) by
      simp only [y, eu, replaceCoordinate, prop144_update_cons_zero]]
    simpa [prop144Section] using hin
  specialize h hmem
  have hsigma :
      (fun i => coordinateRestriction phi (y i) 0) = prop144Sigma phi L := by
    funext i x
    let eu := prop144IndexEquiv n i
    simp only [coordinateRestriction, y, replaceCoordinate,
      prop144_update_cons_zero, prop144Sigma]
  rw [hsigma, prop144_energy_eq_count] at h
  simpa only [p, prop144_index_card, Finset.sum_const_zero,
    Finset.sum_const, nsmul_eq_mul, one_mul, mul_one, Nat.cast_pow,
    Nat.cast_ofNat] using h

private lemma prop144_countWhere_eq_sum_ite {X : Type*} [Fintype X]
    (P : X → Prop) :
    countWhere P = ∑ x : X,
      @ite Nat (P x) (Classical.propDecidable (P x)) 1 0 := by
  classical
  unfold countWhere
  simp

private lemma prop144_countWhere_prod {X Y : Type*} [Fintype X] [Fintype Y]
    (P : X → Y → Prop) :
    countWhere (fun z : X × Y => P z.1 z.2) =
      ∑ x : X, countWhere (P x) := by
  classical
  simp_rw [prop144_countWhere_eq_sum_ite]
  rw [Fintype.sum_prod_type]

private lemma prop144_countWhere_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (P : Y → Prop) :
    countWhere P = countWhere (fun x => P (e x)) := by
  classical
  simp_rw [prop144_countWhere_eq_sum_ite]
  exact (e.sum_comp (fun y => if P y then 1 else 0)).symm

private lemma prop144_sum_section_card {N n : Nat} [NeZero N]
    (B : Finset (Point N (n + 1))) :
    ∑ r : ZMod N, (prop144Section B r).card = B.card := by
  classical
  let e := Fin.consEquiv (fun _ : Fin (n + 1) => ZMod N)
  calc
    ∑ r : ZMod N, (prop144Section B r).card =
        ∑ r : ZMod N, countWhere (fun x : Point N n => Fin.cons r x ∈ B) := by
          apply Fintype.sum_congr
          intro r
          unfold prop144Section countWhere
          apply congrArg Finset.card
          ext x
          simp
    _ = countWhere (fun z : ZMod N × Point N n => Fin.cons z.1 z.2 ∈ B) :=
      (prop144_countWhere_prod _).symm
    _ = countWhere (fun x : Point N (n + 1) => x ∈ B) := by
      symm
      simpa [e, Fin.consEquiv] using
        (prop144_countWhere_equiv e (fun x : Point N (n + 1) => x ∈ B))
    _ = B.card := by simp [countWhere]

private lemma prop144_sum_goodset_card {N n : Nat} [NeZero N]
    (B : Finset (Point N (n + 1))) (phi : Point N (n + 1) → ZMod N) :
    ∑ L : CubeConfiguration N n, (prop144GoodSet B phi L).card =
      ∑ r : ZMod N,
        respectedConfigurationCount (prop144Section B r)
          (prop144SectionPhi phi r) := by
  classical
  simp_rw [show ∀ L : CubeConfiguration N n,
      (prop144GoodSet B phi L).card =
        countWhere (fun r : ZMod N => prop144GoodAt B phi L r) by
    intro L
    unfold prop144GoodSet countWhere
    rfl]
  simp_rw [prop144_countWhere_eq_sum_ite]
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro r
  rw [← prop144_countWhere_eq_sum_ite]
  rfl

private lemma prop144_sum_goodquad_le {N n : Nat} [NeZero N]
    (B : Finset (Point N (n + 1))) (phi : Point N (n + 1) → ZMod N) :
    ∑ L : CubeConfiguration N n,
        countWhere (prop144GoodQuad B phi L) ≤
      respectedConfigurationCount B phi := by
  classical
  rw [← prop144_countWhere_prod]
  unfold respectedConfigurationCount countWhere
  rw [Finset.filter_congr_decidable, Finset.filter_congr_decidable]
  refine Finset.card_le_card_of_injOn
    (fun z : CubeConfiguration N n × (Fin 4 → ZMod N) =>
      prop144Build z.1 z.2) ?_ ?_
  · intro z hz
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact ⟨prop144_build_isIn B phi z.1 z.2 hz,
      prop144_build_isRespected B phi z.1 z.2 hz⟩
  · intro z hz z' hz' heq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hz hz'
    obtain ⟨hL, hq⟩ := prop144_build_injective hz.2.1 hz'.2.1 heq
    exact Prod.ext hL hq

private lemma prop144_configuration_card (N n : Nat) [NeZero N] :
    Fintype.card (CubeConfiguration N n) = N ^ (3 * n) := by
  simp only [CubeConfiguration, Point, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, ZMod.card]
  rw [← pow_add, ← pow_add]
  congr 1
  omega

private lemma prop144_sum_section_density {N n : Nat} [NeZero N]
    (beta : Real) (B : Finset (Point N (n + 1)))
    (hcard : (B.card : Real) = beta * (N : Real) ^ (n + 1)) :
    ∑ r : ZMod N,
        (prop144Section B r).card / (N : Real) ^ n = beta * N := by
  have hN : (N : Real) ≠ 0 := by
    exact_mod_cast (NeZero.ne N)
  calc
    ∑ r : ZMod N,
        (prop144Section B r).card / (N : Real) ^ n =
        (∑ r : ZMod N, ((prop144Section B r).card : Real)) /
          (N : Real) ^ n := by rw [Finset.sum_div]
    _ = (B.card : Real) / (N : Real) ^ n := by
      congr 1
      exact_mod_cast prop144_sum_section_card B
    _ = beta * N := by
      rw [hcard, pow_succ]
      field_simp

private lemma prop144_zero_dim {N : Nat} [NeZero N]
    (beta gamma : Real) (B : Finset (Point N 0))
    (phi : Point N 0 → ZMod N)
    (hbeta : 0 < beta)
    (hcard : (B.card : Real) = beta * (N : Real) ^ 0) :
    beta ^ (4 ^ 0) * gamma ^ (2 * 0 * 4 ^ 0) *
        (N : Real) ^ (3 * 0) ≤ respectedConfigurationCount B phi := by
  classical
  have hbeta_card : (B.card : Real) = beta := by simpa using hcard
  have hcard_pos : 0 < B.card := by exact_mod_cast hbeta_card.symm ▸ hbeta
  have hcard_le : B.card ≤ 1 := by
    simpa [Point] using B.card_le_univ
  have hcard_one : B.card = 1 := by omega
  have hB : B = Finset.univ := by
    apply B.card_eq_iff_eq_univ.mp
    simpa [Point] using hcard_one
  have hbeta_one : beta = 1 := by
    rw [← hbeta_card, hcard_one]
    norm_num
  rw [hbeta_one]
  norm_num
  unfold respectedConfigurationCount countWhere
  apply Finset.one_le_card.mpr
  refine ⟨default, ?_⟩
  rw [Finset.filter_congr_decidable]
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · intro e u
    rw [hB]
    exact Finset.mem_univ _
  · intro j
    exact Fin.elim0 j

private lemma prop144_first_moment {N n : Nat} [NeZero N]
    (beta gamma : Real) (B : Finset (Point N (n + 1)))
    (phi : Point N (n + 1) → ZMod N)
    (hcard : (B.card : Real) = beta * (N : Real) ^ (n + 1))
    (hproduct : HasProductProperty B phi gamma)
    (hind : ∀ (beta' : Real) (B' : Finset (Point N n))
        (phi' : Point N n → ZMod N),
      0 < beta' →
      (B'.card : Real) = beta' * (N : Real) ^ n →
      HasProductProperty B' phi' gamma →
      beta' ^ (4 ^ n) * gamma ^ (2 * n * 4 ^ n) *
          (N : Real) ^ (3 * n) ≤ respectedConfigurationCount B' phi') :
    beta ^ (4 ^ n) * gamma ^ (2 * n * 4 ^ n) *
        (N : Real) ^ (3 * n + 1) ≤
      ∑ L : CubeConfiguration N n,
        ((prop144GoodSet B phi L).card : Real) := by
  let a := 4 ^ n
  let d : ZMod N → Real := fun r =>
    (prop144Section B r).card / (N : Real) ^ n
  let G : Real := gamma ^ (2 * n * a) * (N : Real) ^ (3 * n)
  have hN : 0 < (N : Real) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))
  have ha : 1 ≤ a := by
    dsimp only [a]
    have : 0 < 4 ^ n := pow_pos (by omega) n
    omega
  have ha0 : a ≠ 0 := by omega
  have hd_nonneg (r : ZMod N) : 0 ≤ d r := by
    dsimp only [d]
    positivity
  have hsection (r : ZMod N) :
      d r ^ a * G ≤
        respectedConfigurationCount (prop144Section B r)
          (prop144SectionPhi phi r) := by
    by_cases hr : (prop144Section B r).card = 0
    · have hdr : d r = 0 := by simp [d, hr]
      rw [hdr, zero_pow (by omega), zero_mul]
      positivity
    · have hdr : 0 < d r := by
        dsimp only [d]
        exact div_pos (by exact_mod_cast Nat.pos_of_ne_zero hr) (pow_pos hN n)
      have hdcard : ((prop144Section B r).card : Real) =
          d r * (N : Real) ^ n := by
        dsimp only [d]
        field_simp
      simpa only [a, G, mul_assoc] using
        hind (d r) (prop144Section B r) (prop144SectionPhi phi r)
          hdr hdcard (prop144_section_product_property B phi gamma hproduct r)
  have hsections :
      ∑ r : ZMod N, d r ^ a * G ≤
        ∑ r : ZMod N,
          (respectedConfigurationCount (prop144Section B r)
            (prop144SectionPhi phi r) : Real) := by
    exact Finset.sum_le_sum fun r _ => hsection r
  have hd_sum : ∑ r : ZMod N, d r = beta * N := by
    simpa only [d] using prop144_sum_section_density beta B hcard
  have hmean0 := pow_sum_div_card_le_sum_pow
    (s := (Finset.univ : Finset (ZMod N)))
    (f := d) (fun r _ => hd_nonneg r) (a - 1)
  have hmean : beta ^ a * (N : Real) ≤ ∑ r : ZMod N, d r ^ a := by
    rw [Nat.sub_add_cancel ha] at hmean0
    simp only [Finset.card_univ, ZMod.card] at hmean0
    calc
      beta ^ a * (N : Real) = (beta * N) ^ a / (N : Real) ^ (a - 1) := by
        apply (eq_div_iff (pow_ne_zero _ hN.ne')).2
        rw [mul_pow]
        calc
          beta ^ a * (N : Real) * (N : Real) ^ (a - 1) =
              beta ^ a * ((N : Real) ^ (a - 1) * N) := by ring
          _ = beta ^ a * (N : Real) ^ a := by
            rw [pow_sub_one_mul ha0]
      _ = (∑ r : ZMod N, d r) ^ a / (N : Real) ^ (a - 1) := by
        rw [hd_sum]
      _ ≤ ∑ r : ZMod N, d r ^ a := hmean0
  have hG : 0 ≤ G := by
    dsimp only [G]
    positivity
  calc
    beta ^ (4 ^ n) * gamma ^ (2 * n * 4 ^ n) *
        (N : Real) ^ (3 * n + 1) =
        (beta ^ a * (N : Real)) * G := by
      dsimp only [a, G]
      rw [pow_succ]
      ring
    _ ≤ (∑ r : ZMod N, d r ^ a) * G :=
      mul_le_mul_of_nonneg_right hmean hG
    _ = ∑ r : ZMod N, d r ^ a * G := by rw [Finset.sum_mul]
    _ ≤ ∑ r : ZMod N,
          (respectedConfigurationCount (prop144Section B r)
            (prop144SectionPhi phi r) : Real) := hsections
    _ = ∑ L : CubeConfiguration N n,
          ((prop144GoodSet B phi L).card : Real) := by
      exact_mod_cast (prop144_sum_goodset_card B phi).symm

private lemma prop144_fourth_moment {N n : Nat} [NeZero N]
    (beta gamma : Real) (B : Finset (Point N (n + 1)))
    (phi : Point N (n + 1) → ZMod N)
    (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hfirst : beta ^ (4 ^ n) * gamma ^ (2 * n * 4 ^ n) *
        (N : Real) ^ (3 * n + 1) ≤
      ∑ L : CubeConfiguration N n,
        ((prop144GoodSet B phi L).card : Real)) :
    (beta ^ (4 ^ n) * gamma ^ (2 * n * 4 ^ n) *
        (N : Real) ^ (3 * n + 1)) ^ 4 /
        ((N : Real) ^ (3 * n)) ^ 3 ≤
      ∑ L : CubeConfiguration N n,
        ((prop144GoodSet B phi L).card : Real) ^ 4 := by
  let m : CubeConfiguration N n → Real := fun L =>
    (prop144GoodSet B phi L).card
  have hN : 0 < (N : Real) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))
  have hm_nonneg (L : CubeConfiguration N n) : 0 ≤ m L := by
    dsimp only [m]
    positivity
  have hmean := pow_sum_div_card_le_sum_pow
    (s := (Finset.univ : Finset (CubeConfiguration N n)))
    (f := m) (fun L _ => hm_nonneg L) 3
  simp only [Finset.card_univ, prop144_configuration_card, Nat.cast_pow] at hmean
  have hleft : 0 ≤ beta ^ (4 ^ n) * gamma ^ (2 * n * 4 ^ n) *
      (N : Real) ^ (3 * n + 1) := by positivity
  have hpow :
      (beta ^ (4 ^ n) * gamma ^ (2 * n * 4 ^ n) *
          (N : Real) ^ (3 * n + 1)) ^ 4 ≤
        (∑ L : CubeConfiguration N n, m L) ^ 4 := by
    gcongr
  calc
    (beta ^ (4 ^ n) * gamma ^ (2 * n * 4 ^ n) *
        (N : Real) ^ (3 * n + 1)) ^ 4 /
        ((N : Real) ^ (3 * n)) ^ 3 ≤
      (∑ L : CubeConfiguration N n, m L) ^ 4 /
        ((N : Real) ^ (3 * n)) ^ 3 := by
          exact div_le_div_of_nonneg_right hpow (by positivity)
    _ ≤ ∑ L : CubeConfiguration N n, m L ^ 4 := hmean
    _ = ∑ L : CubeConfiguration N n,
        ((prop144GoodSet B phi L).card : Real) ^ 4 := by rfl

private lemma prop144_sum_product_lower {N n : Nat} [NeZero N]
    (gamma : Real) (B : Finset (Point N (n + 1)))
    (phi : Point N (n + 1) → ZMod N)
    (hproduct : HasProductProperty B phi gamma) :
    gamma ^ (8 * 4 ^ n) * (N : Real)⁻¹ *
        (∑ L : CubeConfiguration N n,
          ((prop144GoodSet B phi L).card : Real) ^ 4) ≤
      ∑ L : CubeConfiguration N n,
        (countWhere (prop144GoodQuad B phi L) : Real) := by
  calc
    gamma ^ (8 * 4 ^ n) * (N : Real)⁻¹ *
        (∑ L : CubeConfiguration N n,
          ((prop144GoodSet B phi L).card : Real) ^ 4) =
      ∑ L : CubeConfiguration N n,
        gamma ^ (8 * 4 ^ n) * (N : Real)⁻¹ *
          ((prop144GoodSet B phi L).card : Real) ^ 4 := by
            rw [Finset.mul_sum]
    _ ≤ ∑ L : CubeConfiguration N n,
        (countWhere (prop144GoodQuad B phi L) : Real) := by
      exact Finset.sum_le_sum fun L _ =>
        prop144_product_lower B phi gamma hproduct L

private lemma prop144_constant_identity {N n : Nat} [NeZero N]
    (beta gamma : Real) :
    beta ^ (4 ^ (n + 1)) * gamma ^ (2 * (n + 1) * 4 ^ (n + 1)) *
        (N : Real) ^ (3 * (n + 1)) =
      gamma ^ (8 * 4 ^ n) * (N : Real)⁻¹ *
        ((beta ^ (4 ^ n) * gamma ^ (2 * n * 4 ^ n) *
          (N : Real) ^ (3 * n + 1)) ^ 4 /
            ((N : Real) ^ (3 * n)) ^ 3) := by
  have hN : (N : Real) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have hfour : 4 ^ (n + 1) = 4 * 4 ^ n := by
    rw [pow_succ]
    omega
  have hgamma : 2 * (n + 1) * 4 ^ (n + 1) =
      8 * 4 ^ n + 4 * (2 * n * 4 ^ n) := by
    rw [hfour]
    ring
  rw [hgamma, hfour, pow_add]
  have hcomm (x : Nat) : 4 * x = x * 4 := by omega
  rw [hcomm (4 ^ n), pow_mul]
  rw [hcomm (2 * n * 4 ^ n), pow_mul]
  simp only [mul_pow]
  have hNfactor : (N : Real) ^ (3 * (n + 1)) =
      (N : Real)⁻¹ * (((N : Real) ^ (3 * n + 1)) ^ 4 /
        ((N : Real) ^ (3 * n)) ^ 3) := by
    field_simp
    rw [← pow_mul, ← pow_mul, ← pow_succ, ← pow_add]
    congr 1
    omega
  rw [hNfactor]
  ring

private theorem prop144_all_dimensions :
    ∀ (k N : Nat) [NeZero N] (beta gamma : Real)
      (B : Finset (Point N k)) (phi : Point N k → ZMod N),
      0 < beta → 0 < gamma →
      (B.card : Real) = beta * (N : Real) ^ k →
      HasProductProperty B phi gamma →
      beta ^ (4 ^ k) * gamma ^ (2 * k * 4 ^ k) *
          (N : Real) ^ (3 * k) ≤ respectedConfigurationCount B phi := by
  intro k
  induction k with
  | zero =>
      intro N _ beta gamma B phi hbeta _ hcard _
      exact prop144_zero_dim beta gamma B phi hbeta hcard
  | succ n ih =>
      intro N _ beta gamma B phi hbeta hgamma hcard hproduct
      have hfirst := prop144_first_moment beta gamma B phi
        hcard hproduct (fun beta' B' phi' hbeta' hcard' hproduct' =>
          ih N beta' gamma B' phi' hbeta' hgamma hcard' hproduct')
      have hfourth := prop144_fourth_moment beta gamma B phi hbeta hgamma hfirst
      have hfactor : 0 ≤ gamma ^ (8 * 4 ^ n) * (N : Real)⁻¹ := by
        positivity
      calc
        beta ^ (4 ^ (n + 1)) *
            gamma ^ (2 * (n + 1) * 4 ^ (n + 1)) *
            (N : Real) ^ (3 * (n + 1)) =
          gamma ^ (8 * 4 ^ n) * (N : Real)⁻¹ *
            ((beta ^ (4 ^ n) * gamma ^ (2 * n * 4 ^ n) *
              (N : Real) ^ (3 * n + 1)) ^ 4 /
                ((N : Real) ^ (3 * n)) ^ 3) :=
          prop144_constant_identity beta gamma
        _ ≤ gamma ^ (8 * 4 ^ n) * (N : Real)⁻¹ *
            (∑ L : CubeConfiguration N n,
              ((prop144GoodSet B phi L).card : Real) ^ 4) :=
          mul_le_mul_of_nonneg_left hfourth hfactor
        _ ≤ ∑ L : CubeConfiguration N n,
            (countWhere (prop144GoodQuad B phi L) : Real) :=
          prop144_sum_product_lower gamma B phi hproduct
        _ ≤ respectedConfigurationCount B phi := by
          exact_mod_cast prop144_sum_goodquad_le B phi

/-- **Lemma 14.4.** Product property gives many respected configurations. -/
theorem lemma_14_4_holds : lemma_14_4 := by
  intro N k _ beta gamma B phi _ hbeta hgamma _ hcard hproduct
  exact prop144_all_dimensions k N beta gamma B phi hbeta hgamma hcard hproduct

private lemma prop145_boolWeight_insertNth {n : Nat}
    (j : Fin (n + 1)) (b : Bool) (e : Fin n → Bool) :
    boolWeight (j.insertNth b e) = (if b then 1 else 0) + boolWeight e := by
  classical
  unfold boolWeight
  rw [prop144_countWhere_eq_sum_ite, prop144_countWhere_eq_sum_ite]
  let ind : Bool → Nat := fun c => if c then 1 else 0
  have hind (c : Bool) :
      @ite Nat (c = true) (Classical.propDecidable (c = true)) 1 0 = ind c := by
    cases c <;> simp [ind]
  have hfun :
      (fun i : Fin (n + 1) =>
        ind ((j.insertNth b e : Fin (n + 1) → Bool) i)) =
        j.insertNth (ind b) (fun i : Fin n => ind (e i)) := by
    rw [Fin.eq_insertNth_iff]
    constructor
    · simp
    · funext i
      simp [Fin.removeNth_apply]
  calc
    (∑ i : Fin (n + 1),
        @ite Nat ((j.insertNth b e : Fin (n + 1) → Bool) i = true)
          (Classical.propDecidable _) 1 0) =
        ∑ i : Fin (n + 1),
          ind ((j.insertNth b e : Fin (n + 1) → Bool) i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hind _
    _ = ∑ i : Fin (n + 1),
        (j.insertNth (ind b) (fun i : Fin n => ind (e i))) i := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrFun hfun i
    _ = ind b + ∑ i : Fin n, ind (e i) := Fin.sum_insertNth j _ _
    _ = (if b then 1 else 0) + ∑ i : Fin n, ind (e i) := by congr 1
    _ = (if b then 1 else 0) +
        ∑ i : Fin n,
          @ite Nat (e i = true) (Classical.propDecidable _) 1 0 := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact (hind _).symm

private lemma prop145_alternating_sum_eq_of_faces {N n : Nat} [NeZero N]
    (F₀ F₁ : (Fin (n + 1) → Bool) → ZMod N) (j : Fin (n + 1))
    (hface : ∀ u,
      F₀ (Function.update u j false) + F₁ (Function.update u j true) =
        F₁ (Function.update u j false) + F₀ (Function.update u j true)) :
    (∑ u : Fin (n + 1) → Bool,
        (-1 : ZMod N) ^ boolWeight u * F₀ u) =
      ∑ u : Fin (n + 1) → Bool,
        (-1 : ZMod N) ^ boolWeight u * F₁ u := by
  let E := Fin.insertNthEquiv (fun _ : Fin (n + 1) => Bool) j
  calc
    (∑ u : Fin (n + 1) → Bool,
        (-1 : ZMod N) ^ boolWeight u * F₀ u) =
      ∑ p : Bool × (Fin n → Bool),
        (-1 : ZMod N) ^ boolWeight (E p) * F₀ (E p) := by
          exact (E.sum_comp _).symm
    _ = ∑ e : Fin n → Bool, ∑ b : Bool,
        (-1 : ZMod N) ^ boolWeight (j.insertNth b e) *
          F₀ (j.insertNth b e) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      rfl
    _ = ∑ e : Fin n → Bool, ∑ b : Bool,
        (-1 : ZMod N) ^ boolWeight (j.insertNth b e) *
          F₁ (j.insertNth b e) := by
      apply Fintype.sum_congr
      intro e
      rw [Fintype.sum_bool, Fintype.sum_bool]
      have hfalse : (-1 : ZMod N) ^ boolWeight (j.insertNth false e) =
          (-1 : ZMod N) ^ boolWeight e := by
        rw [prop145_boolWeight_insertNth]
        simp
      have htrue : (-1 : ZMod N) ^ boolWeight (j.insertNth true e) =
          -((-1 : ZMod N) ^ boolWeight e) := by
        rw [prop145_boolWeight_insertNth]
        simp only [if_true]
        rw [show 1 + boolWeight e = boolWeight e + 1 by omega, pow_succ]
        ring
      rw [hfalse, htrue]
      have hf := hface (j.insertNth false e)
      simp only [Fin.update_insertNth] at hf
      linear_combination (-1 : ZMod N) ^ boolWeight e * hf
    _ = ∑ p : Bool × (Fin n → Bool),
        (-1 : ZMod N) ^ boolWeight (E p) * F₁ (E p) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      rfl
    _ = ∑ u : Fin (n + 1) → Bool,
        (-1 : ZMod N) ^ boolWeight u * F₁ u :=
      E.sum_comp (fun u => (-1 : ZMod N) ^ boolWeight u * F₁ u)

private def prop145Slice {N k : Nat} (C : CubeConfiguration N k)
    (e : Fin k → Bool) : AxisCube N k :=
  (fun i => C.base i + if e i then C.firstSide i else 0, C.secondSide)

private lemma prop145_slice_vertex {N k : Nat} (C : CubeConfiguration N k)
    (e u : Fin k → Bool) :
    (prop145Slice C e).vertex u = C.vertex e u := by
  rfl

private lemma prop145_slice_value_update {N n : Nat} [NeZero N]
    (C : CubeConfiguration N (n + 1)) (phi : Point N (n + 1) → ZMod N)
    (hrespect : C.IsRespected phi) (j : Fin (n + 1))
    (e : Fin (n + 1) → Bool) :
    (prop145Slice C (Function.update e j false)).value phi =
      (prop145Slice C (Function.update e j true)).value phi := by
  unfold AxisCube.value
  simp_rw [prop145_slice_vertex]
  apply prop145_alternating_sum_eq_of_faces
  intro u
  exact hrespect j e u

private def prop145Prefix {k : Nat} (m : Nat) : Fin k → Bool :=
  fun i => if i.val < m then true else false

private lemma prop145_prefix_zero {k : Nat} :
    prop145Prefix (k := k) 0 = fun _ => false := by
  funext i
  simp [prop145Prefix]

private lemma prop145_prefix_full {k : Nat} :
    prop145Prefix (k := k) k = fun _ => true := by
  funext i
  simp [prop145Prefix, i.isLt]

private lemma prop145_prefix_update_false {k m : Nat} (hm : m < k) :
    Function.update (prop145Prefix (k := k) m) ⟨m, hm⟩ false =
      prop145Prefix (k := k) m := by
  funext i
  by_cases hi : i = ⟨m, hm⟩
  · subst i
    simp [Function.update, prop145Prefix]
  · simp [Function.update, hi]

private lemma prop145_prefix_update_true {k m : Nat} (hm : m < k) :
    Function.update (prop145Prefix (k := k) m) ⟨m, hm⟩ true =
      prop145Prefix (k := k) (m + 1) := by
  funext i
  by_cases hi : i = ⟨m, hm⟩
  · subst i
    simp [Function.update, prop145Prefix]
  · have hiv : i.val ≠ m := by
      intro hiv
      apply hi
      exact Fin.ext hiv
    by_cases hlt : i.val < m
    · have hlt' : i.val < m + 1 := by omega
      simp [Function.update, hi, prop145Prefix, hlt, hlt']
    · have hlt' : ¬ i.val < m + 1 := by omega
      simp [Function.update, hi, prop145Prefix, hlt, hlt']

private lemma prop145_slice_end_values {N n : Nat} [NeZero N]
    (C : CubeConfiguration N (n + 1)) (phi : Point N (n + 1) → ZMod N)
    (hrespect : C.IsRespected phi) :
    (prop145Slice C (fun _ => false)).value phi =
      (prop145Slice C (fun _ => true)).value phi := by
  have hpath : ∀ m, m ≤ n + 1 →
      (prop145Slice C (prop145Prefix (k := n + 1) 0)).value phi =
        (prop145Slice C (prop145Prefix (k := n + 1) m)).value phi := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih =>
        have hmk : m < n + 1 := by omega
        calc
          (prop145Slice C (prop145Prefix (k := n + 1) 0)).value phi =
              (prop145Slice C (prop145Prefix (k := n + 1) m)).value phi :=
            ih (by omega)
          _ = (prop145Slice C
              (Function.update (prop145Prefix (k := n + 1) m)
                ⟨m, hmk⟩ false)).value phi := by
            rw [prop145_prefix_update_false hmk]
          _ = (prop145Slice C
              (Function.update (prop145Prefix (k := n + 1) m)
                ⟨m, hmk⟩ true)).value phi :=
            prop145_slice_value_update C phi hrespect ⟨m, hmk⟩ _
          _ = (prop145Slice C
              (prop145Prefix (k := n + 1) (m + 1))).value phi := by
            rw [prop145_prefix_update_true hmk]
  simpa only [prop145_prefix_zero, prop145_prefix_full] using hpath (n + 1) le_rfl

private def prop145Pair {N k : Nat} (C : CubeConfiguration N k) :
    AxisCube N k × AxisCube N k :=
  ((C.base, C.secondSide),
    (fun i => C.base i + C.firstSide i, C.secondSide))

private lemma prop145_pair_good {N n : Nat} [NeZero N]
    (B : Finset (Point N (n + 1))) (phi : Point N (n + 1) → ZMod N)
    (C : CubeConfiguration N (n + 1))
    (hC : C.IsIn B ∧ C.IsRespected phi) :
    (prop145Pair C).1.IsIn B ∧ (prop145Pair C).2.IsIn B ∧
      (prop145Pair C).1.IsCongruent (prop145Pair C).2 ∧
        (prop145Pair C).1.value phi = (prop145Pair C).2.value phi := by
  have hfirst : (prop145Pair C).1 = prop145Slice C (fun _ => false) := by
    ext <;> simp [prop145Pair, prop145Slice]
  have hsecond : (prop145Pair C).2 = prop145Slice C (fun _ => true) := by
    ext <;> simp [prop145Pair, prop145Slice]
  constructor
  · intro u
    rw [hfirst, prop145_slice_vertex]
    exact hC.1 (fun _ => false) u
  constructor
  · intro u
    rw [hsecond, prop145_slice_vertex]
    exact hC.1 (fun _ => true) u
  constructor
  · rfl
  · rw [hfirst, hsecond]
    exact prop145_slice_end_values C phi hC.2

private lemma prop145_pair_injective {N k : Nat}
    {C D : CubeConfiguration N k} (h : prop145Pair C = prop145Pair D) :
    C = D := by
  have hb : C.base = D.base := congrArg (fun P => P.1.1) h
  have hh : C.secondSide = D.secondSide := congrArg (fun P => P.1.2) h
  have hbg : (fun i => C.base i + C.firstSide i) =
      (fun i => D.base i + D.firstSide i) := congrArg (fun P => P.2.1) h
  have hg : C.firstSide = D.firstSide := by
    funext i
    have hi := congrFun hbg i
    rw [congrFun hb i] at hi
    exact add_left_cancel hi
  exact Prod.ext hb (Prod.ext hg hh)

private lemma prop145_count_le {N n : Nat} [NeZero N]
    (B : Finset (Point N (n + 1))) (phi : Point N (n + 1) → ZMod N) :
    respectedConfigurationCount B phi ≤ respectedCubePairCount B phi := by
  classical
  unfold respectedConfigurationCount respectedCubePairCount countWhere
  rw [Finset.filter_congr_decidable, Finset.filter_congr_decidable]
  refine Finset.card_le_card_of_injOn prop145Pair ?_ ?_
  · intro C hC
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hC ⊢
    exact prop145_pair_good B phi C hC
  · intro C _ D _ hCD
    exact prop145_pair_injective hCD

/-- **Corollary 14.5.** Product property gives the same lower bound for
respected congruent cube pairs. -/
theorem corollary_14_5_holds : corollary_14_5 := by
  intro N k _ beta gamma B phi hk hbeta hgamma hgamma_one hcard hproduct
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact (lemma_14_4_holds N (n + 1) beta gamma B phi (by omega) hbeta hgamma
    hgamma_one hcard hproduct).trans (by exact_mod_cast prop145_count_le B phi)

end LeanProofs.GowersSzemeredi
