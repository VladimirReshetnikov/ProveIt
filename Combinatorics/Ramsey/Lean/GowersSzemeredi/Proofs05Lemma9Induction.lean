import GowersSzemeredi.Proofs05Lemma9
import GowersSzemeredi.Proofs05Downstream
import Mathlib.Data.Fintype.EquivFin

/-!
# The refinement engine for Lemma 5.9

This module separates the combinatorial induction needed for simultaneous
polynomial partitioning from its quantitative scale schedule.  Its first
layer transports the strong one-polynomial API from an index interval to an
arbitrary proper natural-number progression.  All progressions remain in the
original natural index set; no modular injectivity beyond `r <= N` is hidden
in the construction.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-! ## Natural-progression transport -/

/-- The point of `P` with natural index `t`. -/
def section5NatIndexPoint (P : NatAP) (t : Nat) : Nat :=
  P.start + t * P.step

/-- Composition of a progression of indices with a natural progression. -/
def section5NatTransport (P R : NatAP) : NatAP where
  start := section5NatIndexPoint P R.start
  step := R.step * P.step
  length := R.length

@[simp] theorem section5NatTransport_length (P R : NatAP) :
    (section5NatTransport P R).length = R.length :=
  rfl

theorem section5Nat_carrier_eq_image_range (P : NatAP) :
    P.carrier = (Finset.range P.length).image (section5NatIndexPoint P) := by
  classical
  ext x
  unfold NatAP.carrier section5NatIndexPoint
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.isLt, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩

theorem section5NatTransport_carrier (P R : NatAP) :
    (section5NatTransport P R).carrier =
      R.carrier.image (section5NatIndexPoint P) := by
  classical
  ext x
  simp only [NatAP.carrier, section5NatTransport, section5NatIndexPoint,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨R.start + (i : Nat) * R.step, ⟨i, rfl⟩, ?_⟩
    ring
  · rintro ⟨t, ⟨i, rfl⟩, rfl⟩
    refine ⟨i, ?_⟩
    ring

theorem section5NatIndexPoint_injective (P : NatAP) (hstep : 0 < P.step) :
    Function.Injective (section5NatIndexPoint P) := by
  intro x y hxy
  unfold section5NatIndexPoint at hxy
  exact Nat.mul_right_cancel hstep (Nat.add_left_cancel hxy)

theorem section5NatTransport_isProper (P R : NatAP)
    (hP : P.IsProper) (hR : R.IsProper) :
    (section5NatTransport P R).IsProper := by
  classical
  constructor
  · exact Nat.mul_pos hR.1 hP.1
  · rw [section5NatTransport_carrier, Finset.card_image_iff.mpr]
    · exact hR.2
    · exact (section5NatIndexPoint_injective P hP.1).injOn

theorem section5NatTransport_subset (P R : NatAP)
    (hR : R.carrier ⊆ Finset.range P.length) :
    (section5NatTransport P R).carrier ⊆ P.carrier := by
  classical
  rw [section5NatTransport_carrier]
  rw [section5Nat_carrier_eq_image_range P]
  exact Finset.image_mono (section5NatIndexPoint P) hR

/-- Transporting an interval partition through a proper natural progression
gives a partition of that progression. -/
theorem section5NatTransport_partition {M : Nat} (P : NatAP)
    (R : Fin M -> NatAP) (hP : P.IsProper)
    (hR : IsNatAPPartition R (Finset.range P.length)) :
    IsNatAPPartition (fun j => section5NatTransport P (R j)) P.carrier := by
  classical
  have hinj := section5NatIndexPoint_injective P hP.1
  constructor
  · intro x
    constructor
    · intro hx
      rw [section5Nat_carrier_eq_image_range] at hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j, htj⟩ := (hR.1 t).mp ht
      refine ⟨j, ?_⟩
      change section5NatIndexPoint P t ∈ (section5NatTransport P (R j)).carrier
      rw [section5NatTransport_carrier]
      exact Finset.mem_image.mpr ⟨t, htj, rfl⟩
    · rintro ⟨j, hx⟩
      exact section5NatTransport_subset P (R j)
        (IsPartition.cell_subset hR j) hx
  · intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    change x ∈ (section5NatTransport P (R i)).carrier at hxi
    change x ∈ (section5NatTransport P (R j)).carrier at hxj
    rw [section5NatTransport_carrier] at hxi hxj
    obtain ⟨s, hsi, hsx⟩ := Finset.mem_image.mp hxi
    obtain ⟨t, htj, htx⟩ := Finset.mem_image.mp hxj
    have hst : s = t := hinj (hsx.trans htx.symm)
    subst t
    exact Finset.disjoint_left.mp (hR.2 i j hij) hsi htj

theorem section5NatIndexPoint_cast {N : Nat} (P : NatAP) (t : Nat) :
    (section5NatIndexPoint P t : ZMod N) =
      (P.start : ZMod N) + (t : ZMod N) * (P.step : ZMod N) := by
  unfold section5NatIndexPoint
  push_cast
  rfl

theorem polynomialOn_section5NatIndexPoint {N k : Nat} [NeZero N]
    (P : NatAP) (phi : ZMod N -> ZMod N)
    (hphi : PolynomialOn k Finset.univ phi) :
    PolynomialOn k Finset.univ
      (fun x => phi ((P.start : ZMod N) + x * (P.step : ZMod N))) :=
  polynomialOn_affine_pullback phi (P.start : ZMod N) (P.step : ZMod N) hphi

private theorem section5NatTransport_image_phi {N : Nat} (P R : NatAP)
    (phi : ZMod N -> ZMod N) :
    (section5NatTransport P R).carrier.image
        (fun x : Nat => phi (x : ZMod N)) =
      R.carrier.image (fun t : Nat =>
        phi ((P.start : ZMod N) + (t : ZMod N) * (P.step : ZMod N))) := by
  classical
  rw [section5NatTransport_carrier, Finset.image_image]
  apply Finset.image_congr
  intro t _ht
  change phi (section5NatIndexPoint P t : ZMod N) = _
  rw [section5NatIndexPoint_cast]

/-! ## The strong local refinement theorem -/

/-- The strong Corollary 5.6 API transported to an arbitrary proper natural
progression. -/
theorem section5_strong_nat_refinement_of_corollary_5_6
    (hstrong : corollary_5_6_strong_diameter)
    {N k u : Nat} [NeZero N] (P : NatAP)
    (phi : ZMod N -> ZMod N) (hP : P.IsProper)
    (hPN : P.length <= N) (hk : 1 <= k)
    (hphi : PolynomialOn k Finset.univ phi)
    (hthreshold : polynomialPartitionThreshold k < P.length)
    (hu : 1 <= u)
    (huupper : (u : Real) <=
      (P.length : Real) ^ (polynomialPartitionConstant k : Real)⁻¹) :
    exists L : Nat, exists Q : Fin L -> NatAP,
      0 < L /\ IsNatAPPartition Q P.carrier /\
      (forall j, (Q j).IsProper /\ 0 < (Q j).length /\
        ((Q j).length = u - 1 \/ (Q j).length = u)) /\
      (forall j, (Q j).carrier ⊆ P.carrier) /\
      forall j, diameterAtMostReal
        ((Q j).carrier.image fun x : Nat => phi (x : ZMod N))
        ((P.length : Real) ^
          (-(2 * (polynomialPartitionConstant k : Real)⁻¹)) * N) := by
  classical
  let pulledPhi : ZMod N -> ZMod N := fun x =>
    phi ((P.start : ZMod N) + x * (P.step : ZMod N))
  have hpulled : PolynomialOn k Finset.univ pulledPhi :=
    polynomialOn_section5NatIndexPoint P phi hphi
  obtain ⟨L, R, hL, hpartition, hcells, hdiameter⟩ :=
    hstrong N k P.length u pulledPhi hk hpulled hthreshold hPN
      (by omega) huupper
  let Q : Fin L -> NatAP := fun j => section5NatTransport P (R j)
  have hQpartition : IsNatAPPartition Q P.carrier :=
    section5NatTransport_partition P R hP hpartition
  have hQcells (j : Fin L) :
      (Q j).IsProper /\ 0 < (Q j).length /\
        ((Q j).length = u - 1 \/ (Q j).length = u) := by
    refine ⟨section5NatTransport_isProper P (R j) hP (hcells j).1, ?_, ?_⟩
    · simpa only [Q, section5NatTransport_length] using (hcells j).2.1
    · simpa only [Q, section5NatTransport_length] using (hcells j).2.2
  refine ⟨L, Q, hL, hQpartition, hQcells, ?_, ?_⟩
  · intro j
    exact IsPartition.cell_subset hQpartition j
  · intro j
    simpa only [Q, pulledPhi, section5NatTransport_image_phi] using hdiameter j

/-! ## Monotonicity needed by the iteration -/

theorem diameterAtMostReal_mono {N : Nat} {A B : Finset (ZMod N)}
    {s t : Real} (hAB : A ⊆ B) (hB : diameterAtMostReal B s)
    (hst : s <= t) : diameterAtMostReal A t := by
  obtain ⟨d, hd, hdscale⟩ := hB
  obtain ⟨a, ha⟩ := hd
  exact ⟨d, ⟨a, hAB.trans ha⟩, hdscale.trans hst⟩

theorem section5_image_mono {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    {A B : Finset X} (f : X -> Y) (hAB : A ⊆ B) :
    A.image f ⊆ B.image f :=
  Finset.image_mono f hAB

/-! ## Dependent flattening for natural progressions -/

/-- The canonical finite reindexing used to flatten dependent refinements. -/
noncomputable def section5NatFlattenEquiv {M : Nat} (L : Fin M -> Nat) :
    (Sigma fun i : Fin M => Fin (L i)) ≃ Fin (∑ i, L i) :=
  Fintype.equivFinOfCardEq (by simp)

/-- Flatten a dependent family of natural progressions. -/
noncomputable def section5NatFlatten {M : Nat} (L : Fin M -> Nat)
    (R : (i : Fin M) -> Fin (L i) -> NatAP) :
    Fin (∑ i, L i) -> NatAP := fun j =>
  let z := (section5NatFlattenEquiv L).symm j
  R z.1 z.2

private theorem section5Nat_sigma_partition {X : Type*} [DecidableEq X]
    {M : Nat} (L : Fin M -> Nat) (A : Fin M -> Finset X) (S : Finset X)
    (B : (i : Fin M) -> Fin (L i) -> Finset X)
    (hA : IsPartition A S) (hB : forall i, IsPartition (B i) (A i)) :
    (forall x, x ∈ S <->
      exists z : Sigma fun i : Fin M => Fin (L i), x ∈ B z.1 z.2) /\
      forall z w : Sigma fun i : Fin M => Fin (L i), z != w ->
        Disjoint (B z.1 z.2) (B w.1 w.2) := by
  constructor
  · intro x
    rw [hA.1]
    constructor
    · rintro ⟨i, hi⟩
      obtain ⟨j, hj⟩ := (hB i).1 x |>.mp hi
      exact ⟨⟨i, j⟩, hj⟩
    · rintro ⟨⟨i, j⟩, hij⟩
      exact ⟨i, (hB i).1 x |>.mpr ⟨j, hij⟩⟩
  · intro z w hzw
    have hzw' : z ≠ w := bne_iff_ne.mp hzw
    by_cases hi : z.1 = w.1
    · rcases z with ⟨i, j⟩
      rcases w with ⟨i', j'⟩
      dsimp only at hi ⊢
      subst i'
      have hj : j ≠ j' := by
        intro h
        subst j'
        exact hzw' rfl
      exact (hB i).2 j j' (bne_iff_ne.mpr hj)
    · exact Disjoint.mono (IsPartition.cell_subset (hB z.1) z.2)
        (IsPartition.cell_subset (hB w.1) w.2)
        (hA.2 z.1 w.1 (bne_iff_ne.mpr hi))

/-- Flattening dependent local partitions gives a partition of the original
natural progression. -/
theorem section5NatFlatten_partition {M : Nat} (P : Fin M -> NatAP)
    (S : Finset Nat) (L : Fin M -> Nat)
    (R : (i : Fin M) -> Fin (L i) -> NatAP)
    (hP : IsNatAPPartition P S)
    (hR : forall i, IsNatAPPartition (R i) (P i).carrier) :
    IsNatAPPartition (section5NatFlatten L R) S := by
  classical
  let e := section5NatFlattenEquiv L
  have hsigma := section5Nat_sigma_partition L (fun i => (P i).carrier) S
    (fun i j => (R i j).carrier) hP hR
  constructor
  · intro x
    rw [hsigma.1 x]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨e z, ?_⟩
      change x ∈
        (R ((section5NatFlattenEquiv L).symm (section5NatFlattenEquiv L z)).1
          ((section5NatFlattenEquiv L).symm (section5NatFlattenEquiv L z)).2).carrier
      rw [(section5NatFlattenEquiv L).symm_apply_apply z]
      exact hz
    · rintro ⟨j, hj⟩
      refine ⟨e.symm j, ?_⟩
      simpa only [section5NatFlatten, e] using hj
  · intro i j hij
    have hij' : i ≠ j := bne_iff_ne.mp hij
    have hpre : e.symm i ≠ e.symm j := fun h => hij' (e.symm.injective h)
    simpa only [section5NatFlatten, e] using
      hsigma.2 (e.symm i) (e.symm j) (bne_iff_ne.mpr hpre)

theorem section5NatFlatten_isProper {M : Nat} (L : Fin M -> Nat)
    (R : (i : Fin M) -> Fin (L i) -> NatAP)
    (hR : forall i j, (R i j).IsProper) :
    forall j, (section5NatFlatten L R j).IsProper := by
  intro j
  let z := (section5NatFlattenEquiv L).symm j
  simpa only [section5NatFlatten, z] using hR z.1 z.2

theorem section5NatFlatten_subset {M : Nat} (P : NatAP)
    (L : Fin M -> Nat) (R : (i : Fin M) -> Fin (L i) -> NatAP)
    (hR : forall i j, (R i j).carrier ⊆ P.carrier) :
    forall j, (section5NatFlatten L R j).carrier ⊆ P.carrier := by
  intro j
  let z := (section5NatFlattenEquiv L).symm j
  simpa only [section5NatFlatten, z] using hR z.1 z.2

/-! ## An exact branch-sensitive schedule -/

/-- A branch-sensitive schedule for iterating the strong one-polynomial
refinement.  Both possible child lengths are recorded, so no rounding choice
is silently discarded.  `globalScale` is the final diameter coefficient,
before multiplication by `N`. -/
def section5StrongRefinementSchedule (k : Nat) (globalScale : Real) :
    Nat -> List Nat -> Prop
  | _t, [] => True
  | t, u :: us =>
      polynomialPartitionThreshold k < t /\
      1 <= u /\
      (u : Real) <=
        (t : Real) ^ (polynomialPartitionConstant k : Real)⁻¹ /\
      (t : Real) ^ (-(2 * (polynomialPartitionConstant k : Real)⁻¹)) <=
        globalScale /\
      section5StrongRefinementSchedule k globalScale (u - 1) us /\
      section5StrongRefinementSchedule k globalScale u us

private lemma section5StrongRefinementSchedule_tail_of_length
    {k t u ell : Nat} {globalScale : Real} {us : List Nat}
    (hschedule : section5StrongRefinementSchedule k globalScale t (u :: us))
    (hell : ell = u - 1 \/ ell = u) :
    section5StrongRefinementSchedule k globalScale ell us := by
  rcases hell with rfl | rfl
  · exact hschedule.2.2.2.2.1
  · exact hschedule.2.2.2.2.2

/-- Increasing the current cell length preserves a valid schedule. -/
theorem section5StrongRefinementSchedule_mono {k s t : Nat}
    {globalScale : Real} {targets : List Nat} (hst : s <= t)
    (hs : section5StrongRefinementSchedule k globalScale s targets) :
    section5StrongRefinementSchedule k globalScale t targets := by
  cases targets with
  | nil => trivial
  | cons u us =>
      have hsPos : 0 < s := by
        have hthreshold := hs.1
        omega
      have hcast : (s : Real) <= t := by exact_mod_cast hst
      have hKInv : 0 <= (polynomialPartitionConstant k : Real)⁻¹ := by positivity
      have htarget :
          (u : Real) <=
            (t : Real) ^ (polynomialPartitionConstant k : Real)⁻¹ := by
        exact hs.2.2.1.trans
          (Real.rpow_le_rpow (by positivity) hcast hKInv)
      have hnegative :
          -(2 * (polynomialPartitionConstant k : Real)⁻¹) <= 0 := by
        exact neg_nonpos.mpr (mul_nonneg (by norm_num) hKInv)
      have hdiameter :
          (t : Real) ^ (-(2 * (polynomialPartitionConstant k : Real)⁻¹)) <=
            globalScale := by
        exact (Real.rpow_le_rpow_of_nonpos
          (by exact_mod_cast hsPos) hcast hnegative).trans hs.2.2.2.1
      exact ⟨hs.1.trans_le hst, hs.2.1, htarget, hdiameter,
        hs.2.2.2.2.1, hs.2.2.2.2.2⟩

/-- It is enough to verify the continuation on the shorter `u - 1` branch;
monotonicity supplies the `u` branch. -/
theorem section5StrongRefinementSchedule_cons_of_min
    {k t u : Nat} {globalScale : Real} {targets : List Nat}
    (hthreshold : polynomialPartitionThreshold k < t) (hu : 1 <= u)
    (huupper : (u : Real) <=
      (t : Real) ^ (polynomialPartitionConstant k : Real)⁻¹)
    (hdiameter :
      (t : Real) ^ (-(2 * (polynomialPartitionConstant k : Real)⁻¹)) <=
        globalScale)
    (htail : section5StrongRefinementSchedule k globalScale (u - 1) targets) :
    section5StrongRefinementSchedule k globalScale t (u :: targets) := by
  refine ⟨hthreshold, hu, huupper, hdiameter, htail, ?_⟩
  exact section5StrongRefinementSchedule_mono (by omega : u - 1 <= u) htail

private lemma section5_getLast?_tail_of_cons {X : Type*} {a v : X}
    {l : List X} (hl : l ≠ []) (h : (a :: l).getLast? = some v) :
    l.getLast? = some v := by
  cases l with
  | nil => exact (hl rfl).elim
  | cons b l => simpa using h

/-! ## Iteration over a nonempty list of polynomials -/

/-- Iterating the local strong refinement along an explicit branch-sensitive
schedule.  The theorem is independent of the later quantitative construction
of such a schedule. -/
theorem section5_iterated_strong_nat_refinement
    (hstrong : corollary_5_6_strong_diameter) {N k : Nat} [NeZero N]
    (hk : 1 <= k) (globalScale : Real) :
    forall (functions : List (ZMod N -> ZMod N)) (targets : List Nat),
      functions.length = targets.length -> functions ≠ [] ->
      forall (P : NatAP), P.IsProper -> 0 < P.length -> P.length <= N ->
      (forall phi, phi ∈ functions -> PolynomialOn k Finset.univ phi) ->
      section5StrongRefinementSchedule k globalScale P.length targets ->
      forall v : Nat, targets.getLast? = some v ->
      exists M : Nat, exists Q : Fin M -> NatAP,
        0 < M /\ IsNatAPPartition Q P.carrier /\
        (forall j, (Q j).IsProper /\ 0 < (Q j).length /\
          ((Q j).length = v - 1 \/ (Q j).length = v)) /\
        (forall j, (Q j).carrier ⊆ P.carrier) /\
        forall phi, phi ∈ functions -> forall j,
          diameterAtMostReal
            ((Q j).carrier.image fun x : Nat => phi (x : ZMod N))
            (globalScale * N) := by
  intro functions
  induction functions with
  | nil =>
      intro targets hlength hnonempty
      exact (hnonempty rfl).elim
  | cons phi functions ih =>
      intro targets hlength _hnonempty P hP hPpos hPN hpolys hschedule v hlast
      cases targets with
      | nil => simp at hlength
      | cons u targets =>
          have hlengthTail : functions.length = targets.length := by
            simpa using Nat.succ.inj hlength
          have hphi : PolynomialOn k Finset.univ phi :=
            hpolys phi (by simp)
          obtain ⟨L, R, hL, hRpartition, hRcells, hRsubset, hRdiameter⟩ :=
            section5_strong_nat_refinement_of_corollary_5_6 hstrong P phi hP hPN
              hk hphi hschedule.1 hschedule.2.1 hschedule.2.2.1
          by_cases hfunctions : functions = []
          · subst functions
            have htargets : targets = [] :=
              List.eq_nil_of_length_eq_zero hlengthTail.symm
            subst targets
            simp only [List.getLast?_singleton, Option.some.injEq] at hlast
            subst v
            refine ⟨L, R, hL, hRpartition, hRcells, hRsubset, ?_⟩
            intro psi hpsi j
            have hpsiEq : psi = phi := by simpa using hpsi
            subst psi
            obtain ⟨d, hd, hdscale⟩ := hRdiameter j
            refine ⟨d, hd, hdscale.trans ?_⟩
            exact mul_le_mul_of_nonneg_right hschedule.2.2.2.1 (by positivity)
          · have htargets : targets ≠ [] := by
              intro ht
              subst targets
              exact hfunctions (List.eq_nil_of_length_eq_zero hlengthTail)
            choose M Q hM hQpartition hQcells hQsubset hQdiameter using
              fun i : Fin L =>
                ih targets hlengthTail hfunctions (R i) (hRcells i).1
                  (hRcells i).2.1
                  (by
                    calc
                      (R i).length = (R i).carrier.card := (hRcells i).1.2.symm
                      _ <= P.carrier.card := Finset.card_le_card (hRsubset i)
                      _ = P.length := hP.2
                      _ <= N := hPN)
                  (fun psi hpsi => hpolys psi (by simp [hpsi]))
                  (section5StrongRefinementSchedule_tail_of_length hschedule
                    (hRcells i).2.2)
                  v (section5_getLast?_tail_of_cons htargets hlast)
            let F : Fin (∑ i, M i) -> NatAP := section5NatFlatten M Q
            have hFpartition : IsNatAPPartition F P.carrier :=
              section5NatFlatten_partition R P.carrier M Q hRpartition hQpartition
            have hFproper : forall j, (F j).IsProper :=
              section5NatFlatten_isProper M Q (fun i j => (hQcells i j).1)
            have hFsubset : forall j, (F j).carrier ⊆ P.carrier := by
              apply section5NatFlatten_subset P M Q
              intro i j
              exact (hQsubset i j).trans (hRsubset i)
            have hMsum : 0 < ∑ i, M i := by
              let i : Fin L := ⟨0, hL⟩
              have hle : M i <= ∑ j, M j := by
                exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
              exact (hM i).trans_le hle
            refine ⟨∑ i, M i, F, hMsum, hFpartition, ?_, hFsubset, ?_⟩
            · intro j
              let z := (section5NatFlattenEquiv M).symm j
              simpa only [F, section5NatFlatten, z] using hQcells z.1 z.2
            · intro psi hpsi j
              rcases List.mem_cons.mp hpsi with hpsiHead | hpsiTail
              · subst psi
                let z := (section5NatFlattenEquiv M).symm j
                have hsub : (F j).carrier ⊆ (R z.1).carrier := by
                  simpa only [F, section5NatFlatten, z] using hQsubset z.1 z.2
                apply diameterAtMostReal_mono
                  (section5_image_mono (fun x : Nat => phi (x : ZMod N)) hsub)
                  (hRdiameter z.1)
                exact mul_le_mul_of_nonneg_right hschedule.2.2.2.1 (by positivity)
              · let z := (section5NatFlattenEquiv M).symm j
                simpa only [F, section5NatFlatten, z] using
                  hQdiameter z.1 psi hpsiTail z.2

/-! ## Reduction of the live statement to a quantitative schedule -/

/-- The initial natural progression whose carrier is `range r`. -/
def section5RangeNatAP (r : Nat) : NatAP where
  start := 0
  step := 1
  length := r

@[simp] theorem section5RangeNatAP_length (r : Nat) :
    (section5RangeNatAP r).length = r :=
  rfl

@[simp] theorem section5RangeNatAP_carrier (r : Nat) :
    (section5RangeNatAP r).carrier = Finset.range r := by
  classical
  ext x
  simp only [NatAP.carrier, section5RangeNatAP, Finset.mem_image,
    Finset.mem_univ, true_and, Finset.mem_range, zero_add, mul_one]
  constructor
  · rintro ⟨i, rfl⟩
    exact i.isLt
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem section5RangeNatAP_isProper (r : Nat) :
    (section5RangeNatAP r).IsProper := by
  constructor
  · simp [section5RangeNatAP]
  · simp

/-- The remaining purely quantitative assertion needed by the strong
refinement engine: the repaired live hypotheses produce a finite target list
which is safe on both rounding branches. -/
def lemma_5_9_scale_schedule : Prop :=
  forall (k q r v : Nat),
    1 <= k -> 1 <= q -> simultaneousPolynomialThreshold k q < r ->
    1 <= v -> (v : Real) <=
      (r : Real) ^
        (2 * (polynomialPartitionConstant k : Real) ^ q)⁻¹ ->
      exists targets : List Nat,
        targets.length = q /\ targets.getLast? = some v /\
        section5StrongRefinementSchedule k
          ((r : Real) ^
            (-((polynomialPartitionConstant k : Real) ^ q)⁻¹))
          r targets

/-- The canonical target list: use the largest integral `K`-th-root target
until the last stage, where the prescribed final target `v` is used. -/
def section5MaximalTargets (K : Nat) : Nat -> Nat -> Nat -> List Nat
  | 0, _t, _v => []
  | 1, _t, v => [v]
  | q + 2, t, v =>
      let u := Nat.floor ((t : Real) ^ (K : Real)⁻¹)
      u :: section5MaximalTargets K (q + 1) (u - 1) v

theorem section5MaximalTargets_length (K q t v : Nat) :
    (section5MaximalTargets K q t v).length = q := by
  match q with
  | 0 => simp [section5MaximalTargets]
  | 1 => simp [section5MaximalTargets]
  | q + 2 =>
      simp only [section5MaximalTargets, List.length_cons]
      rw [section5MaximalTargets_length K (q + 1)]
termination_by q

private lemma section5_getLast?_cons_of_eq_some {X : Type*} {a v : X}
    {l : List X} (h : l.getLast? = some v) :
    (a :: l).getLast? = some v := by
  cases l with
  | nil => simp at h
  | cons b l => simpa using h

theorem section5MaximalTargets_getLast? (K q t v : Nat) (hq : 1 <= q) :
    (section5MaximalTargets K q t v).getLast? = some v := by
  match q with
  | 0 => omega
  | 1 => simp [section5MaximalTargets]
  | q + 2 =>
      simp only [section5MaximalTargets]
      apply section5_getLast?_cons_of_eq_some
      exact section5MaximalTargets_getLast? K (q + 1)
        (Nat.floor ((t : Real) ^ (K : Real)⁻¹) - 1) v (by omega)
termination_by q

/-- The last remaining analytic-arithmetic estimate in the maximal-target
construction.  It is kept separate from the combinatorial induction so the
three quantitative obligations (threshold, target, and diameter) are visible
in the resulting goal. -/
def lemma_5_9_maximal_target_bounds : Prop :=
  forall (k q r v : Nat),
    1 <= k -> 1 <= q -> simultaneousPolynomialThreshold k q < r ->
    1 <= v -> (v : Real) <=
      (r : Real) ^
        (2 * (polynomialPartitionConstant k : Real) ^ q)⁻¹ ->
      section5StrongRefinementSchedule k
        ((r : Real) ^
          (-((polynomialPartitionConstant k : Real) ^ q)⁻¹))
        r (section5MaximalTargets (polynomialPartitionConstant k) q r v)

/-- The maximal-target estimate is exact in the one-polynomial base case. -/
theorem lemma_5_9_maximal_target_bounds_one
    {k r v : Nat}
    (hthreshold : simultaneousPolynomialThreshold k 1 < r)
    (hv : 1 <= v)
    (hvupper : (v : Real) <=
      (r : Real) ^
        (2 * (polynomialPartitionConstant k : Real) ^ (1 : Nat))⁻¹) :
    section5StrongRefinementSchedule k
      ((r : Real) ^
        (-((polynomialPartitionConstant k : Real) ^ (1 : Nat))⁻¹))
      r (section5MaximalTargets (polynomialPartitionConstant k) 1 r v) := by
  have hthreshold' : polynomialPartitionThreshold k < r := by
    have htwo : 2 * polynomialPartitionThreshold k < r := by
      simpa only [simultaneousPolynomialThreshold, Nat.sub_self, pow_zero,
        pow_one] using hthreshold
    omega
  have hrOneNat : 1 <= r := by omega
  have hrOne : (1 : Real) <= r := by exact_mod_cast hrOneNat
  have hKPos : (0 : Real) < polynomialPartitionConstant k := by
    unfold polynomialPartitionConstant
    positivity
  have hexponentTarget :
      (2 * (polynomialPartitionConstant k : Real))⁻¹ <=
        (polynomialPartitionConstant k : Real)⁻¹ := by
    exact (inv_le_inv₀ (by positivity) hKPos).2 (by nlinarith)
  have htarget :
      (v : Real) <=
        (r : Real) ^ (polynomialPartitionConstant k : Real)⁻¹ := by
    calc
      (v : Real) <=
          (r : Real) ^ (2 * (polynomialPartitionConstant k : Real))⁻¹ := by
        simpa only [pow_one] using hvupper
      _ <= (r : Real) ^ (polynomialPartitionConstant k : Real)⁻¹ :=
        Real.rpow_le_rpow_of_exponent_le hrOne hexponentTarget
  have hexponentDiameter :
      -(2 * (polynomialPartitionConstant k : Real)⁻¹) <=
        -(polynomialPartitionConstant k : Real)⁻¹ := by
    have hnonneg : 0 <= (polynomialPartitionConstant k : Real)⁻¹ := by positivity
    linarith
  have hdiameter :
      (r : Real) ^ (-(2 * (polynomialPartitionConstant k : Real)⁻¹)) <=
        (r : Real) ^ (-(polynomialPartitionConstant k : Real)⁻¹) :=
    Real.rpow_le_rpow_of_exponent_le hrOne hexponentDiameter
  simpa only [section5MaximalTargets, pow_one] using
    (show section5StrongRefinementSchedule k
        ((r : Real) ^ (-(polynomialPartitionConstant k : Real)⁻¹)) r [v] from
      ⟨hthreshold', hv, htarget, hdiameter, trivial, trivial⟩)

theorem lemma_5_9_scale_schedule_holds_of_maximal_target_bounds
    (hmaximal : lemma_5_9_maximal_target_bounds) : lemma_5_9_scale_schedule := by
  intro k q r v hk hq hthreshold hv hvupper
  refine ⟨section5MaximalTargets (polynomialPartitionConstant k) q r v,
    section5MaximalTargets_length _ _ _ _,
    section5MaximalTargets_getLast? _ _ _ _ hq, ?_⟩
  exact hmaximal k q r v hk hq hthreshold hv hvupper

/-- Once the branch-sensitive scale schedule is supplied, the strong
one-polynomial diameter theorem proves the full live Lemma 5.9 statement. -/
theorem lemma_5_9_holds_of_strong_diameter_and_scale_schedule
    (hstrong : corollary_5_6_strong_diameter)
    (hschedule : lemma_5_9_scale_schedule) : lemma_5_9 := by
  intro N k q r v _ phi hk hq hphi hthreshold hrN hv hvupper
  obtain ⟨targets, htargetsLength, htargetsLast, htargetsSchedule⟩ :=
    hschedule k q r v hk hq hthreshold hv hvupper
  let functions : List (ZMod N -> ZMod N) := List.ofFn phi
  have hfunctionsLength : functions.length = targets.length := by
    simpa only [functions, List.length_ofFn] using htargetsLength.symm
  have hfunctionsNonempty : functions ≠ [] := by
    intro hnil
    have hzero : functions.length = 0 := by simp [hnil]
    have hlengthQ : functions.length = q := by
      simp only [functions, List.length_ofFn]
    omega
  have hfunctionsPolynomial :
      forall psi, psi ∈ functions -> PolynomialOn k Finset.univ psi := by
    intro psi hpsi
    change psi ∈ List.ofFn phi at hpsi
    rw [List.mem_ofFn'] at hpsi
    obtain ⟨i, rfl⟩ := hpsi
    exact hphi i
  obtain ⟨M, P, hM, hpartition, hcells, hsubset, hdiameter⟩ :=
    section5_iterated_strong_nat_refinement hstrong hk
      ((r : Real) ^ (-((polynomialPartitionConstant k : Real) ^ q)⁻¹))
      functions targets hfunctionsLength hfunctionsNonempty
      (section5RangeNatAP r) (section5RangeNatAP_isProper r)
      (by
        simpa only [section5RangeNatAP_length] using
          (lt_of_le_of_lt (Nat.zero_le _) hthreshold))
      hrN hfunctionsPolynomial htargetsSchedule v htargetsLast
  refine ⟨M, P, hM, ?_, hcells, ?_⟩
  · simpa only [section5RangeNatAP_carrier] using hpartition
  · intro i j
    have hmem : phi i ∈ functions := by
      change phi i ∈ List.ofFn phi
      rw [List.mem_ofFn']
      exact ⟨i, rfl⟩
    exact hdiameter (phi i) hmem j

end LeanProofs.GowersSzemeredi
