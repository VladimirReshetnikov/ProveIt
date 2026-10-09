import GowersSzemeredi.Proofs05SchmidtRecurrence
import GowersSzemeredi.Proofs05SimultaneousMultiaffineStep

/-! Simultaneous multiaffine partitions with polynomial dependence on family size.

For a downward-closed family of h square-free monomials in k > 0 variables,
there are constants K >= 2 and p > 0 such that q phases on a proper input box
of width at least H^(p*(q+1)^(2*h)), with H >= K*(q+1), share a proper box
partition of minimum width H and diameter at most h*N/H for each phase.

A common Schmidt recurrence removes one maximal monomial from every phase.
At scale T = H^(p*(q+1)^(2*h)), coarse cells have widths T or T+1;
the lower-height induction therefore applies without short tail cells.
The exponent bound accounts for both the recurrence multiplier and the
coarse partition's size requirement. Taking h = 2^k covers all multilinear
phases. Constants depend on dimension and monomial height, not family size;
no explicit all-length Szemeredi threshold is asserted.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace LeanProofs.GowersSzemeredi

theorem simultaneous_height_exponent_bound (k h p e d : Nat) (hp : 0 < p) :
    (2 + 2 * k * (p * (d + 1) ^ (2 * h))) * (e * (d + 1) ^ 2) +
      4 * (p * (d + 1) ^ (2 * h)) ≤
    (p * (2 * (k + 1) * e + 4)) * (d + 1) ^ (2 * (h + 1)) := by
  have hr : 1 ≤ p * (d + 1) ^ (2 * h) := Nat.mul_pos hp (by positivity)
  have hd : 1 ≤ (d + 1) ^ 2 := one_le_pow₀ (by omega)
  have ha : 2 + 2 * k * (p * (d + 1) ^ (2 * h)) ≤
      2 * (k + 1) * (p * (d + 1) ^ (2 * h)) := by nlinarith
  have hb := Nat.mul_le_mul_right (e * (d + 1) ^ 2) ha
  have hc := Nat.mul_le_mul_left (4 * (p * (d + 1) ^ (2 * h))) hd
  rw [show 2 * (h + 1) = 2 * h + 2 by omega, pow_add]
  nlinarith only [hb, hc]

private theorem simultaneous_constant_box_partition {N k : Nat} [NeZero N]
    (P : Box N k) (hP : P.IsProper) (q : Nat)
    (f : Fin q → Point N k → ZMod N) (a : Fin q → ZMod N)
    (hf : ∀ i x, f i x = a i) (H : Nat) (D : Real)
    (hH : H ≤ P.width) (hD : 0 ≤ D) :
    ∃ M : Nat, ∃ Q : Fin M → Box N k,
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
      (∀ j, (H : Real) ≤ (Q j).width) ∧
      ∀ i j, diameterAtMostReal ((Q j).carrier.image (f i)) D := by
  classical
  refine ⟨1, fun _ => P, ?_, fun _ => hP, fun _ => by exact_mod_cast hH, ?_⟩
  · constructor
    · intro x; simp
    · intro i j hij
      exact ((bne_iff_ne.mp hij) (Subsingleton.elim i j)).elim
  · intro i _
    refine ⟨0, ⟨a i, ?_⟩, by simpa using hD⟩
    intro y hy
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
    simp [hf, modInterval, ModAP.carrier]

def SimultaneousMultiaffinePartitionBound (k h : Nat) (K : Real) (p : Nat) : Prop :=
  ∀ (N : Nat) [NeZero N] (q : Nat) (F : Finset (Finset (Fin k))),
    MonomialFamilyClosed F → F.card = h →
    ∀ (c : Fin q → Finset (Fin k) → ZMod N) (P : Box N k), P.IsProper →
    ∀ H : Nat, 0 < H → K * ((q : Real) + 1) ≤ H →
      H ^ (p * (q + 1) ^ (2 * h)) ≤ P.width →
      ∃ M : Nat, ∃ Q : Fin M → Box N k,
        IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
        (∀ j, (H : Real) ≤ (Q j).width) ∧
        ∀ i j, diameterAtMostReal ((Q j).carrier.image (multiaffineEval F (c i)))
          ((h : Real) / H * N)

theorem simultaneousMultiaffinePartitionBound_zero (k : Nat) :
    SimultaneousMultiaffinePartitionBound k 0 2 1 := by
  intro N _ q F _ hcard c P hP H _ _ hsize
  have hF : F = ∅ := Finset.card_eq_zero.mp hcard
  apply simultaneous_constant_box_partition P hP q (fun i => multiaffineEval F (c i)) (fun _ => 0)
  · intro i x
    simp [hF, multiaffineEval]
  · simpa using hsize
  · simp

theorem SimultaneousMultiaffinePartitionBound.step {k h p e : Nat} {K C : Real}
    (hk : 0 < k) (hK : 2 ≤ K) (hp : 0 < p) (hC : 1 ≤ C)
    (hrec : UniformModularMonomialRecurrence k C e)
    (hpartition : SimultaneousMultiaffinePartitionBound k h K p) :
    SimultaneousMultiaffinePartitionBound k (h + 1) (max K C)
      (p * (2 * (k + 1) * e + 4)) := by
  classical
  intro N _ q F hF hcard c P hP H hH hscale hsize
  have hscaleK : K * ((q : Real) + 1) ≤ H :=
    (mul_le_mul_of_nonneg_right (le_max_left K C) (by positivity)).trans hscale
  have hscaleC : C * ((q : Real) + 1) ≤ H :=
    (mul_le_mul_of_nonneg_right (le_max_right K C) (by positivity)).trans hscale
  have hH2 : 2 ≤ H := by
    have hc : (1 : Real) ≤ (q : Real) + 1 := by norm_num
    have hh : (2 : Real) ≤ H :=
      hK.trans ((le_mul_of_one_le_right (by linarith : 0 ≤ K) hc).trans hscaleK)
    exact_mod_cast hh
  have hexppos : 0 < (p * (2 * (k + 1) * e + 4)) * (q + 1) ^ (2 * (h + 1)) := by positivity
  have hHP : H ≤ P.width := by
    apply le_trans _ hsize
    simpa only [pow_one] using (pow_le_pow_right₀ (by omega : 1 ≤ H) (show 1 ≤ _ by omega))
  have hFnonempty : F.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨A, hA, hmax⟩ := monomialFamily_exists_maximal F hFnonempty
  by_cases hAempty : A = ∅
  · have hFsingle : F = {∅} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨by simpa [hAempty] using hA, ?_⟩
      intro S hS
      simpa [hAempty] using hmax S hS (by simp [hAempty])
    apply simultaneous_constant_box_partition P hP q (fun i => multiaffineEval F (c i)) (fun i => c i ∅)
    · intro i x
      simp [hFsingle, multiaffineEval]
    · exact hHP
    · positivity
  have hd : 1 ≤ A.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hAempty)
  have hdk : A.card ≤ k := by simpa using Finset.card_le_univ A
  let r := p * (q + 1) ^ (2 * h)
  let T := H ^ r
  let u := T + 1
  let B := (2 + 2 * k * r) * (e * (q + 1) ^ 2)
  let M := H ^ B
  let R : Real := ((H : Real) * (u : Real) ^ k)⁻¹
  have hr : 0 < r := Nat.mul_pos hp (by positivity)
  have hT : 0 < T := pow_pos hH _
  have hHT : H ≤ T := by
    simpa only [pow_one] using (pow_le_pow_right₀ (by omega : 1 ≤ H) (show 1 ≤ r by omega))
  have hT2 : 2 ≤ T := hH2.trans hHT
  have hu : 1 ≤ u := by dsimp [u]; omega
  have huT : u ≤ T ^ 2 := by dsimp [u]; nlinarith
  have hHR : (0 : Real) < H := by exact_mod_cast hH
  have huR : (0 : Real) < u := by exact_mod_cast (show 0 < u by omega)
  have hR : 0 < R := by dsimp [R]; positivity
  have hR1 : R ≤ 1 := by
    apply (inv_le_one₀ (by positivity : (0 : Real) < H * (u : Real) ^ k)).mpr
    have hu1 : (1 : Real) ≤ (u : Real) ^ k := one_le_pow₀ (by exact_mod_cast hu)
    have hh1 : (1 : Real) ≤ H := by exact_mod_cast (show 1 ≤ H by omega)
    nlinarith
  have huPow : (u : Real) ^ k ≤ (H : Real) ^ (2 * k * r) := by
    have hh := Nat.pow_le_pow_left huT k
    dsimp [T] at hh
    rw [← pow_mul, ← pow_mul] at hh
    convert (show (u : Real) ^ k ≤ (H : Real) ^ (r * (2 * k)) by exact_mod_cast hh) using 1
    ring
  have hbase : C * ((q : Real) + 1) / R ≤ (H : Real) ^ (2 + 2 * k * r) := by
    dsimp [R]
    rw [div_inv_eq_mul]
    calc
      _ ≤ (H : Real) * (H * (u : Real) ^ k) := mul_le_mul_of_nonneg_right hscaleC (by positivity)
      _ ≤ (H : Real) * (H * (H : Real) ^ (2 * k * r)) := by gcongr
      _ = _ := by rw [pow_add]; ring
  have hM : (C * ((Fintype.card (Fin q) : Real) + 1) / R) ^
      (e * (Fintype.card (Fin q) + 1) ^ 2) ≤ M := by
    simp only [Fintype.card_fin]
    have hC0 : 0 ≤ C := (by norm_num : (0 : Real) ≤ 1).trans hC
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ C * ((q : Real) + 1) / R) hbase (e * (q + 1) ^ 2)
    simpa only [M, B, Nat.cast_pow, ← pow_mul] using hh
  obtain ⟨s, hs, hsM, hsmall⟩ := hrec N (Fin q)
    (fun i => c i A * P.commonDiff ^ A.card) M R hR hR1 hM ⟨A.card - 1, by omega⟩
  have hsu : s * u ^ 2 ≤ P.width := by
    calc
      _ ≤ M * (T ^ 2) ^ 2 := Nat.mul_le_mul hsM (Nat.pow_le_pow_left huT 2)
      _ = H ^ (B + 4 * r) := by dsimp [M, T]; rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
      _ ≤ H ^ ((p * (2 * (k + 1) * e + 4)) * (q + 1) ^ (2 * (h + 1))) :=
        pow_le_pow_right₀ (by omega) (simultaneous_height_exponent_bound k h p e q hp)
      _ ≤ P.width := hsize
  have hcoeff (i : Fin q) : (u : Real) ^ A.card *
      centeredAbs (c i A * ((s : ZMod N) * P.commonDiff) ^ A.card) ≤ (1 / H : Real) * N := by
    have hid : (s : ZMod N) ^ ((A.card - 1) + 1) * (c i A * P.commonDiff ^ A.card) =
        c i A * ((s : ZMod N) * P.commonDiff) ^ A.card := by
      rw [Nat.sub_add_cancel hd, mul_pow]
      ring
    have hh := hsmall i
    change (centeredAbs ((s : ZMod N) ^ ((A.card - 1) + 1) * (c i A * P.commonDiff ^ A.card)) : Real) < R * N at hh
    rw [hid] at hh
    calc
      _ ≤ (u : Real) ^ k * (R * N) := mul_le_mul
        (pow_le_pow_right₀ (by exact_mod_cast hu) hdk) hh.le (by positivity) (by positivity)
      _ = _ := by dsimp [R]; field_simp
  have hchild (Q : Box N k) (hQ : Q.IsProper) (hlow : u - 1 ≤ Q.width)
      (_hhigh : Q.width ≤ u) (c' : Fin q → Finset (Fin k) → ZMod N) :
      ∃ L : Nat, ∃ S : Fin L → Box N k,
        IsBoxPartition S Q ∧ (∀ j, (S j).IsProper) ∧
        (∀ j, (H : Real) ≤ (S j).width) ∧
        ∀ i j, diameterAtMostReal ((S j).carrier.image (multiaffineEval (F.erase A) (c' i)))
          ((h : Real) / H * N) := by
    apply hpartition N q (F.erase A) (hF.erase_maximal A hmax)
      (by rw [Finset.card_erase_of_mem hA, hcard]; omega) c' Q hQ H hH hscaleK
    simpa only [u, Nat.add_sub_cancel] using hlow
  obtain ⟨L, Q, hQpart, hQproper, hQwidth, hQdiam⟩ :=
    simultaneous_multiaffine_box_height_step hk F hF A hA hmax q c P hP s u hs hu hsu
      H ((h : Real) / H * N) ((1 / H : Real) * N) hHR hcoeff hchild
  refine ⟨L, Q, hQpart, hQproper, hQwidth, ?_⟩
  intro i j
  convert hQdiam i j using 1
  push_cast
  ring

theorem exists_simultaneous_multiaffine_partition_bound (k : Nat) (hk : 0 < k) (h : Nat) :
    ∃ (K : Real) (p : Nat), 2 ≤ K ∧ 0 < p ∧ SimultaneousMultiaffinePartitionBound k h K p := by
  obtain ⟨C, e, hC, he, hrec⟩ := exists_uniform_modular_monomial_recurrence k
  induction h with
  | zero => exact ⟨2, 1, le_rfl, by decide, simultaneousMultiaffinePartitionBound_zero k⟩
  | succ h ih =>
    obtain ⟨K, p, hK, hp, hpartition⟩ := ih
    exact ⟨max K C, p * (2 * (k + 1) * e + 4), hK.trans (le_max_left _ _),
      Nat.mul_pos hp (by omega), hpartition.step hk hK hp hC hrec⟩

/-- The multilinear partition statement in dimension `k` at constants `K, p`:
the body of `exists_simultaneous_multilinear_partition_bound`. -/
def MultilinearPartitionBoundAt (k : Nat) (K : Real) (p : Nat) : Prop :=
      ∀ (N : Nat) [NeZero N] (q : Nat) (P : Box N k), P.IsProper →
        ∀ mu : Fin q → Point N k → ZMod N, (∀ i, MultilinearOn P.carrier (mu i)) →
        ∀ H : Nat, 0 < H → K * ((q : Real) + 1) ≤ H →
          H ^ (p * (q + 1) ^ (2 * (2 ^ k))) ≤ P.width →
          ∃ M : Nat, ∃ Q : Fin M → Box N k,
            IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
            (∀ j, (H : Real) ≤ (Q j).width) ∧
            ∀ i j, diameterAtMostReal ((Q j).carrier.image (mu i)) ((2 ^ k : Real) / H * N)

/-- The multilinear partition from the multiaffine one at `2^k` monomial
families, with the same constants. -/
theorem multilinearPartitionBoundAt_of {k : Nat} {K : Real} {p : Nat}
    (hpartition : SimultaneousMultiaffinePartitionBound k (2 ^ k) K p) :
    MultilinearPartitionBoundAt k K p := by
  classical
  unfold MultilinearPartitionBoundAt
  intro N _ q P hP mu hmu H hH hscale hsize
  choose psi hpsi heq using hmu
  choose c hc using (fun i => (isMultilinear_iff_multiaffineEval (psi i)).mp (hpsi i))
  obtain ⟨M, Q, hQpart, hQproper, hQwidth, hQdiam⟩ := hpartition N q Finset.univ
    (fun _ _ _ _ => Finset.mem_univ _) (by simp) c P hP H hH hscale hsize
  refine ⟨M, Q, hQpart, hQproper, hQwidth, ?_⟩
  intro i j
  have himage : (Q j).carrier.image (mu i) = (Q j).carrier.image (multiaffineEval Finset.univ (c i)) := by
    apply Finset.image_congr
    intro x hx
    exact (heq i x (IsPartition.cell_subset hQpart j hx)).trans (hc i x)
  rw [himage]
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hQdiam i j

/-- All simultaneous multilinear phases on a proper box share a minimum-width
partition with polynomial family-size dependence in the required input width. -/
theorem exists_simultaneous_multilinear_partition_bound (k : Nat) (hk : 0 < k) :
    ∃ (K : Real) (p : Nat), 2 ≤ K ∧ 0 < p ∧
      ∀ (N : Nat) [NeZero N] (q : Nat) (P : Box N k), P.IsProper →
        ∀ mu : Fin q → Point N k → ZMod N, (∀ i, MultilinearOn P.carrier (mu i)) →
        ∀ H : Nat, 0 < H → K * ((q : Real) + 1) ≤ H →
          H ^ (p * (q + 1) ^ (2 * (2 ^ k))) ≤ P.width →
          ∃ M : Nat, ∃ Q : Fin M → Box N k,
            IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
            (∀ j, (H : Real) ≤ (Q j).width) ∧
            ∀ i j, diameterAtMostReal ((Q j).carrier.image (mu i)) ((2 ^ k : Real) / H * N) := by
  obtain ⟨K, p, hK, hp, hpartition⟩ := exists_simultaneous_multiaffine_partition_bound k hk (2 ^ k)
  exact ⟨K, p, hK, hp, multilinearPartitionBoundAt_of hpartition⟩

end LeanProofs.GowersSzemeredi
