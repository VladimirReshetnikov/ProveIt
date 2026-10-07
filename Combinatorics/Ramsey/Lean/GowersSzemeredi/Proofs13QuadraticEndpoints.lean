import GowersSzemeredi.Proofs13EndpointDeletion

/-! Quadratic interpolation controls the affine derivative at progression
endpoints. A factor-four diameter reserve avoids deleting any points. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

private theorem centeredAbs_add_bound {N : Nat} [NeZero N] (x y : ZMod N) :
    centeredAbs (x + y) ≤ centeredAbs x + centeredAbs y :=
  (ZMod.natAbs_valMinAbs_add_le x y).trans (Int.natAbs_add_le _ _)

private theorem centeredAbs_three_add_bound {N : Nat} [NeZero N] (x y : ZMod N) :
    centeredAbs (3 * x + y) ≤ 3 * centeredAbs x + centeredAbs y := by
  have h1 := centeredAbs_add_bound x x
  have h2 := centeredAbs_add_bound (x + x) x
  have h3 := centeredAbs_add_bound (x + x + x) y
  rw [show (3 : ZMod N) * x + y = x + x + x + y by ring]
  omega

theorem stage135Quadratic_forward_difference {N : Nat} [NeZero N]
    (hprime : N.Prime) (hodd : N != 2) (a b h d : ZMod N) :
    (a * h + b) * d =
      3 * (stage135AmbientQuadratic a b (h + d) - stage135AmbientQuadratic a b h) +
      (stage135AmbientQuadratic a b (h + d) - stage135AmbientQuadratic a b (h + 2 * d)) := by
  letI : Fact N.Prime := ⟨hprime⟩
  have htwo : (2 : ZMod N) ≠ 0 := by
    intro hz
    have hdvd : N ∣ 2 := (ZMod.natCast_eq_zero_iff 2 N).mp hz
    exact (bne_iff_ne.mp hodd) (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) hdvd) hprime.two_le)
  have hfour : (4 : ZMod N) ≠ 0 := by
    rw [show (4 : ZMod N) = 2 * 2 by norm_num]
    exact mul_ne_zero htwo htwo
  unfold stage135AmbientQuadratic
  field_simp [htwo, hfour]
  ring

theorem stage135_forward_small_affine_of_pairwise {N : Nat} [NeZero N]
    (hprime : N.Prime) (hodd : N != 2) (A : Finset (ZMod N)) (a b h d : ZMod N)
    {s : Real} (hpair : ∀ x ∈ A, ∀ y ∈ A,
      (centeredAbs (stage135AmbientQuadratic a b x - stage135AmbientQuadratic a b y) : Real) ≤ s)
    (hh : h ∈ A) (h1 : h + d ∈ A) (h2 : h + 2 * d ∈ A) :
    (centeredAbs ((a * h + b) * d) : Real) ≤ 4 * s := by
  classical
  have hd1 := hpair _ h1 _ hh
  have hd2 := hpair _ h1 _ h2
  rw [stage135Quadratic_forward_difference hprime hodd]
  have htriangle : (centeredAbs (3 * (stage135AmbientQuadratic a b (h + d) -
      stage135AmbientQuadratic a b h) + (stage135AmbientQuadratic a b (h + d) -
      stage135AmbientQuadratic a b (h + 2 * d))) : Real) ≤
      3 * centeredAbs (stage135AmbientQuadratic a b (h + d) - stage135AmbientQuadratic a b h) +
      centeredAbs (stage135AmbientQuadratic a b (h + d) - stage135AmbientQuadratic a b (h + 2 * d)) := by
    exact_mod_cast centeredAbs_three_add_bound
      (stage135AmbientQuadratic a b (h + d) - stage135AmbientQuadratic a b h)
      (stage135AmbientQuadratic a b (h + d) - stage135AmbientQuadratic a b (h + 2 * d))
  linarith

theorem stage135_full_cell_small_affine_of_pairwise {N : Nat} [NeZero N]
    (hprime : N.Prime) (hodd : N != 2) (Q : ModAP N) (hQ : 3 ≤ Q.length)
    (a b : ZMod N) {s : Real} (hs : 0 ≤ s)
    (hpair : ∀ x ∈ Q.carrier, ∀ y ∈ Q.carrier,
      (centeredAbs (stage135AmbientQuadratic a b x - stage135AmbientQuadratic a b y) : Real) ≤ s)
    {h : ZMod N} (hh : h ∈ Q.carrier) :
    (centeredAbs ((a * h + b) * Q.step) : Real) ≤ 4 * s := by
  classical
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hh
  have hi := i.isLt
  have hmem (j : Nat) (hj : j < Q.length) : Q.start + (j : ZMod N) * Q.step ∈ Q.carrier :=
    Finset.mem_image.mpr ⟨⟨j, hj⟩, Finset.mem_univ _, rfl⟩
  by_cases hi0 : i.val = 0
  · have h0 := hmem 0 (by omega)
    have h1 := hmem 1 (by omega)
    have h2 := hmem 2 (by omega)
    simp only [hi0, Nat.cast_zero, zero_mul, add_zero]
    apply stage135_forward_small_affine_of_pairwise hprime hodd Q.carrier a b Q.start Q.step hpair
    · simpa using h0
    · simpa using h1
    · simpa using h2
  · by_cases hlast : i.val + 1 = Q.length
    · have hb1 : Q.start + (i.val : ZMod N) * Q.step + -Q.step ∈ Q.carrier := by
        convert hmem (i.val - 1) (by omega) using 1
        rw [Nat.cast_sub (by omega : 1 ≤ i.val)]
        push_cast
        ring
      have hb2 : Q.start + (i.val : ZMod N) * Q.step + 2 * -Q.step ∈ Q.carrier := by
        convert hmem (i.val - 2) (by omega) using 1
        rw [Nat.cast_sub (by omega : 2 ≤ i.val)]
        push_cast
        ring
      have hb := stage135_forward_small_affine_of_pairwise hprime hodd Q.carrier a b
        (Q.start + (i.val : ZMod N) * Q.step) (-Q.step) hpair (hmem i.val hi) hb1 hb2
      simpa only [mul_neg, centeredAbs_neg] using hb
    · have hInt : Q.start + (i.val : ZMod N) * Q.step ∈ Q.interior.carrier := by
        apply Finset.mem_image.mpr
        refine ⟨⟨i.val - 1, by dsimp [ModAP.interior]; omega⟩, Finset.mem_univ _, ?_⟩
        dsimp [ModAP.interior]
        rw [Nat.cast_sub (by omega : 1 ≤ i.val)]
        push_cast
        ring
      obtain ⟨_, hp, hm⟩ := Q.interior_neighbors hInt
      have hid := stage135Quadratic_symmetric_difference hprime hodd
        (modInterval N 0 N) a b (Q.start + (i.val : ZMod N) * Q.step) Q.step
      simp only [stage135Quadratic, stage135ModPoint, modInterval, mul_one, zero_add] at hid
      change stage135AmbientQuadratic a b _ - stage135AmbientQuadratic a b _ = _ at hid
      rw [← hid]
      exact (hpair _ hp _ hm).trans (by linarith)

 theorem stage135_forward_small_affine {N : Nat} [NeZero N]
    (hprime : N.Prime) (hodd : N != 2) (A : Finset (ZMod N)) (a b h d : ZMod N)
    {s : Real} (hdiam : diameterAtMostReal (A.image (stage135AmbientQuadratic a b)) s)
    (hh : h ∈ A) (h1 : h + d ∈ A) (h2 : h + 2 * d ∈ A) :
    (centeredAbs ((a * h + b) * d) : Real) ≤ 4 * s := by
  classical
  exact stage135_forward_small_affine_of_pairwise hprime hodd A a b h d
    (fun x hx y hy => hdiam.centeredAbs_sub_le (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      (Finset.mem_image.mpr ⟨y, hy, rfl⟩)) hh h1 h2

theorem stage135_full_cell_small_affine {N : Nat} [NeZero N]
    (hprime : N.Prime) (hodd : N != 2) (Q : ModAP N) (hQ : 3 ≤ Q.length)
    (a b : ZMod N) {s : Real} (hs : 0 ≤ s)
    (hdiam : diameterAtMostReal (Q.carrier.image (stage135AmbientQuadratic a b)) s)
    {h : ZMod N} (hh : h ∈ Q.carrier) :
    (centeredAbs ((a * h + b) * Q.step) : Real) ≤ 4 * s := by
  classical
  exact stage135_full_cell_small_affine_of_pairwise hprime hodd Q hQ a b hs
    (fun x hx y hy => hdiam.centeredAbs_sub_le (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      (Finset.mem_image.mpr ⟨y, hy, rfl⟩)) hh

end LeanProofs.GowersSzemeredi
