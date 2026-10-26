import DiophantineConsistency.Carrier66Source
import DiophantineConsistency.ThirteenFreshSeed

/-!
# Fresh-seed completeness from an actual positive Carrier65 zero

The finite mask interface is supplemented by MC ≡ 2 modulo 4. Evenness alone
does not fix the rank modulo 4. The resulting map preserves all nine outer
coordinates and replaces the four private coordinates by proved fresh Pell
witnesses. No compatibility with the parent's private seed is assumed.
-/

namespace DiophantineConsistency.ThirteenCarrierComplete

open Diophantine Pell NativePellBootstrap NativeSourceMask NativeBinaryScale

/-- The low mask's additional residue forces the precise rank sign class. -/
theorem source_rank_mod_four (p : Fin 4 → ℤ) {d MC MF : ℕ}
    (hi : Interface p d MC MF) (hMC4 : MC % 4 = 2)
    (x : Fin 31 → ℕ) (hx : ∀ j, 0 < x j)
    (hs : ∀ j, SplitCertificate59.sourceRows p (fun k => (x k : ℤ)) j = 0) :
    (nativeRank x).toNat % 4 = 3 := by
  obtain ⟨N,hN,hq,hJ,hmask,_,_⟩ := source_mask_tests p hi x hx hs
  have hJ8 : x 0 % 8 = 1 := by
    rw [hJ]
    exact NativeMaskPopulation.repunit_mod_eight (by have := hi.width; omega) hN
  have hJ4 : x 0 % 4 = 1 := by omega
  have hq4 : sourceQ p x % 4 = 0 := by
    rw [hq, ← pow_mul]
    apply Nat.mod_eq_zero_of_dvd
    change 2 ^ 2 ∣ 2 ^ (d * N)
    apply pow_dvd_pow
    have := hi.width
    nlinarith
  have hm4 : (MC * x 0 + 1) % 4 = 3 := by
    norm_num [Nat.add_mod, Nat.mul_mod, hMC4, hJ4]
  have hlow := congrArg (fun z : ℕ => z % 2 ^ 2) hmask
  rw [Nat.and_mod_two_pow] at hlow
  change (gap p x - 1) % 4 &&& (MC * x 0 + 1) % 4 = 0 at hlow
  rw [hm4] at hlow
  have hpre : (gap p x - 1) % 4 = 0 := by
    simpa only [show (3 : ℕ) = 2 ^ 2 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod] using hlow
  rw [source_rank_four_blocks p hi x hx hs]
  norm_num [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hq4, hpre, hm4, hMC4, hJ4]

/-- The exact binary shift is larger than the entire native base. -/
theorem source_spatial_gt_base (p : Fin 4 → ℤ) {d MC MF : ℕ}
    (hi : Interface p d MC MF) (x : Fin 31 → ℕ) (hx : ∀ j, 0 < x j)
    (hs : ∀ j, SplitCertificate59.sourceRows p (fun k => (x k : ℤ)) j = 0) :
    sourceQ p x < x 10 := by
  obtain ⟨N,_,hq,_,_,_,_,_,_,hw,_⟩ := NativeSourceWindow.source_native_window p hi x hx hs
  have hqu : sourceQ p x = 2 ^ (d * N) := by rw [hq, pow_mul]
  have hR := NativePellScaleBounds.source_binary_exponent_bound p hi.portBox x hx hs hqu
  rw [hqu, hw]
  exact Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)

variable {R : Type*} [CommRing R]

def transport (p : Fin 4 → R) (v : Fin 14 → R) : R :=
  (p 1 + v 8) * (Carrier65.core p v).C - v 1

/-- These outer facts are derived before any new private seed is chosen. -/
theorem outer_facts (p : Fin 4 → ℤ) (hp : Carrier65Witness.PortBounds p)
    {d MC MF : ℕ} (hi : Interface p d MC MF) (hMC4 : MC % 4 = 2)
    (v : Fin 14 → ℤ) (hv : ∀ j, 0 < v j) (hz : Carrier65.value p v = 0) :
    0 < (Carrier65.core p v).rank ∧
      (Carrier65.core p v).rank.toNat % 4 = 3 ∧
      (Carrier65.core p v).c =
        (yn (by omega : 1 < (Carrier65.core p v).a.toNat + 2)
          (Carrier65.core p v).rank.toNat : ℤ) ∧
      0 < transport p v ∧ (p 0 * v 0) ∣ transport p v := by
  have hb : 0 < p 0 := by have := hp.beta_min; omega
  have hwin := Carrier65Witness.positive_zero_rank_window p hp v hv hz
  have hC := hwin.1
  have hR : 0 < (Carrier65.core p v).rank := by have := hwin.2.1; omega
  obtain ⟨h,_,hpos,hcanon⟩ := Carrier66.positive_zero_restores_canonical p hp v hv hz
  let u := Carrier66.restore p v h
  let x := Carrier66Source.sourceNat p u
  have hx := Carrier66Source.sourceNat_pos p u hb hpos hcanon
  have hs := Carrier66Source.sourceNat_rows p u hb hpos hcanon
  have hr := Carrier66Source.nativeRank_eq p u hb hpos hcanon
  change nativeRank x = (Carrier65.core p v).rank at hr
  have hmod := source_rank_mod_four p hi hMC4 x hx hs
  rw [hr] at hmod
  have hcmain := (source_main_index_exact p hi.portBox x hx hs).2
  rw [hr] at hcmain
  change (Carrier65.core p v).c.toNat =
    yn (by omega : 1 < (Carrier65.core p v).a.toNat + 2)
      (Carrier65.core p v).rank.toNat at hcmain
  have hccast := Carrier66Source.sourceNat_cast p u hb hpos hcanon 19
  change ((Carrier65.core p v).c.toNat : ℤ) = (Carrier65.core p v).c at hccast
  have hc : (Carrier65.core p v).c =
      (yn (by omega : 1 < (Carrier65.core p v).a.toNat + 2)
        (Carrier65.core p v).rank.toNat : ℤ) := by
    rw [← hccast, hcmain]
  have hw := source_spatial_gt_base p hi x hx hs
  rw [Carrier66Source.sourceQ_eq p u hb hpos hcanon] at hw
  change (Carrier65.core p v).q.toNat < (v 8).toNat at hw
  have hq := Carrier65.q_ge_two p v hb hv
  have hwq : (Carrier65.core p v).q < v 8 := by
    have hwz := (show ((Carrier65.core p v).q.toNat : ℤ) < ((v 8).toNat : ℤ) by exact_mod_cast hw)
    rw [Int.toNat_of_nonneg (by omega : 0 ≤ (Carrier65.core p v).q),
      Int.toNat_of_nonneg (hv 8).le] at hwz
    exact hwz
  have hFq : v 1 < (Carrier65.core p v).q := by
    change 0 < (Carrier65.core p v).q - v 1 - v 2 at hC
    have := hv 2
    omega
  have hG : 0 < transport p v := by
    have hmul := mul_nonneg (show 0 ≤ p 1 + v 8 by have := hp.K_pos; have := hv 8; omega)
      (show 0 ≤ (Carrier65.core p v).C - 1 by omega)
    dsimp [transport]
    have := hp.K_pos
    nlinarith only [hmul, hwq, hFq, this]
  have hW := ((Carrier65.value_zero_iff_norms p v hb hv).mp hz).2.2.2.2
  have hGshape : transport p v = (p 0 * v 0) * (v 3 - 1) := by
    change (p 1 + v 8) * (Carrier65.core p v).C +
      ((Carrier65.core p v).q - v 1) - v 3 * (p 0 * v 0) = 1 at hW
    have hqshape : (Carrier65.core p v).q = p 0 * v 0 + 1 := rfl
    dsimp [transport]
    rw [hqshape] at hW
    linear_combination hW
  exact ⟨hR,hmod,hc,hG,⟨v 3 - 1,hGshape⟩⟩

/-- Preserve J,F,alpha,s,w,n,eta,zeta,gamma and replace only f,i,T,m. -/
def replace (v : Fin 14 → R) (f i T m : R) (j : Fin 13) : R :=
  match j.val with
  | 0 => v 0
  | 1 => v 1
  | 2 => v 2
  | 3 => f
  | 4 => i
  | 5 => T
  | 6 => v 7
  | 7 => v 8
  | 8 => v 9
  | 9 => v 10
  | 10 => v 11
  | 11 => m
  | _ => v 13

/-- The complete literal core, including the retained first-root carrier n. -/
theorem core_replace (p : Fin 4 → R) (v : Fin 14 → R) (f i T m : R) :
    let b := Carrier65.core p v
    let V := f ^ 2 * (b.c * T - b.rank) - b.c
    let y := 1 + 4 * (p 0 * v 0 * (m - V ^ 2 * transport p v) - transport p v)
    ThirteenCarrier.core p (replace v f i T m) =
      ⟨b.a, b.delta, p 0 * v 0 * i * b.c ^ 2, f, V ^ 2 - y ^ 2, y, b.P, b.Q⟩ := rfl

theorem replace_pos (v : Fin 14 → ℤ) (hv : ∀ j, 0 < v j)
    (f i T m : ℤ) (hf : 0 < f) (hi : 0 < i) (hT : 0 < T) (hm : 0 < m) :
    ∀ j, 0 < replace v f i T m j := by
  intro j
  fin_cases j
  · exact hv 0
  · exact hv 1
  · exact hv 2
  · exact hf
  · exact hi
  · exact hT
  · exact hv 7
  · exact hv 8
  · exact hv 9
  · exact hv 10
  · exact hv 11
  · exact hm
  · exact hv 13

/-- All nine outer coordinates retain their exact values. -/
def SameOuter (v : Fin 14 → R) (u : Fin 13 → R) : Prop :=
  u 0 = v 0 ∧ u 1 = v 1 ∧ u 2 = v 2 ∧ u 6 = v 7 ∧ u 7 = v 8 ∧
    u 8 = v 9 ∧ u 9 = v 10 ∧ u 10 = v 11 ∧ u 12 = v 13

omit [CommRing R] in
theorem replace_same_outer (v : Fin 14 → R) (f i T m : R) :
    SameOuter v (replace v f i T m) := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- The two fresh norms and the two retained norms give the actual69 evaluator. -/
theorem replace_zero69 (p : Fin 4 → R) (v : Fin 14 → R) (f i T m : R)
    (hP : (Carrier65.core p v).P = 1) (hQ : (Carrier65.core p v).Q = 1)
    (hs : f ^ 2 - (Carrier65.core p v).delta *
      (p 0 * v 0 * i * (Carrier65.core p v).c ^ 2) ^ 2 = 1)
    (hu : let b := Carrier65.core p v
      let S := b.delta * (p 0 * v 0 * i * b.c ^ 2)
      let V := f ^ 2 * (b.c * T - b.rank) - b.c
      let y := 1 + 4 * (p 0 * v 0 * (m - V ^ 2 * transport p v) - transport p v)
      S ^ 2 * (V ^ 2 - y ^ 2) + y ^ 2 = 1) :
    ThirteenCarrier.value69 p (replace v f i T m) = 0 := by
  have hz : (Carrier65.core p v).delta * f ^ 2 -
      ((Carrier65.core p v).delta * (p 0 * v 0 * i * (Carrier65.core p v).c ^ 2)) ^ 2 =
      (Carrier65.core p v).delta := by
    linear_combination (Carrier65.core p v).delta * hs
  dsimp only [ThirteenCarrier.value69]
  rw [core_replace]
  dsimp only
  rw [hP, hQ, hu, hz]
  ring

/-- Every actual positive Carrier65 zero supplies positive zeros of all three
literal13 polynomials, through fresh private witnesses and unchanged outer data. -/
theorem positive_zero_completes (p : Fin 4 → ℤ) (hp : Carrier65Witness.PortBounds p)
    {d MC MF : ℕ} (hi : Interface p d MC MF) (hMC4 : MC % 4 = 2)
    (v : Fin 14 → ℤ) (hv : ∀ j, 0 < v j) (hz : Carrier65.value p v = 0) :
    ∃ u : Fin 13 → ℤ, (∀ j, 0 < u j) ∧ SameOuter v u ∧
      MvPolynomial.eval u (ThirteenCarrier.polynomial69 p) = 0 ∧
      MvPolynomial.eval u (ThirteenCarrier.polynomial70 p) = 0 ∧
      MvPolynomial.eval u (ThirteenCarrier.polynomial71 p) = 0 := by
  have hb : 0 < p 0 := by have := hp.beta_min; omega
  have hbJ : 0 < p 0 * v 0 := mul_pos hb (hv 0)
  have ha := (Carrier65.scales_pos p v hb hv).2.2.2
  obtain ⟨hR,hR4,hc,hG,hd⟩ := outer_facts p hp hi hMC4 v hv hz
  have hbcast : (((p 0 * v 0).toNat : ℕ) : ℤ) = p 0 * v 0 := Int.toNat_of_nonneg hbJ.le
  have hRcast : (((Carrier65.core p v).rank.toNat : ℕ) : ℤ) =
      (Carrier65.core p v).rank := Int.toNat_of_nonneg hR.le
  have hAcast : (((Carrier65.core p v).a.toNat + 2 : ℕ) : ℤ) =
      (Carrier65.core p v).a + 2 := by
    rw [Nat.cast_add, Int.toNat_of_nonneg ha.le]
    rfl
  have hdelta : ((((Carrier65.core p v).a.toNat + 2 : ℕ) : ℤ) ^ 2 - 1) =
      (Carrier65.core p v).delta := by
    rw [hAcast, Carrier65.delta_shape]
  have hfresh := ThirteenFreshSeed.fresh_private_seed
    ((Carrier65.core p v).a.toNat + 2) (Carrier65.core p v).rank.toNat
    (p 0 * v 0).toNat (by omega) (by omega) hR4 (transport p v) hG
    (by rwa [hbcast])
  dsimp only at hfresh
  rw [← hc, hdelta, hbcast, hRcast] at hfresh
  obtain ⟨f,i,T,m,hf,hii,hT,hm,hstrong,haux,_⟩ := hfresh
  let u := replace v f i T m
  have hup : ∀ j, 0 < u j := replace_pos v hv f i T m hf hii hT hm
  obtain ⟨hP,hQ,_,_,_⟩ := (Carrier65.value_zero_iff_norms p v hb hv).mp hz
  have h69 : ThirteenCarrier.value69 p u = 0 := replace_zero69 p v f i T m hP hQ hstrong haux
  have heq := ThirteenCarrier.positive_zero_sets p u hb hup
  have h71 : ThirteenCarrier.value71 p u = 0 := heq.1.mp h69
  have h70 : ThirteenCarrier.value70 p u = 0 := heq.2.mpr h71
  refine ⟨u,hup,replace_same_outer v f i T m,?_,?_,?_⟩
  · rwa [ThirteenCarrier.eval_polynomial69]
  · rwa [ThirteenCarrier.eval_polynomial70]
  · rwa [ThirteenCarrier.eval_polynomial71]

/-- The input can equally be stated as a zero of the literal14 polynomial. -/
theorem polynomial_zero_completes (p : Fin 4 → ℤ) (hp : Carrier65Witness.PortBounds p)
    {d MC MF : ℕ} (hi : Interface p d MC MF) (hMC4 : MC % 4 = 2)
    (v : Fin 14 → ℤ) (hv : ∀ j, 0 < v j)
    (hz : MvPolynomial.eval v (Carrier65.polynomial p) = 0) :
    ∃ u : Fin 13 → ℤ, (∀ j, 0 < u j) ∧ SameOuter v u ∧
      MvPolynomial.eval u (ThirteenCarrier.polynomial69 p) = 0 ∧
      MvPolynomial.eval u (ThirteenCarrier.polynomial70 p) = 0 ∧
      MvPolynomial.eval u (ThirteenCarrier.polynomial71 p) = 0 := by
  rw [Carrier65.eval_polynomial] at hz
  exact positive_zero_completes p hp hi hMC4 v hv hz

end DiophantineConsistency.ThirteenCarrierComplete
