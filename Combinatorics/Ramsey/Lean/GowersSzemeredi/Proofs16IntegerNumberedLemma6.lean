import GowersSzemeredi.Proofs16IntegerFamilyLemma6
import GowersSzemeredi.Proofs16IntegerSourceBudget
import GowersSzemeredi.Proofs16AllDimensionsExplicit

/-! Lemma 16.6 with the literal numbered width and ordinary integer boxes.
The covering premise uses the paper's ordinary-box geometry. No primality
hypothesis is needed once that cover and the induced linearity are supplied. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Multiple linearity interpreted on boxes with integer representatives. -/
abbrev IntegerMultiplyLinear {N k : Nat} [NeZero N] (gamma r : Real)
    (Gamma : Finset (Point N k × ZMod N)) : Prop :=
  IntegerMultiplyLinearWith (fun rho => (multipleQ (rho / r) gamma k) ^ r)
    (fun rho => (multipleC (rho / r) gamma k) ^ r) Gamma

/-- The numbered width in Lemma 16.6 with ascending integer output boxes,
over every nonzero cyclic modulus, from an ordinary-box covering premise. -/
theorem lemma_16_6_integer_representatives :
  ∀ (N k m : Nat) [NeZero N], 1 ≤ k →
    ∀ (theta gamma sigma : Real),
    0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    0 < sigma → sigma ≤ 1 →
    ∀ (B : Finset (Point N (k + 1)))
      (phi : Point N (k + 1) → ZMod N)
      (H Jbase H1 : Finset (Point N k))
      (Y : (h : Point N k) → Finset (Section16CubeElement B h))
      (phiPrime : Point N k → ZMod N → ZMod N),
    let theta1 := section16ThetaOne theta gamma k
    let delta := section16Delta theta1
    let zeta := section16Zeta theta gamma k
    let t := section16T delta theta1 k
    H1 = H ∩ Jbase →
    IntegerMultiplyLinear delta t
      (restrictRelation (section16SpectrumRelation B delta) Jbase) →
    Section16InducedSelection B phi H Y
      (fun h => section16LargeSpectrum B h delta) zeta phiPrime →
    ∀ (P : Box N (k + 1)) (Q : Box N k) (I : ModAP N),
      P.HasIntegerRepresentatives → IsLastCoordinateBoxProduct P Q I → m ≤ P.width →
      ∃ q : Nat,
        (q : Real) ≤ section16Lemma6QBound sigma delta theta1 k ∧
        ∃ G : Finset (Point N k), ∃ M : Nat,
          ∃ S : Fin M → Box N (k + 1),
            ∃ T : Fin M → Box N k, ∃ A : Fin M → ModAP N,
              G ⊆ Q.carrier ∧
              (1 - sigma) * Q.carrier.card ≤ G.card ∧
              IsBoxPartition S P ∧ (∀ u, (S u).IsAscendingInteger) ∧
              (∀ u, IsLastCoordinateBoxProduct (S u) (T u) (A u)) ∧
              (∀ u, section16Lemma6Width m q k sigma delta theta1 zeta ≤
                (S u).width) ∧
              ∀ u h, h ∈ G → h ∈ H1 → h ∈ (T u).carrier →
                LinearOn ((A u).carrier.filter fun x =>
                  (h, x) ∈ section16InducedDomain B H Y) (phiPrime h) := by
  intro N k m _ hk theta gamma sigma ht ht1 hg hg1 hs hs1 B phi H Jbase H1 Y phiPrime
  dsimp only
  intro hH1 hML hselection P Q I hP hproduct hmP
  classical
  let theta1 := section16ThetaOne theta gamma k
  let delta := section16Delta theta1
  let zeta := section16Zeta theta gamma k
  let t := section16T delta theta1 k
  let C := Nat.ceil (multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
  let p := (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1))
  let q := Nat.floor (section16Lemma6QBound sigma delta theta1 k)
  let D (x : Point N k) := Finset.univ.filter (fun y => (x, y) ∈ section16InducedDomain B H Y)
  obtain ⟨hth, hth1, hd, hd1⟩ := section16_theta_delta_bounds k ht ht1 hg hg1
  obtain ⟨ha0, ha01⟩ := section16_lemma6_exponent_bounds k ht ht1 hg hg1 hs hs1
  have ha : 0 < (multipleC (sigma / t) delta k) ^ t := by
    simpa only [div_eq_mul_inv, mul_comm] using ha0
  have ha1 : (multipleC (sigma / t) delta k) ^ t ≤ 1 := by
    simpa only [div_eq_mul_inv, mul_comm] using ha01
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) (section16T_one_le k hd hd1 hth hth1)
  have hQ0 : 0 ≤ section16Lemma6QBound sigma delta theta1 k := by
    unfold section16Lemma6QBound multipleQ multipleC
    positivity
  have hC : 1 ≤ C := le_trans (by norm_num) (two_le_ceil_multiaffinePartitionK _ _)
  have hp : 0 < p := Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _)
  obtain ⟨hCq, hpq⟩ := section16Lemma6QBound_floor_profile k (explicit_family_constants_le k)
    hd hd1 hth hth1 hs hs1
  obtain ⟨hz, hzHalf⟩ := section16Zeta_pos_le_half k ht ht1 hg hg1
  have hfreq (_c : Unit) (x : Point N k) (hx : x ∈ H1) (r : ZMod N)
      (hr : r ∈ section16LargeSpectrum B x delta) :
      (x, r) ∈ restrictRelation (section16SpectrumRelation B delta) Jbase := by
    have hxJ := (Finset.mem_inter.mp (hH1 ▸ hx)).2
    simpa only [restrictRelation, section16SpectrumRelation, Finset.mem_filter,
      Finset.mem_univ, true_and] using And.intro hr hxJ
  have hlinear (_c : Unit) (x : Point N k) (hx : x ∈ H1) (v : Nat) (hv : 0 < v)
      (J : ModAP N) (hJ : J.length ≤ v)
      (hdJ : J.step ∈ bohr (section16LargeSpectrum B x delta) (zeta / v)) :
      LinearOn (J.carrier ∩ D x) (phiPrime x) := by
    have hxH := (Finset.mem_inter.mp (hH1 ▸ hx)).1
    have h := hselection.2 x hxH v hv J.step hdJ J rfl hJ
    simpa only [D, Finset.inter_filter, Finset.inter_univ] using h
  obtain ⟨G, M, S, T, J, hGsub, hGmass, hpart, hSproper, hSproduct, hwidth, hlin⟩ :=
    integerAbstractFamilyLemma166At_explicit k N m hk zeta sigma hz hzHalf hs hs1
      (fun rho => (multipleQ (rho / t) delta k) ^ t)
      (fun rho => (multipleC (rho / t) delta k) ^ t) hQ0 ha ha1
      (restrictRelation (section16SpectrumRelation B delta) Jbase) hML Unit
      (fun _ => H1) (fun _ x => section16LargeSpectrum B x delta) (fun _ => D)
      (fun _ => phiPrime) hfreq hlinear P Q I hP hproduct hmP
  refine ⟨q, Nat.floor_le hQ0, G, M, S, T, J, hGsub, hGmass, hpart, hSproper, hSproduct, ?_, ?_⟩
  · intro u
    exact family_printed_width_le_of_power_width m (S u).width hk hC hp hCq hpq ha hz
      (by linarith) (hwidth u)
  · intro u x hxG hxH hxT
    have h := hlin () u x hxG hxH hxT
    simpa only [D, Finset.inter_filter, Finset.inter_univ] using h

end LeanProofs.GowersSzemeredi
