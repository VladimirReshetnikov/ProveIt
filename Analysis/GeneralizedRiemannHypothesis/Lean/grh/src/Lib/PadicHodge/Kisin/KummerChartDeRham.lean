import Lib.PadicHodge.Kisin.PeriodMatrixBasis

/-!
# Kummer charts: the different, the primes φ^a E of A_inf and their images in B_dR

Fix a Kummer chart `k` (`New.Lift.KummerChart`) with ring `S ⊆ A_inf` and distinguished element `E`.
The file studies the elements p_a = φ^a E and δ = zτ of A_inf and bounds the different of the chart.

## Main definitions and results

* `New.Lift.KummerChart.exists_derivative_dvd_p_pow`: a bound for the different.
* `New.Lift.phiInvToBdR`: the map `r ↦ φ^{-a} r` from `A_inf` to `B_dR`.
* `New.Lift.KummerChart.phiInvToBdR_mem_hodgeFil_one_iff`,
  `New.Lift.KummerChart.phiInvToBdR_frobE_zpow_mem_hodgeFil`: it sends `r` to an element of positive
  order exactly when `φ^a E` divides `r`, and the `m`-th power of the image of `φ^a E` has order at
  least `m`.
* `New.Lift.KummerChart.valueField`: the subfield `𝒦_a` of `B_dR` in which values are taken.
* `New.Lift.KummerChart.sum_phiInvToBdR_map_mul_mem_of_mem_valueField`: `S`-linear maps `A_inf → S`
  preserve linear relations over `𝒦_a`.
* `New.Lift.KummerChart.smul_sub_mem_hodgeFil_of_valueField`: if `φ^a E` divides `gs − s` for all
  `s` in `S`, then `g` fixes the elements of `𝒦_a` of order at least `0` modulo `t`; more generally,
  the same holds for the sums `∑ l, t l s` and `∑ l, t l x`, with the `t l` in the Galois monoid.

Notions from other files:
* `New.Period.Ainf`: the ring A_inf of p-typical Witt vectors over the tilt O^♭ of the ring O_C of
  integers of C_p.
* `New.Period.tau`, `New.Period.xi`: τ = [ε^(1/p)] − 1, with φ τ = μ = [ε] − 1, and ξ = μ/τ.
* `New.Lift.FrobGroup`: the group ℤ × Γ, acting on A_inf by (n, g) ↦ φ^n j(g).
* `New.Lift.Chart.S`, `New.Lift.Chart.bicommutant`: for a chart, the Λ-subalgebra S of A_inf that is
  the image of the chart's map Λ[[X]] → A_inf, with `k.coord₀ : A_inf → S` an S-linear retraction of
  A_inf onto S, and the subalgebra S_B of B^+, the closure of S[E/p] with p inverted.
* `New.Period.hodgeFil`: the step Fil^n = t^n B_dR^+ of the filtration of B_dR, for n in ℤ.

## Relation to the literature

Known; see `Lib.PadicHodge.Kisin.PeriodMatrixFrame` for sources.
-/

noncomputable section

namespace New.Lift.KummerChart

open Period Polynomial FrobGroup ValuationRing NeZero

variable {p : ℕ} [ThePrime p] [Γ : GroupOverGp p] [k : KummerChart Γ] (a : ℕ)

/-! ### The primes p_a = φ^a E and the element δ = zτ -/

/-- The submonoid of ℤ × Γ consisting of the elements (0,g) with g in the subgroup Γ' of the
Kummer chart. -/
def galMonoid : Submonoid (FrobGroup Γ) := MonoidHom.mrange (inr.comp k.subgroup.subtype)

/-- The element δ = zτ of A_inf, where z is the coordinate of the Kummer chart. -/
def zTau : Ainf := tau * k.z

lemma val_frobE : (k.frobE a).val = φ ^ a • k.E := by
  rw [phi_pow_smul]
  exact k.coe_phi_pow a k.E

/-- The prime p does not divide p_a = φ^a E in A_inf. -/
lemma not_p_dvd_val_frobE : ¬↑p ∣ (k.frobE a).val := by
  -- Undoing `φ ^ a` would give `p ∣ E`, and `E` divides `ξ`.
  rintro ⟨y, hy⟩
  have h_E : k.E.val = ↑p * ((φ ^ a)⁻¹ • y) := by
    simpa [val_frobE, ← eq_inv_smul_iff] using hy
  exact not_p_dvd_xi ((Dvd.intro _ h_E.symm).trans k.associated_E_xi.dvd)

/-- The image in W(C^♭) of p_a = φ^a(E), as a unit; it is invertible because p does not divide
p_a in A_inf. -/
def frobEUnit : WittCFlatˣ := (isUnit_algebraMap_wittCFlat_of_not_p_dvd
  (not_p_dvd_val_frobE a)).unit

/-- The image in W(C^♭) of δ = zτ, as a unit; it is invertible because p divides neither z nor τ
in A_inf. -/
def zTauUnit : WittCFlatˣ :=
  (isUnit_algebraMap_wittCFlat_of_not_p_dvd
    (Ainf.prime_p.not_dvd_mul not_p_dvd_tau k.not_p_dvd_z)).unit

variable {a : ℕ} {b : ℕ} (g : k.galMonoid)

@[simp high]
lemma frobE_ne_zero : (k.frobE a).val ≠ 0 := fun h ↦ not_p_dvd_val_frobE a (by simp [h])

/-- Bound for the different of a chart: write the Kummer chart as S = Λ⟦z⟧ ⊂ A_inf with
Λ = `WittFq k.f` (Witt vectors of a finite field), let E = `k.E` ∈ S be the image of X^e A + p, and
let e be the ramification index of the chart. Then there is a polynomial P over Λ with E ∣ P(z) in S
such that θ(P'(z)) divides p^d in O_C, where θ : A_inf → O_C is Fontaine's map, where
d = `differentBound` is 0 if e = 1 and v_p(e) + 1 otherwise. -/
lemma exists_derivative_dvd_p_pow :
    ∃ P : (WittFq k.f)[X],
      k.E ∣ aeval k.z P ∧ theta (aeval k.z P.derivative).val ∣ p ^ k.differentBound := by
  -- Take `P = X ^ e - R`, with `R` the remainder of `z ^ e` modulo `E`. If `θ (P'(z))` did not
  -- divide `p ^ (v_p e + 1)`, this power would divide `P'`, whose top coefficient is `e`.
  -- Weierstrass division: `rem s` is the one polynomial of degree `< e` with `E ∣ s - (rem s)(z)`.
  have h_division : ∀ s : k.S, ∃ r : (WittFq k.f)[X]_k.e, k.frobE 0 ∣ s - r.val.aeval k.z ∧
      ∀ r' : (WittFq k.f)[X]_k.e, k.frobE 0 ∣ s - r'.val.aeval k.z → r' = r :=
    k.weierstrass_division 0 (one_mul k.e)
  choose rem h_rem h_uniq using h_division
  set R : (WittFq k.f)[X] := (rem (k.z ^ k.e)).val
  have hR : k.frobE 0 ∣ k.z ^ k.e - R.aeval k.z := h_rem (k.z ^ k.e)
  have hR_deg : ∀ i, k.e ≤ i → R.coeff i = 0 := by
    simpa [degreeLT] using (rem (k.z ^ k.e)).property
  have hP_dvd : k.E ∣ aeval k.z (X ^ k.e - R) := by simpa [Chart.frobE] using hR
  refine ⟨X ^ k.e - R, hP_dvd, ?_⟩
  unfold differentBound
  split_ifs with he_one
  · -- for `e = 1` the remainder `R` is a constant, so `P' = 1`
    have hR_derivative : R.derivative = 0 := by
      ext i
      simp [coeff_derivative, hR_deg (i + 1) (by omega)]
    simp [he_one, hR_derivative]
  set m : ℕ := padicValNat p k.e + 1
  -- divisibility in `O_C` is total, so it suffices to exclude `p ^ m ∣ θ (P'(z))`
  refine (dvd_total _ _).resolve_right fun h_dvd ↦ ?_
  apply pow_succ_padicValNat_not_dvd (p := p) (NeZero.ne k.e)
  -- the quotient can be taken in `S` modulo `E`: apply `exists_frobE_dvd_sub_of_dvd` to an
  -- `S`-linear retraction of `A_inf` onto `S`
  have h_theta_zero (r : Ainf) : thetaPhiInv 0 r = theta r := by
    simpa using thetaPhiInv_phi_pow 0 r
  have h_dvd_zero : thetaPhiInv 0 ((p ^ m : k.S) : Ainf) ∣
      thetaPhiInv 0 (aeval k.z (X ^ k.e - R).derivative).val := by simpa [h_theta_zero] using h_dvd
  -- (the type of `hx` is left to the elaborator: stated, it sends the check into long unfolding)
  obtain ⟨x, hx⟩ := k.exists_frobE_dvd_sub_of_dvd 0 k.coord₀ (p ^ m) _ h_dvd_zero
  rw [k.coord₀_coe] at hx
  -- `P'` and `p ^ m • rem x` have degree `< e` and are both remainders of `p ^ m * x` modulo `E`
  have h_deg : (X ^ k.e - R).derivative ∈ (WittFq k.f)[X]_k.e := by
    simp only [degreeLT, Submodule.mem_iInf, LinearMap.mem_ker, lcoeff_apply]
    intro i hi
    simp [coeff_derivative, coeff_X_pow, hR_deg (i + 1) (by omega), show i + 1 ≠ k.e by omega]
  -- the polynomials are left to unification: written out, elaboration times out
  have h_left : (⟨_, h_deg⟩ : (WittFq k.f)[X]_k.e) = rem (p ^ m * x) :=
    h_uniq (p ^ m * x) ⟨_, h_deg⟩ (dvd_sub_comm.mp hx)
  have h_mul : k.frobE 0 ∣ p ^ m * x - (p ^ m • rem x).val.aeval k.z := by
    simpa [mul_sub] using (h_rem x).mul_left (p ^ m)
  have h_right : p ^ m • rem x = rem (p ^ m * x) := h_uniq (p ^ m * x) _ h_mul
  have h_eq : (X ^ k.e - R).derivative = p ^ m • (rem x).val :=
    congrArg Subtype.val (h_left.trans h_right.symm)
  -- the coefficient of `X ^ (e - 1)` in `P'` is `e`, so `p ^ m` divides `e` in `Λ`
  have h_coeff : ((p ^ m : ℕ) : WittFq k.f) ∣ (k.e : WittFq k.f) := by
    have h_top : (X ^ k.e - R).derivative.coeff (k.e - 1) = (k.e : WittFq k.f) := by
      simp [coeff_derivative, hR_deg, NeZero.one_le]
    exact ⟨(rem x).val.coeff (k.e - 1), by rw [← h_top, h_eq, coeff_smul, nsmul_eq_mul]⟩
  -- pass from `Λ` to `O_C` by `θ`, and on to `ℕ` by `p`-adic norms
  have h_coeff_OC : ((p ^ m : ℕ) : OC) ∣ (k.e : OC) := by
    simpa using (theta.comp (algebraMap (WittFq k.f) Ainf)).map_dvd h_coeff
  have h_norm : ‖((k.e : ℤ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(m : ℤ)) := by
    simpa [← PadicComplex.norm_extends', valRingCp.dvd_iff_norm_le, norm_p_eq_inv] using h_coeff_OC
  exact_mod_cast (Padic.norm_int_le_pow_iff_dvd _ _).mp h_norm

/-- The subgroup Γ', with the restriction of j, is a group over G_p: its image is open. -/
@[simps]
instance : OverGp k.subgroup p where
  toGp := toGp.comp k.subgroup.subtype
  isOpen_range :=
    ⟨Subgroup.isOpen_of_mem_nhds _ (nhds_one_le_map_nearOne Γ (nearOne_le fun g ↦ ⟨g, rfl⟩))⟩

lemma not_frobE_dvd_p (a : ℕ) : ¬(k.frobE a).val ∣ p := by simp [frobE_dvd_iff, NeZero.ne]

lemma frobE_dvd_phi_pow_tau (h_lt : a < b) : (k.frobE a).val ∣ φ ^ b • tau := by
  -- Write `b` as `a + c + 1`: `thetaPhiInv a` sends `φ ^ (a + c + 1) τ` to `θ (φ ^ c μ) = 0`, as
  -- `φ τ = μ`.
  obtain ⟨c, rfl⟩ : ∃ c : ℕ, b = a + c + 1 := Nat.exists_eq_add_of_lt h_lt
  simp [pow_add, mul_smul, phi_smul_ainf, phi_pow_smul c, frobE_dvd_iff]

/-- For a ≠ b, the element p_a = φ^a E does not divide p_b = φ^b E in A_inf. -/
lemma not_frobE_dvd_frobE_of_ne (h_ne : a ≠ b) : ¬(k.frobE a).val ∣ k.frobE b := by
  -- Both elements are prime, so each would divide the other. The one of smaller index divides
  -- `φ ^ n τ`, with `n` the larger index; the one of index `n` does not.
  intro h_dvd
  have prime (n : ℕ) : Prime (k.frobE n).val := by
    simp [Prime, isUnit_iff_dvd_one, frobE_dvd_iff]
  have not_dvd (n : ℕ) : ¬(k.frobE n).val ∣ φ ^ n • tau := by simp [frobE_dvd_iff]
  obtain hab | hba := h_ne.lt_or_gt
  · exact not_dvd b (((prime a).associated_of_dvd (prime b) h_dvd).dvd'.trans
      (frobE_dvd_phi_pow_tau hab))
  · exact not_dvd a (h_dvd.trans (frobE_dvd_phi_pow_tau hba))

/-- For any action of ℤ × Γ on a type X, an element g of the Galois monoid of the chart commutes
with φ^a. -/
lemma smul_phi_pow_comm {X : Type*} [MulAction (FrobGroup Γ) X] (x : X) :
    g • φ ^ a • x = φ ^ a • g • x := by
  -- the second component of `φ` is `1`, and the first factor `ℤ` is commutative
  have h_comm : Commute (g : FrobGroup Γ) (φ ^ a) :=
    (Commute.prod (.all _ _) (.one_right _)).pow_right a
  simp only [Submonoid.smul_def, smul_smul, h_comm.eq]

/-- The coordinate z is a Teichmüller lift, so φ^a z = z^(p^a). -/
lemma phi_pow_smul_z : φ ^ a • k.z.val = k.z ^ p ^ a := by simp [phi_pow_smul, k.z_eq_teichmuller]

lemma zTau_dvd_phi_pow_smul (a : ℕ) : k.zTau ∣ φ ^ a • k.zTau := by
  simp [k.z_eq_teichmuller, phi_pow_smul, mul_dvd_mul, tau, sub_one_dvd_pow_sub_one, zTau,
    NeZero.ne]

lemma not_frobE_dvd_zTau (a : ℕ) : ¬(k.frobE a : Ainf) ∣ k.zTau := by
  -- `zTau` divides `φ ^ a • zTau`, and `φ ^ a • E` does not divide the latter.
  intro h
  simpa [zTau, frobE_dvd_iff, Chart.theta_z_ne_zero] using h.trans (zTau_dvd_phi_pow_smul a)

/-! ### The action of Γ' on the chart -/

/-- Let Γ' be the subgroup of Γ of index prime to p attached to the Kummer chart S = Λ⟦z⟧, and let g
be in the Galois monoid, that is, an element (0, γ) of ℤ × Γ with γ ∈ Γ', acting through γ. Then for
every s ∈ S, the element zτ·E divides gs − s in A_inf, where zτ = `zTau` and z is the coordinate of
the chart. -/
lemma zTau_mul_E_dvd_smul_sub (s : k.S) : k.zTau * k.E ∣ g • s - s := by
  -- As `τ E` is associated to `μ` and `g` fixes the constants, it is enough that `z μ ∣ g z - z`.
  obtain ⟨_, γ, rfl⟩ := g
  obtain ⟨h_const, h_fix⟩ : FixesLambda k.f (toGp (γ : Γ)) ∧
      toGp (γ : Γ) • theta k.z = theta k.z := fixes γ
  have hz : theta k.z ≠ 0 := k.theta_z_ne_zero
  grw [zTau, mul_rotate, mul_assoc, k.associated_E_mul_tau_mu.dvd]
  apply k.dvd_smul_sub_of_fixesLambda _ h_const
  -- `z = [ϖ]` and `g z = [ϖ']` with `ϖ' = g ϖ`; `ϖ'` has the same untilt as `ϖ`, so `ϖ' = ϖ η`.
  -- `erw` sees through the coercion of `z` from `S` to `A_inf`.
  erw [← theta_smul, k.z_eq_teichmuller, smul_teichmuller] at *
  generalize MonoidHom.inr (Multiplicative ℕ) (Gp p) (toGp (γ : Γ)) • k.varpiFlat = ϖ'
    at h_fix ⊢
  change theta (WittVector.teichmuller p ϖ') = theta (WittVector.teichmuller p k.varpiFlat) at h_fix
  change WittVector.teichmuller p k.varpiFlat * mu ∣
    WittVector.teichmuller p ϖ' - WittVector.teichmuller p k.varpiFlat
  have h_untilt_dvd : k.varpiFlat.untilt ∣ ϖ'.untilt := by simpa using h_fix.symm.dvd
  obtain ⟨η, hη⟩ : k.varpiFlat ∣ ϖ' := Variety.untilt_dvd_iff.mp h_untilt_dvd
  -- `η` has untilt `1`, as `ϖ` and `ϖ η` have the same nonzero untilt; so `θ (φ ^ n ([η] - 1)) = 0`
  -- for all `n`, which makes `[η] - 1` a multiple of `μ` (`mu_dvd_of_theta_frobEnd`)
  have hη_one : η.untilt = 1 := by
    have h_untilt : k.varpiFlat.untilt * η.untilt = k.varpiFlat.untilt := by simpa [hη] using h_fix
    have h_ne : k.varpiFlat.untilt ≠ 0 := by simpa using hz
    exact (mul_eq_left₀ h_ne).mp h_untilt
  have h_theta (j : ℕ) : theta (frobEnd^[j] (WittVector.teichmuller p η - 1)) = 0 := by
    simp [hη_one]
  have h_mu : mu ∣ WittVector.teichmuller p η - 1 := mu_dvd_of_theta_frobEnd h_theta
  rw [hη, map_mul, ← mul_sub_one]
  exact mul_dvd_mul_left _ h_mu

end New.Lift.KummerChart

/-! ## The fields 𝒦_a in B_dR and linearity of coordinate maps over them -/

namespace New.Lift

open Period Algebra IntermediateField algebraAdjoinAdjoin BdRPlus Submodule FrobGroup Finset

variable {p : ℕ} [ThePrime p] [Γ : GroupOverGp p] [k : KummerChart Γ]
  (a : ℕ) {n : ℤ} {x y : BdR} {r : Ainf}

/-- The ring homomorphism `A_inf → B_dR` that sends `r` to the image of `φ^{-a} r`. -/
def phiInvToBdR : Ainf →+* BdR :=
  (algebraMap Ainf BdR).comp (MulSemiringAction.toRingHom (FrobGroup Γ) Ainf (φ ^ a)⁻¹)

/-- The subfield `𝒦_a` of `B_dR` generated over the fixed field of `Γ'` by the products
`b * φ^{-a} s` with `b` in `S_B` and `s` in `S`. It is the field generated by the images of `S_B`
and of `φ^{-a} S`, see `KummerChart.valueField_eq_adjoin_union`. -/
def KummerChart.valueField : IntermediateField (localFieldOf k.subgroup) BdR :=
  IntermediateField.adjoin (localFieldOf k.subgroup)
    (Set.range fun q : k.bicommutant × k.S ↦
      algebraMap k.bicommutant BdR q.1 * phiInvToBdR a q.2)

variable {a}

omit [KummerChart Γ] in
@[simp] lemma phiInvToBdR_eq_zero_iff : phiInvToBdR a r = 0 ↔ r = 0 := by
  simp [phiInvToBdR, inv_smul_eq_iff]

omit Γ k in
lemma smul_mem_hodgeFil (g : Gp p) (hx : x ∈ hodgeFil n) : g • x ∈ hodgeFil n := by
  -- `g` multiplies `tUnit ^ n` by a scalar (`smul_tUnit_zpow`)
  obtain ⟨y, rfl⟩ := mem_hodgeFil.mp hx
  -- `↓` rewrites `g • tUnit ^ n` by `smul_tUnit_zpow` before `simp` splits the power
  simp [↓smul_mul', ↓smul_tUnit_zpow, smul_of_tower_mem, mem_hodgeFil]

namespace KummerChart

variable (g : k.galMonoid)

/-- The Galois monoid acts on B_dR through the Galois group G_p. -/
instance : MulSemiringAction k.galMonoid BdR := .compHom _ ((toGp.comp snd).domRestrict _)

/-- The action of the Galois monoid on B_dR is compatible with its action on A_inf. -/
instance : SMulDistribClass k.galMonoid Ainf BdR := ⟨fun ⟨_, γ, rfl⟩ ↦ smul_distrib_smul (toGp γ)⟩

/-- An element g of the Galois monoid commutes with the map `r ↦ φ^{-a} r` from A_inf to
BdR. -/
@[simp] lemma smul_phiInvToBdR : g • phiInvToBdR a r = phiInvToBdR a (g • r) := by
  simp [phiInvToBdR, eq_inv_smul_iff, ← smul_phi_pow_comm]

lemma galMonoid_smul_mem_hodgeFil (hx : x ∈ hodgeFil n) : g • x ∈ hodgeFil n :=
  smul_mem_hodgeFil _ hx

/-- For r in A_inf, the image of φ^{−a}(r) in B_dR lies in tB_dR^+ if and only if φ^a(E) divides
r in A_inf. -/
lemma phiInvToBdR_mem_hodgeFil_one_iff :
    phiInvToBdR a r ∈ hodgeFil 1 ↔ (k.frobE a : Ainf) ∣ r :=
  algebraMap_mem_hodgeFil_one_iff.trans (by simp [frobE_dvd_iff, ← thetaPhiInv_phi_pow a])

/-- Let `r` in A_inf be prime to `φ^a E`. Then for every integer `m` and every `y` in B_dR, the
product of `(φ^{-a} r)^m` and `y` lies in Fil^n = t^n B_dR^+ exactly when `y` does. -/
lemma mul_mem_hodgeFil_iff_of_not_frobE_dvd (hr : ¬(k.frobE a : Ainf) ∣ r) (m : ℤ) :
    phiInvToBdR a r ^ m * y ∈ hodgeFil n ↔ y ∈ hodgeFil n := by
  -- `phiInvToBdR a r` comes from a unit of `BdRPlus`: a non-unit lies in `hodgeFil 1`, which
  -- forces `k.frobE a ∣ r`.
  have hu : IsUnit (algebraMap Ainf BdRPlus ((φ ^ a)⁻¹ • r)) :=
    isUnit_iff.mpr fun h_fil ↦
      hr (phiInvToBdR_mem_hodgeFil_one_iff.mp (algebraMap_mem_hodgeFil_one_iff.mpr h_fil))
  have h_unit : phiInvToBdR a r = algebraMap BdRPlus BdR hu.unit := rfl
  have h_smul : phiInvToBdR a r ^ m * y = hu.unit ^ m • y := by
    cases m <;> simp [h_unit, Units.smul_def, smul_def']
  rw [h_smul, smul_mem_iff']

/-- For every integer m, let u be the image in B_dR of φ^{−a}(φ^a E), that is, of E. Then u^m lies
in Fil^m = t^m B_dR^+. -/
lemma phiInvToBdR_frobE_zpow_mem_hodgeFil (a : ℕ) (m : ℤ) :
    phiInvToBdR a (k.frobE a) ^ m ∈ hodgeFil m := by
  -- `phiInvToBdR a (k.frobE a)` is the image of `E`, and `E w = t` for a unit `w` of `BdRPlus`.
  obtain ⟨w, hw⟩ : Associated (algebraMap Ainf BdRPlus k.E) tPeriod :=
    (k.associated_E_xi.map _).trans associated_xi_tPeriod
  refine mem_hodgeFil.mpr ⟨↑(w ^ m)⁻¹, ?_⟩
  cases m <;>
    simp [phiInvToBdR, val_frobE, tUnit, ← hw, mul_pow, field, ← IsScalarTower.algebraMap_apply]

lemma phiInvToBdR_mem_valueField (s : k.S) : phiInvToBdR a s ∈ valueField a :=
  subset_adjoin _ _ ⟨(1, s), by simp⟩

lemma algebraMap_bicommutant_mem_valueField (b : k.bicommutant) :
    algebraMap k.bicommutant BdR b ∈ valueField a :=
  subset_adjoin _ _ ⟨(b, 1), by simp⟩

/-- The field `𝒦_a` is generated by the images of `S_B` and of `φ^{-a} S`. -/
lemma valueField_eq_adjoin_union :
    valueField a = IntermediateField.adjoin (localFieldOf k.subgroup)
      (Set.range (algebraMap k.bicommutant BdR) ∪ Set.range fun s : k.S ↦ phiInvToBdR a s) := by
  apply le_antisymm
  · exact IntermediateField.adjoin_le_iff.mpr (Set.forall_mem_range.mpr fun (b, s) ↦
      mul_mem (subset_adjoin _ _ (.inl ⟨b, rfl⟩)) (subset_adjoin _ _ (.inr ⟨s, rfl⟩)))
  · exact IntermediateField.adjoin_le_iff.mpr (Set.union_subset
      (Set.forall_mem_range.mpr algebraMap_bicommutant_mem_valueField)
      (Set.forall_mem_range.mpr phiInvToBdR_mem_valueField))

/-- The image in B_dR of an element `s` of S is the image of `s` under S_B → B_dR: both maps
factor through B^+. -/
private lemma algebraMap_ainf_eq_algebraMap_bicommutant (s : k.S) :
    algebraMap Ainf BdR s =
      algebraMap k.bicommutant BdR ⟨Chart.ainfToBPlus s, k.ainfToBPlus_mem_bicommutant s⟩ :=
  rfl

/-- The field `𝒦_0` is contained in `𝒦_a`. -/
lemma valueField_zero_le : valueField 0 ≤ valueField a := by
  rw [valueField_eq_adjoin_union (a := 0)]
  refine IntermediateField.adjoin_le_iff.mpr (Set.union_subset
    (Set.forall_mem_range.mpr algebraMap_bicommutant_mem_valueField)
    (Set.forall_mem_range.mpr fun s ↦ ?_))
  -- At level `0` the image of `S` lies in the image of `S_B`.
  rw [show phiInvToBdR 0 (s : Ainf) = algebraMap Ainf BdR s by simp [phiInvToBdR],
    algebraMap_ainf_eq_algebraMap_bicommutant]
  exact algebraMap_bicommutant_mem_valueField _

/-- An element of `B_dR` fixed by `Γ'` lies in `Fil⁰` and in `𝒦₀`. -/
lemma mem_hodgeFil_zero_and_mem_valueField_zero_of_fixed
    (h_fixed : ∀ g : k.subgroup, x = toGp (g : Γ) • x) :
    x ∈ hodgeFil 0 ∧ x ∈ valueField 0 := by
  -- Tate–Sen: a fixed element of `BdR` is a constant `c` in the fixed field of `toGp Γ'`.
  obtain ⟨c, hc⟩ : ∃ c : localFieldOf k.subgroup,
      x - algebraMap (localFieldOf k.subgroup) BdR c ∈ (⊥ : Submodule BdRPlus BdR) :=
    BdR.exists_sub_mem_of_smul_sub_mem _ ⊥ fun g ↦ sub_eq_zero.mpr (h_fixed g).symm
  rw [sub_eq_zero.mp ((Submodule.mem_bot BdRPlus).mp hc)]
  exact ⟨algebraMap_mem_hodgeFil_zero, (valueField 0).algebraMap_mem c⟩

@[simp]
lemma coord₀_one : k.coord₀ 1 = 1 := k.coord₀_coe 1

/-- Let `f : A_inf → S` be `S`-linear, and let the `v l` lie in `𝒦_a` = `valueField a`, the subfield
of `B_dR` generated over the fixed field of Γ' by the images of `S_B` and of φ^{-a} S. If the sum of
the `φ^{-a} (r l) * v l` lies in a `B_dR^+`-submodule `W` of `B_dR`, then so does the sum of the
`φ^{-a} (f (r l)) * v l`. -/
lemma sum_phiInvToBdR_map_mul_mem_of_mem_valueField (f : Ainf →ₗ[k.S] k.S) {ι : Type*} [Fintype ι]
    (v : ι → BdR) (r : ι → Ainf) (hv : ∀ l : ι, v l ∈ valueField a) {W : Submodule BdRPlus BdR}
    (h_sum : ∑ l : ι, phiInvToBdR a (r l) * v l ∈ W) :
    ∑ l : ι, phiInvToBdR a (f (r l)) * v l ∈ W := by
  -- Let `A` be the algebra generated over the constants by the products `b * φ^{-a} s`.
  let prod : k.bicommutant × k.S →* BdR := (algebraMap k.bicommutant BdR).toMonoidHom.coprod
    ((phiInvToBdR a).domRestrict k.S).toMonoidHom
  let A : Subalgebra (localFieldOf k.subgroup) BdR :=
    Algebra.adjoin (localFieldOf k.subgroup) (Set.range prod)
  -- Clear denominators: `𝒦_a` is the fraction field of `A`.
  obtain ⟨d, w, hw⟩ : ∃ (d : BdR) (w : ι → A), ∀ l, d * w l = v l := by
    obtain ⟨d, hd⟩ : ∃ d : nonZeroDivisors A, ∀ l : ι, IsLocalization.IsInteger A
        ((d : A) • (⟨v l, hv l⟩ : IntermediateField.adjoin (localFieldOf k.subgroup)
          (Set.range prod))) :=
      IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A) _
    choose w hw using hd
    refine ⟨(((d : A) : BdR))⁻¹, w, fun l ↦ ?_⟩
    -- `using!`: the map from `A` to its field of fractions is the inclusion, seen only by unfolding
    simpa [Subtype.ext_iff, smul_def' (d : A), ← inv_mul_eq_iff_eq_mul₀] using! hw l
  -- The products form a monoid, so they span `A` over the constants.
  have h_span (l : ι) : ∃ (q : Finset (k.bicommutant × k.S)) (c : q → localFieldOf k.subgroup),
      ∑ i : q, c i • prod i = w l := by
    have h_mem : (w l : BdR) ∈ span (localFieldOf k.subgroup) (prod '' Set.univ) := by
      simpa using (adjoin_eq_span _ (Set.range prod)).le (w l).property
    obtain ⟨q, -, c, hc⟩ := (mem_span_image_iff_exists_fun _).mp h_mem
    exact ⟨q, c, hc⟩
  choose q c hc using h_span
  -- The conjugate `f' = φ^{-a} ∘ f ∘ φ^a` is again `S`-linear.
  let f' : Ainf →ₗ[k.S] Ainf :=
    { toFun x := (φ ^ a)⁻¹ • f (φ ^ a • x)
      map_add' := by simp
      map_smul' s x := by
        simpa [smul_def', inv_smul_eq_iff, Subtype.ext_iff] using
          f.map_smul ⟨φ ^ a • s, by simp [phi_pow_smul, ← k.coe_phi_pow]⟩ (φ ^ a • x) }
  -- Applying the extension of `f'` to `BPlus` to the terms `b * φ^{-a} (s * r l)` multiplies
  -- their sum, weighted by the `c`, by some `u` in `BdRPlus`. The extension is linear over
  -- `bicommutant` and sends such a term to `b * φ^{-a} s * φ^{-a} (f (r l))`.
  obtain ⟨u, h_mul⟩ : ∃ u : BdRPlus, ∑ l, w l * phiInvToBdR a (f (r l)) =
      (∑ l, w l * phiInvToBdR a (r l)) * algebraMap BdRPlus BdR u := by
    let term (l : ι) (bs : k.bicommutant × k.S) : BPlus :=
      bs.fst * Chart.ainfToBPlus ((φ ^ a)⁻¹ • bs.snd • r l)
    obtain ⟨u, hu⟩ : ∑ i : Σ l, q l, algebraMap (PadicAlgCl p) BdRPlus (c i.fst i.snd) *
          algebraMap BPlus BdRPlus (term i.fst i.snd) ∣
        ∑ i : Σ l, q l, algebraMap (PadicAlgCl p) BdRPlus (c i.fst i.snd) *
          algebraMap BPlus BdRPlus (k.extendToBPlus f' (term i.fst i.snd)) :=
      k.isChartOf.dvd_extendToBPlus _ (fun i : Σ l, q l ↦ (c i.fst i.snd).property) f'
        fun i ↦ term i.fst i.snd
    -- evaluate the extension of `f'` on each term; it is linear over `bicommutant`
    simp [term, f', k.extendToBPlus_mul, k.extendToBPlus_ainfToBPlus,
      -not_isEmpty_of_nonempty] at hu
    refine ⟨u, ?_⟩
    -- regroup the sum over the pairs `(l, i)`; the two sides then agree only up to the maps
    -- `B^+ → B_dR^+ → B_dR` and `S_B → B_dR`, which `simp` does not identify without unfolding
    with_unfolding_all
      simpa [← hc, prod, sum_mul, sum_sigma', smul_def', mul_assoc,
        -not_isEmpty_of_nonempty] using!
        congr(algebraMap BdRPlus BdR $hu)
  -- Multiply by `d`: the new sum is `u` times the old one.
  have h_scale (z : ι → BdR) : ∑ l, z l * v l = d * ∑ l, w l * z l := by
    simp only [← hw, mul_sum, mul_assoc, mul_comm (z _)]
  have h_new : ∑ l, phiInvToBdR a (f (r l)) * v l = u • ∑ l, phiInvToBdR a (r l) * v l := by
    rw [h_scale, h_scale, h_mul, Algebra.smul_def]
    ring
  rw [h_new]
  exact smul_mem W u h_sum

/-- Let `g` and `t 0, …, t (m - 1)` be elements of the Galois monoid of the chart, that is, elements
(0, γ) of ℤ × Γ with γ in the subgroup Γ', each acting through γ. Let `x` be an element of `𝒦_a`
(the subfield of `B_dR` generated over the fixed field of Γ' by `S_B` and φ^{-a} S) that lies in
Fil⁰ = B_dR^+. Suppose that for every `s` in `S`, `φ^a E` divides `g (∑ l, t l s) - ∑ l, t l s` in
A_inf; then `g (∑ l, t l x) - ∑ l, t l x` lies in Fil¹ = t B_dR^+. -/
lemma smul_sub_mem_hodgeFil_of_valueField {m : ℕ} (t : Fin m → k.galMonoid)
    (hx : x ∈ valueField a) (hx_int : x ∈ hodgeFil 0)
    (hg : ∀ s : k.S,
      (k.frobE a : Ainf) ∣ g • ∑ l : Fin m, t l • (s : Ainf) - ∑ l : Fin m, t l • (s : Ainf)) :
    g • ∑ l : Fin m, t l • x - ∑ l : Fin m, t l • x ∈ hodgeFil 1 := by
  -- By density, `p ^ e * x ≡ r` modulo `hodgeFil 1` for some `e` and some `r` in `Ainf`.
  obtain ⟨y, hy⟩ : ∃ y : BdRPlus, algebraMap BdRPlus BdR y = x := by
    simpa using mem_hodgeFil.mp hx_int
  obtain ⟨e, r, hr⟩ : ∃ e : ℕ, ∃ r : Ainf,
      algebraMap Ainf BdRPlus xi ^ 1 ∣ p ^ e * y - algebraMap Ainf BdRPlus r :=
    y.exists_Ainf_approx 1
  -- Read this as a relation with coefficients `1`, `φ ^ a • r` between `p ^ e • x` and `-1`, and
  -- apply the retraction `k.coord₀ : Ainf → S` to the coefficients: `r` is replaced by `φ^{-a} s`.
  let s : k.S := k.coord₀ (φ ^ a • r)
  have h_rel : ∑ l : Fin 2, phiInvToBdR a (![1, φ ^ a • r] l) * ![p ^ e • x, -1] l ∈
      hodgeFil 1 := by
    simpa [phiInvToBdR, ← hy, sub_eq_add_neg, IsScalarTower.algebraMap_apply Ainf BdRPlus BdR] using
      algebraMap_mem_hodgeFil_iff_xi_pow_dvd.mpr hr
  have approx : p ^ e • x - phiInvToBdR a s ∈ hodgeFil 1 := by
    simpa [← sub_eq_add_neg] using sum_phiInvToBdR_map_mul_mem_of_mem_valueField k.coord₀
      ![p ^ e • x, -1]
      ![1, φ ^ a • r] (Fin.forall_fin_two.mpr ⟨nsmul_mem hx (p ^ e), neg_mem (one_mem _)⟩) h_rel
  -- By `hg` the claim holds for `φ^{-a} s`, hence for `p ^ e • x`; `p` is prime to `k.frobE a`.
  refine (mul_mem_hodgeFil_iff_of_not_frobE_dvd (not_frobE_dvd_p a) e).mp ?_
  have h_fix_s :
      phiInvToBdR a (g • ∑ l, t l • (s : Ainf) - ∑ l, t l • (s : Ainf)) ∈ hodgeFil 1 :=
    phiInvToBdR_mem_hodgeFil_one_iff.mpr (hg s)
  have approx_sum : ∑ l, t l • (p ^ e • x - phiInvToBdR a s) ∈ hodgeFil 1 :=
    sum_mem fun l _ ↦ galMonoid_smul_mem_hodgeFil (t l) approx
  have h_fix_approx : g • ∑ l, t l • (p ^ e • x - phiInvToBdR a s) ∈ hodgeFil 1 :=
    galMonoid_smul_mem_hodgeFil g approx_sum
  -- `p ^ e` times the claim is the sum of `h_fix_approx` and `h_fix_s` minus `approx_sum`
  simpa [mul_sub, mul_sum, smul_sum, smul_sub, ← sub_eq_add_neg] using
    sub_mem (add_mem h_fix_approx h_fix_s) approx_sum

end KummerChart

end New.Lift

end
