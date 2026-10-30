import DiophantineConsistency.ArithmeticHalfBinomial

/-! Construction stage S (spec §9 S, plan K6): the outer Pell seed, in every
model of IΣ1, from an odd rank `R = 2r+1` with exact population `3u+2`.

**Interface for the 14-coordinate assembly (K7).** `outer_seed` returns
positive `s n η ζ γ` such that `SeedRelations u R s n η ζ γ` holds. With

  `q = 2^u, X = 2^R, Y = s*q^3, E = X*Y, k = η+ζ, c = k*Y+η, a = E+Y,`
  `d = X+a*c+γ*(4a+3), τ = E*n+k-R`

(the same `let` names and shapes as `ArithmeticCarrierSoundness2011.Equations`,
coordinates `v7 = s, v9 = n, v10 = η, v11 = ζ, v13 = γ`), it states

* `τ*τ = 1+(E*Y)*(E*Y+1)*k*k`         (first norm, Equations row 2),
* `d*d = 1+(a+1)*(a+3)*c*c`            (main norm, Equations row 3),
* `c = ycoord R a`, `d = xcoord R a`   (main index; feeds `auxiliary_seed`),
* `R = 2r+1`, `τ = xcoord (r+1) B`, `k = 2*ycoord (r+1) B` with
  `B = 2*(E*Y-1)+1` (first index, doubled ordinate retained).

K7 identifies `q` with `βJ+1` and `X` with `w*q`; the rank facts come from
`ArithmeticRankForcing`. Ingredients: `ArithmeticHalfBinomial.binomial_floor`
(Kummer direction + binomial floor), `construction_interval` (integer Pell
sandwich), `ArithmeticPellCongruences.residue_quotients` (index) and
`ArithmeticPellPowerRecovery.projection_quotient` (root). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticOuterSeed
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPow ArithmeticPellRecurrence ArithmeticPellCongruences ArithmeticPellPowerRecovery
  ArithmeticBinaryPopulation ArithmeticHalfBinomial ArithmeticHalfBinomialSandwich
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The outer-seed coordinate relations consumed by the assembly. -/
def SeedRelations (u R s n eta zeta gamma : V) : Prop :=
  let q:=Exp.exp u; let X:=Exp.exp R; let Y:=s*q^3; let E:=X*Y
  let k:=eta+zeta; let c:=k*Y+eta; let a:=E+Y
  let d:=X+a*c+gamma*(4*a+3); let tau:=E*n+k-R
  tau*tau=1+(E*Y)*(E*Y+1)*k*k ∧ d*d=1+(a+1)*(a+3)*c*c ∧
    c=ycoord R a ∧ d=xcoord R a ∧
    ∃ r, R=2*r+1 ∧ tau=xcoord (r+1) (2*(E*Y-1)+1) ∧ k=2*ycoord (r+1) (2*(E*Y-1)+1)

/-- `x_t(b) > (b+1)*y_t(b)` at every internal time. -/
theorem x_gt (t b : V) : (b+1)*ycoord t b<xcoord t b :=
  ArithmeticPellPowerRecovery.x_gt b t

/-- **The outer Pell seed.** -/
theorem outer_seed_with_size (u R : V) (hu : 0<u) (hodd : ∃ r, R=2*r+1) (hpop : population R=3*u+2) :
    ∃ s n eta zeta gamma : V, 0<s ∧ 0<n ∧ 0<eta ∧ 0<zeta ∧ 0<gamma ∧
      SeedRelations u R s n eta zeta gamma ∧ s*Exp.exp u^3 ≤ power (Exp.exp R + 1) R := by
  obtain ⟨r,rfl⟩ := hodd
  have hpr : population r=3*u+1 := by
    rw [population_odd] at hpop
    exact add_right_cancel (hpop.trans (by ring))
  have hu1 : 1≤u := pos_iff_one_le.mp hu
  have hr4 : 4≤r := by
    have h4 : (4:V)≤3*u+1 := by
      have : (3:V)*1≤3*u := mul_le_mul_of_nonneg_left hu1 (by simp)
      calc (4:V)=3*1+1 := by ring
        _≤3*u+1 := add_le_add this le_rfl
    rw [←hpr] at h4
    exact le_trans h4 (le_trans (population_le r).1 (population_le r).2)
  have hr1 : 1≤r := le_trans (by simp) hr4
  obtain ⟨X,hX⟩ : ∃ X, X=Exp.exp (2*r+1) := ⟨_,rfl⟩
  have hX1 : 1≤X := by rw [hX]; exact one_le_exp _
  obtain ⟨Y,s,v,w,hN,hv,hYs,hY1,_⟩ := binomial_floor X r u hr1 hX hpr.ge
  have hspos : 0<s := by
    rcases zero_or_succ s with h0|⟨s',hs'⟩
    · rw [h0,zero_mul] at hYs; rw [hYs] at hY1; simp at hY1
    · rw [hs']; simp
  have hY' : s*Exp.exp u^3=Y := by
    rw [hYs,show 3*u=u+u+u by ring,exp_add,exp_add]; ring
  -- the new size fact
  have hYbound : s*Exp.exp u^3 ≤ power (Exp.exp (2*r+1) + 1) (2*r+1) := by
    rw [hY', ← hX]
    have hp1 : 1 ≤ power X r := one_le_power X r hX1
    have h2p : 1 ≤ 2*power X r := le_trans hp1 (le_mul_of_one_le_left (by simp) (by simp))
    calc Y ≤ Y*(2*power X r) := le_mul_of_one_le_right (by simp) h2p
      _ = 2*Y*power X r := by ring
      _ ≤ 2*Y*power X r+v := le_add_of_nonneg_right (by simp)
      _ = power (X+1) (2*r) := hN.symm
      _ ≤ power (X+1) (2*r+1) :=
          power_mono_exponent _ _ _ (le_add_of_nonneg_left (by simp))
            (le_add_of_nonneg_right (by simp))
  obtain ⟨hlo,hhi⟩ := construction_interval X Y r v hr4 hX hY1 hN hv
  obtain ⟨K,hKd⟩ : ∃ K, ycoord (r+1) (2*(X*Y*Y-1)+1)=K := ⟨_,rfl⟩
  obtain ⟨c,hcd⟩ : ∃ c, ycoord (2*r+1) (Y*(X+1))=c := ⟨_,rfl⟩
  rw [hKd,hcd] at hlo hhi
  obtain ⟨eta,heta_def⟩ : ∃ eta, eta=c-2*K*Y := ⟨_,rfl⟩
  have hc : 2*K*Y+eta=c := by rw [heta_def]; exact add_tsub_cancel_of_le hlo.le
  have heta : 0<eta := by rw [heta_def]; exact tsub_pos_of_lt hlo
  have hetak : eta<2*K := by
    have h : 2*K*Y+eta<2*K*Y+2*K := by rw [hc]; simpa [mul_add] using hhi
    exact lt_of_add_lt_add_left h
  obtain ⟨zeta,hzeta_def⟩ : ∃ zeta, zeta=2*K-eta := ⟨_,rfl⟩
  have hk : eta+zeta=2*K := by rw [hzeta_def]; exact add_tsub_cancel_of_le hetak.le
  have hzeta : 0<zeta := by rw [hzeta_def]; exact tsub_pos_of_lt hetak
  have hZ1 : 1≤X*Y*Y := one_le_mul (one_le_mul hX1 hY1) hY1
  have hB : 2*(X*Y*Y-1)+1+1=2*(X*Y*Y) := by
    have he : X*Y*Y-1+1=X*Y*Y := tsub_add_cancel_of_le hZ1
    calc
      2*(X*Y*Y-1)+1+1=2*(X*Y*Y-1+1) := by ring
      _=2*(X*Y*Y) := by rw [he]
  have hdvd : X*Y∣2*(X*Y*Y-1)+1+1 := ⟨2*Y,by rw [hB]; ring⟩
  obtain ⟨ρ,σ,hxρ,hyσ⟩ := residue_quotients (r+1) (2*(X*Y*Y-1)+1) (X*Y) hdvd
  rw [hKd] at hyσ
  have hEpos : 0<X*Y := lt_of_lt_of_le (by simp) (one_le_mul hX1 hY1)
  have hxgt := x_gt (r+1) (2*(X*Y*Y-1)+1)
  rw [hB,hKd,hxρ] at hxgt
  have hρ : 2*σ+2≤ρ := by
    have hK : σ+1≤K := by
      rw [hyσ]
      calc
        σ+1≤X*Y*σ+(r+1) := add_le_add (le_mul_of_one_le_left (by simp)
          (one_le_mul hX1 hY1)) (le_add_of_nonneg_left (by simp))
        _=r+1+X*Y*σ := by ring
    have h1 : X*Y*(2*σ+2)<X*Y*ρ+1 := calc
      X*Y*(2*σ+2)=2*(X*Y)*(σ+1) := by ring
      _≤2*(X*Y)*(Y*K) := mul_le_mul_of_nonneg_left
          (le_trans hK (le_mul_of_one_le_left (by simp) hY1)) (by simp)
      _=2*(X*Y*Y)*K := by ring
      _<1+X*Y*ρ := hxgt
      _=X*Y*ρ+1 := by ring
    exact le_of_mul_le_mul_left (lt_succ_iff_le.mp h1) hEpos
  obtain ⟨n,hn_def⟩ : ∃ n, n=ρ-2*σ := ⟨_,rfl⟩
  have hnρ : n+2*σ=ρ := by
    rw [hn_def]; exact tsub_add_cancel_of_le (le_trans (le_add_of_nonneg_right (by simp)) hρ)
  have hn : 0<n := by
    rw [hn_def]
    exact tsub_pos_of_lt (lt_of_lt_of_le (by simp : 2*σ<2*σ+2) hρ)
  obtain ⟨gamma,hgamma⟩ := projection_quotient (X*Y+Y) (2*r+1)
  have hYX : Y*(X+1)=X*Y+Y := by ring
  rw [hYX] at hcd
  rw [hcd,←hX] at hgamma
  have hxc := x_gt (2*r+1) (X*Y+Y)
  rw [hcd] at hxc
  have hcX : X<c := by
    rw [←hcd]
    have hp := power_le_ycoord (X*Y+Y) (r+r)
    rw [show r+r+1=2*r+1 by ring] at hp
    have hbase : X<2*(X*Y+Y)+3 := by
      have hXa : X≤X*Y+Y := le_trans (le_mul_of_one_le_right (by simp) hY1)
        (le_add_of_nonneg_right (by simp))
      calc
        X≤X*Y+Y := hXa
        _≤(X*Y+Y)+(X*Y+Y) := le_add_of_nonneg_right (by simp)
        _=2*(X*Y+Y) := (two_mul _).symm
        _<2*(X*Y+Y)+3 := lt_add_of_pos_right _ (by simp)
    have hmono : 2*(X*Y+Y)+3≤power (2*(X*Y+Y)+3) (r+r) := by
      have h13 : (1:V)≤2*(X*Y+Y)+3 := le_trans (by simp) (le_add_of_nonneg_left (by simp))
      have := power_mono_exponent (2*(X*Y+Y)+3) 1 (r+r) h13
        (le_trans hr1 (le_add_of_nonneg_right (by simp)))
      simpa using this
    exact lt_of_lt_of_le hbase (le_trans hmono hp)
  have hgpos : 0<gamma := by
    rcases zero_or_succ gamma with h0|⟨g,hg⟩
    · exfalso
      rw [h0,mul_zero,add_zero] at hgamma
      have : (X*Y+Y+1)*c<X+(X*Y+Y)*c := by rw [hgamma] at hxc; exact hxc
      have h2 : X+(X*Y+Y)*c<(X*Y+Y+1)*c := by
        calc X+(X*Y+Y)*c<c+(X*Y+Y)*c := add_lt_add_of_lt_of_le hcX le_rfl
          _=(X*Y+Y+1)*c := by ring
      exact (lt_asymm this) h2
    · rw [hg]; simp
  refine ⟨s,n,eta,zeta,gamma,hspos,hn,heta,hzeta,hgpos,?_,hYbound⟩
  dsimp only [SeedRelations]
  rw [←hX,hY',hk,hc]
  have htau : X*Y*n+2*K-(2*r+1)=xcoord (r+1) (2*(X*Y*Y-1)+1) := by
    rw [hxρ]
    apply tsub_eq_of_eq_add
    rw [←hnρ,hyσ]; ring
  have hnorm1 := norm (r+1) (2*(X*Y*Y-1)+1)
  have hdelta : delta (2*(X*Y*Y-1)+1)=(2*(X*Y*Y))*(2*(X*Y*Y)+2) := by
    unfold delta; rw [hB,show 2*(X*Y*Y-1)+1+3=2*(X*Y*Y-1)+1+1+2 by ring,hB]
  rw [hdelta,hKd] at hnorm1
  have hnorm2 := norm (2*r+1) (X*Y+Y)
  rw [hcd] at hnorm2
  unfold delta at hnorm2
  have hd : X+(X*Y+Y)*c+gamma*(4*(X*Y+Y)+3)=xcoord (2*r+1) (X*Y+Y) := by rw [hgamma]; ring
  refine ⟨?_,?_,hcd.symm,hd,r,rfl,htau,by rw [hKd]⟩
  · rw [htau,hnorm1]; ring
  · rw [hd,hnorm2]


/-- The outer Pell seed without its size bound. -/
theorem outer_seed (u R : V) (hu : 0<u) (hodd : ∃ r, R=2*r+1) (hpop : population R=3*u+2) :
    ∃ s n eta zeta gamma : V, 0<s ∧ 0<n ∧ 0<eta ∧ 0<zeta ∧ 0<gamma ∧
      SeedRelations u R s n eta zeta gamma := by
  obtain ⟨s,n,eta,zeta,gamma,hs,hn,he,hz,hg,hseed,_⟩ :=
    outer_seed_with_size u R hu hodd hpop
  exact ⟨s,n,eta,zeta,gamma,hs,hn,he,hz,hg,hseed⟩

end DiophantineConsistency.ArithmeticOuterSeed
