import DiophantineConsistency.ArithmeticPellFirstIndex
import DiophantineConsistency.ArithmeticPellPowerRecovery

/-! # The quotient-carrier residue sign (package 170, §4–§5)

Package 170's residue carriers delete Carrier65's carrier coordinate `n` and
recover the parent index quotient from a residue. This module is the internal
core of `FIXED_CARRIER_PROOF.md` §4–§5 and §6.1, in every model of `𝗜𝚺₁`,
stated for a first Pell root `τ` that is *not* tied to the carrier:

* `τ² = 1 + (E Y)(E Y + 1) k²`, the main, strong and auxiliary norms of
  Carrier65 (strong multiplier `i`, `I = Δ i c²`), `X ≥ 16`, `Y ≥ 4`,
  `24 ≤ R`;
* a modulus `M ∣ E = X Y` with `R + 2 < M`;
* the residue disjunction `k ≡ R + 1` or `k + 1 ≡ R (mod M)`, i.e.
  `k - R ≡ ±1`.

`carrier_of_residue` concludes `E N + k = τ + R` for a positive `N`, i.e.
the Carrier65 carrier `τ = E N + k - R`. The first index `ν` of the
classification `τ = x_ν`, `k = 2 y_ν` (base `P0 = 2 E Y + 1`) satisfies
`2ν ≡ R + ε (mod M)`, hence `2ν + 1 ≥ R`, so the main index exceeds five and
the signed half-index recovery `ArithmeticPellHalfIndex.literal_half_index`
gives the main index `R`. Then `2ν = R + ε` exactly. The case `ε = -1`
(`R = 2ν + 1`) contradicts the growth comparison
`ArithmeticPellPowerRecovery.paired_comparison_strict` with `c < k (Y + 1)`;
in the case `ε = +1`, `k = R + 1 + 4 E Y h` and `τ = 1 + 2 E Y r`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Q170Residue
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPellRecurrence ArithmeticPellClassification
  ArithmeticPellCongruences ArithmeticPellHalfIndex
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `ArithmeticPellFirstIndex.large_of_six` (private there). -/
theorem large_of_six (a p : V) (hp : 6≤p) :
    (a+2)*delta a*delta a<ycoord p a := by
  have hx : (a+2)*delta a*delta a≤32*(a+2)*delta a*delta a+32*(a+2)*delta a := by
    calc
      (a+2)*delta a*delta a≤32*((a+2)*delta a*delta a) :=
        le_mul_of_one_le_left (by simp) (by simp)
      _=32*(a+2)*delta a*delta a := by ring
      _≤32*(a+2)*delta a*delta a+32*(a+2)*delta a := by simp
  have hpos : 0<6*(a+2) := mul_pos (by simp) (by simp)
  have h := lt_of_le_of_lt hx (lt_add_of_pos_right _ hpos)
  rw [←ArithmeticPellFirstIndex.y_six] at h
  exact lt_of_lt_of_le h ((y_strictMono a).monotone hp)

/-- A residue below the modulus of an element below twice the modulus plus it. -/
theorem eq_of_mod_small (x r M : V) (hM : 0<M) (hmod : x%M=r) (hx : x<M+r) : x=r := by
  have hd := div_add_mod x M
  rw [hmod] at hd
  have hz : x/M=0 := by
    by_contra hz
    have h1 : 1≤x/M := pos_iff_one_le.mp (pos_iff_ne_zero.mpr hz)
    have : M+r≤x := calc
      M+r≤M*(x/M)+r := add_le_add (le_mul_of_one_le_right (by simp) h1) le_rfl
      _=x := hd
    exact (not_le_of_gt hx) this
  rw [hz,mul_zero,zero_add] at hd
  exact hd.symm

/-- **Residue recovery of the Carrier65 carrier.** -/
theorem carrier_of_residue (X Y k eta d f i R y T tau M : V)
    (hX : 16≤X) (hY : 4≤Y) (heta : 0<eta) (hketa : eta<k)
    (hf : 0<f) (hi : 0<i) (hy : 0<y) (hR : 24≤R) (hRM : R+2<M) (hME : M∣X*Y)
    (hfirst : tau*tau=1+((X*Y)*Y)*((X*Y)*Y+1)*k*k)
    (hmain : d*d=1+delta (X*Y+Y)*(k*Y+eta)*(k*Y+eta))
    (hstrict : f*f=1+delta (X*Y+Y)*(i*(k*Y+eta)*(k*Y+eta))*(i*(k*Y+eta)*(k*Y+eta)))
    (haux : let c:=k*Y+eta
      let I:=delta (X*Y+Y)*i*c*c
      let u:=absdiff (f*f*c*T) (f*f*R+c)
      I*I*u*u+y*y=1+I*I*y*y)
    (hres : k%M=R+1 ∨ (k+1)%M=R) :
    ∃ N : V, 0<N ∧ (X*Y)*N+k=tau+R := by
  let E := X*Y
  let Q := E*Y
  let B := 2*(Q-1)+1
  let a := E+Y
  let c := k*Y+eta
  have hX1 : 1≤X := le_trans (by norm_num) hX
  have hY1 : 1≤Y := le_trans (by norm_num) hY
  have hY2 : 2≤Y := le_trans (by norm_num) hY
  have hE1 : 1≤E := one_le_mul hX1 hY1
  have hE : 0<E := lt_of_lt_of_le (by simp) hE1
  have hYpos : 0<Y := lt_of_lt_of_le (by simp) hY1
  have hQ : 0<Q := mul_pos hE hYpos
  have hQ1 : Q-1+1=Q := tsub_add_cancel_of_le (pos_iff_one_le.mp hQ)
  have hM : 0<M := lt_of_le_of_lt (Arithmetic.zero_le _) hRM
  have hk : 0<k := lt_of_le_of_lt (Arithmetic.zero_le _) hketa
  have hn0 : tau*tau=1+ArithmeticPellFirstNorm.discriminant (Q-1)*k*k := by
    have hd : ArithmeticPellFirstNorm.discriminant (Q-1)=Q*(Q+1) := by
      unfold ArithmeticPellFirstNorm.discriminant
      rw [show Q-1+2=(Q-1+1)+1 by ring,hQ1]
    rw [hd]
    exact hfirst
  obtain ⟨n,r,h,_,hnx,hnk,htr,hkr⟩ := ArithmeticPellFirstNorm.solution_residues (Q-1) tau k hn0
  rw [hQ1] at htr hkr
  change xcoord n B=tau at hnx
  change 2*ycoord n B=k at hnk
  -- `M ∣ 4 Q`, so `k ≡ 2 n (mod M)`
  obtain ⟨m4,hm4⟩ : M∣4*Q := by
    obtain ⟨g,hg⟩ := hME
    exact ⟨4*g*Y,by dsimp only [Q,E]; rw [hg]; ring⟩
  have hk' : k=2*n+M*(m4*h) := by rw [hkr,hm4]; ring
  have hkmod : k%M=(2*n)%M := by rw [hk',mod_add_mul' _ _ hM]
  have hk1mod : (k+1)%M=(2*n+1)%M := by
    rw [hk',show 2*n+M*(m4*h)+1=2*n+1+M*(m4*h) by ring,mod_add_mul' _ _ hM]
  -- both signs give `R ≤ 2 n + 1`
  have hRn : R≤2*n+1 := by
    rcases hres with hp | hm
    · rw [hkmod] at hp
      have h1 := mod_le (2*n) M
      rw [hp] at h1
      exact le_trans (le_of_lt (lt_add_one R)) (le_trans h1 (le_of_lt (lt_add_one _)))
    · rw [hk1mod] at hm
      rw [←hm]
      exact mod_le _ _
  have hn12 : (12:V)≤n := by
    by_contra hc
    have hle : n+1≤12 := lt_iff_succ_le.mp (lt_of_not_ge hc)
    have h2 : 2*n+1≤23 := by
      have := mul_le_mul_of_nonneg_left hle (by simp : (0:V)≤2)
      have h3 : 2*n+1+1≤24 := by
        calc 2*n+1+1=2*(n+1) := by ring
          _≤2*12 := this
          _=24 := by norm_num
      exact (add_le_add_iff_right (1:V)).mp (le_trans h3 (by norm_num))
    have : (24:V)≤23 := le_trans hR (le_trans hRn h2)
    exact absurd this (by norm_num)
  have hn5 : 5≤n := le_trans (by norm_num) hn12
  -- the main index exceeds the first one
  have hc : 0<c := lt_of_lt_of_le (mul_pos hk hYpos) (by simp [c])
  have hkc : k<c := calc
    k≤k*Y := le_mul_of_one_le_right (by simp) hY1
    _<k*Y+eta := lt_add_of_pos_right _ heta
  have hB : B+2=2*Q+1 := by
    dsimp [B]
    calc
      2*(Q-1)+1+2=2*(Q-1+1)+1 := by ring
      _=2*Q+1 := by rw [hQ1]
  have hab : a≤B := by
    have hEsub : E-1+1=E := tsub_add_cancel_of_le hE1
    have hYsub : Y-2+2=Y := tsub_add_cancel_of_le hY2
    have he : a+2+(E-1)*(2*(Y-2)+3)+(Y-2)=B+2 := by
      rw [hB]
      calc
        a+2+(E-1)*(2*(Y-2)+3)+(Y-2)=
          (E-1+1)+(Y-2+2)+2+(E-1)*(2*(Y-2)+3)+(Y-2) := by rw [hEsub,hYsub]
        _=2*((E-1+1)*(Y-2+2))+1 := by ring
        _=2*Q+1 := by rw [hEsub,hYsub]
    have he' : a+2≤B+2 := by rw [←he]; simp
    exact (add_le_add_iff_right (2:V)).mp he'
  obtain ⟨p,_,_hpd,hpc⟩ := solution_index a d c hmain
  have hnp : n<p := by
    by_contra hn
    have hp : p≤n := le_of_not_gt hn
    have he : c≤k := calc
      c=ycoord p a := hpc.symm
      _≤ycoord n a := (y_strictMono a).monotone hp
      _≤ycoord n B := (ArithmeticPellFirstIndex.base_mono a B hab n).2
      _≤2*ycoord n B := le_mul_of_one_le_left (by simp) (by simp)
      _=k := hnk
    exact (not_le_of_gt hkc) he
  have hp6 : 6≤p := by
    have h1:=le_trans (add_le_add hn5 (le_refl (1:V))) (lt_iff_succ_le.mp hnp)
    simpa only [show (5:V)+1=6 by ring] using h1
  have hbig : (a+2)*delta a*delta a<c := by rw [←hpc]; exact large_of_six a p hp6
  -- `2 R < c`: `c ≥ 4 k`, `R ≤ k + 1`, `k ≥ 2 n ≥ 24`
  have hkn : 2*n≤k := by
    rw [←hnk]; exact mul_le_mul_of_nonneg_left (time_le_y n B) (by simp)
  have h24 : (24:V)≤2*n := by
    simpa only [show (2:V)*12=24 by norm_num] using
      mul_le_mul_of_nonneg_left hn12 (by simp : (0:V)≤2)
  have hk2 : (2:V)<k := lt_of_lt_of_le (by norm_num : (2:V)<24) (le_trans h24 hkn)
  have h4k : 4*k≤c := calc
    4*k=k*4 := by ring
    _≤k*Y := mul_le_mul_of_nonneg_left hY (by simp)
    _≤k*Y+eta := by simp
  have hhalf : 2*R<c := calc
    2*R≤2*(k+1) := mul_le_mul_of_nonneg_left (le_trans hRn (add_le_add hkn (le_refl (1:V)))) (by simp)
    _=2*k+2 := by ring
    _<2*k+2*k := add_lt_add_of_le_of_lt le_rfl (lt_of_lt_of_le hk2 (le_mul_of_one_le_left (by simp)
        (by norm_num : (1:V)≤2)))
    _=4*k := by ring
    _≤c := h4k
  have hR0 : 0<R := lt_of_lt_of_le (by norm_num) hR
  obtain ⟨_hdr,hcr⟩ := literal_half_index a c d f i R y T hc hi hf hR0 hy hmain hstrict hbig
    hhalf haux
  have hpR : p=R := index_unique a p R (hpc.trans hcr)
  have hnR : n<R := by rwa [hpR] at hnp
  have hRM' : R<M := lt_trans (lt_add_of_pos_right R (by norm_num)) hRM
  rcases hres with hplus | hminus
  · -- `2 n ≡ R + 1`, so `2 n = R + 1` and `k = R + 1 + 4 Q h`
    rw [hkmod] at hplus
    have h2n : 2*n=R+1 := eq_of_mod_small (2*n) (R+1) M hM hplus (calc
      2*n<2*R := mul_lt_mul_of_pos_left hnR (by simp)
      _=R+R := two_mul R
      _<M+(R+1) := add_lt_add hRM' (lt_add_one R))
    have hkR : k=R+1+E*(4*Y*h) := by rw [hkr,h2n]; dsimp only [Q]; ring
    have htR : tau+R=R+1+E*(2*Y*r) := by rw [htr]; dsimp only [Q]; ring
    -- `k < τ`
    have hkt : k<tau := by
      apply lt_of_mul_self_lt_mul_self₀ (Arithmetic.zero_le _)
      rw [hfirst]
      have hQQ : 1≤((X*Y)*Y)*((X*Y)*Y+1) := one_le_mul (pos_iff_one_le.mp hQ)
        (le_add_of_nonneg_left (Arithmetic.zero_le _))
      calc
        k*k=1*(k*k) := (one_mul _).symm
        _≤(((X*Y)*Y)*((X*Y)*Y+1))*(k*k) := mul_le_mul_of_nonneg_right hQQ (Arithmetic.zero_le _)
        _=((X*Y)*Y)*((X*Y)*Y+1)*k*k := by ring
        _<1+((X*Y)*Y)*((X*Y)*Y+1)*k*k := lt_one_add _
    have hlt : E*(4*Y*h)<E*(2*Y*r) := by
      have h1 : R+1+E*(4*Y*h)<R+1+E*(2*Y*r) := by
        rw [←hkR,←htR]
        exact lt_of_lt_of_le hkt le_self_add
      exact (add_lt_add_iff_left (R+1)).mp h1
    have hlt' : 4*Y*h<2*Y*r := lt_of_mul_lt_mul_left hlt (Arithmetic.zero_le E)
    refine ⟨2*Y*r-4*Y*h,tsub_pos_of_lt hlt',?_⟩
    change E*(2*Y*r-4*Y*h)+k=tau+R
    rw [htR,hkR]
    have he : E*(2*Y*r-4*Y*h)+E*(4*Y*h)=E*(2*Y*r) := by
      rw [←mul_add,tsub_add_cancel_of_le (le_of_lt hlt')]
    calc
      E*(2*Y*r-4*Y*h)+(R+1+E*(4*Y*h))=R+1+(E*(2*Y*r-4*Y*h)+E*(4*Y*h)) := by ring
      _=R+1+E*(2*Y*r) := by rw [he]
  · -- `2 n + 1 ≡ R`, so `R = 2 n + 1`, contradicting the growth comparison
    exfalso
    rw [hk1mod] at hminus
    have h2n : 2*n+1=R := eq_of_mod_small (2*n+1) R M hM hminus (calc
      2*n+1≤2*R := by
        have h1 := mul_le_mul_of_nonneg_left (lt_iff_succ_le.mp hnR) (by simp : (0:V)≤2)
        exact le_trans (by simpa only [mul_add,mul_one] using
          (add_le_add (le_refl (2*n)) (by norm_num : (1:V)≤2))) h1
      _=R+R := two_mul R
      _<M+R := add_lt_add_of_lt_of_le hRM' le_rfl)
    have ha : a=Y*(X+1) := by dsimp only [a,E]; ring
    have hBQ : B+2=2*X*Y*Y+1 := by rw [hB]; dsimp only [Q,E]; ring
    have hsep : 16*(2*(B+2))<(2*(Y*(X+1))+3)*(2*(Y*(X+1))+3) := by
      rw [hBQ]; exact ArithmeticPellPowerRecovery.coefficient_gap X Y hX hY1
    have hn0' : 0<n := lt_of_lt_of_le (by norm_num) hn5
    have hcmp := ArithmeticPellPowerRecovery.paired_comparison_strict (Y*(X+1)) B hsep n hn0'
    have hlow := ArithmeticPellPowerRecovery.y_lower B n
    have hcR : c=ycoord (2*n+1) (Y*(X+1)) := by rw [h2n,←ha]; exact hcr
    have hck : c<k*(Y+1) := by
      show k*Y+eta<k*(Y+1)
      have h1 := add_lt_add_of_le_of_lt (le_refl (k*Y)) hketa
      simpa only [mul_add,mul_one] using h1
    have hchain : (2*B+3)*ycoord n B<(2*(Y+1))*ycoord n B := calc
      (2*B+3)*ycoord n B<ycoord (n+1) B := hlow
      _≤Exp.exp (4*n)*ycoord (n+1) B := le_mul_of_one_le_left (by simp) (one_le_exp _)
      _<ycoord (2*n+1) (Y*(X+1)) := hcmp
      _=c := hcR.symm
      _<k*(Y+1) := hck
      _=(2*(Y+1))*ycoord n B := by rw [←hnk]; ring
    have hcoef : 2*B+3<2*(Y+1) := lt_of_mul_lt_mul_right hchain (Arithmetic.zero_le _)
    have hQY : Y≤Q := le_mul_of_one_le_left (by simp) hE1
    have hYB : Y≤B := by
      apply (add_le_add_iff_right (2:V)).mp
      rw [hB]
      calc
        Y+2≤Y+Y+1 := by
          rw [add_assoc]; exact add_le_add (le_refl Y) (by
            simpa only [one_add_one_eq_two] using add_le_add hY1 (le_refl (1:V)))
        _=2*Y+1 := by ring
        _≤2*Q+1 := add_le_add (mul_le_mul_of_nonneg_left hQY (by simp)) le_rfl
    have : 2*(Y+1)≤2*B+3 := calc
      2*(Y+1)=2*Y+2 := by ring
      _≤2*B+2 := add_le_add (mul_le_mul_of_nonneg_left hYB (by simp)) le_rfl
      _≤2*B+3 := add_le_add (le_refl (2*B)) (by norm_num)
    exact (not_lt_of_ge this) hcoef

#print axioms Q170Residue.carrier_of_residue
end Q170Residue
