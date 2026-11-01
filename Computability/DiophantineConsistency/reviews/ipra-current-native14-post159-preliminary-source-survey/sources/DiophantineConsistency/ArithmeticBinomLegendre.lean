import DiophantineConsistency.ArithmeticBinomFactorial
import DiophantineConsistency.ArithmeticBinaryPopulation

/-! Legendre's formula for the prime two, `v₂(n!) = n - σ(n)`, in the
division-free form `n! * 2^σ(n) = 2^n * (odd)`, at arbitrary internal `n`,
and its consequence: the exact 2-adic valuation of the represented central
binomial coefficient `binom (2r) r` is the binary population of `r`.
No general Kummer theorem or valuation function is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticBinomLegendre
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticBinomPascal ArithmeticBinomFactorial ArithmeticBinaryPopulation
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Parity and cancellation helpers -/

theorem two_mul_ne_odd (t z : V) : 2*t≠2*z+1 := by
  intro h
  have hm := congrArg (fun x : V => x % 2) h
  rw [mod_mul_self_right, show (2*z+1) % 2=1 from by
    simpa only [mul_comm] using mod_mul_add_of_lt z 2 (by simp : (1:V)<2)] at hm
  exact zero_ne_one hm

theorem cancel_left {c x y : V} (hc : 0<c) (h : c*x=c*y) : x=y :=
  le_antisymm (le_of_mul_le_mul_left h.le hc) (le_of_mul_le_mul_left h.ge hc)

/-- Every positive element is a power of two times an odd element. -/
theorem two_adic (b : V) (hb : 0<b) : ∃ j o, (∃ z, o=2*z+1) ∧ b=Exp.exp j*o := by
  induction b using ISigma1.sigma1_order_induction with
  | hP => definability
  | ind b ih =>
    rcases even_or_odd b with ⟨x,hx|hx⟩
    · have hx0 : 0<x :=
        pos_of_mul_pos_right (by rw [←hx]; exact hb) (by simp)
      have hxb : x<b := by
        rw [hx]
        simpa [mul_comm] using
          (mul_lt_mul_of_pos_right (show (1:V)<2 by simp) hx0)
      rcases ih x hxb hx0 with ⟨j,o,ho,hxo⟩
      exact ⟨j+1,o,ho,by rw [hx,hxo,exp_succ]; ring⟩
    · exact ⟨0,b,⟨x,hx⟩,by simp⟩

/-- An odd factor prevents an additional power of two. -/
private theorem exp_odd_ge {j p o t : V} (ho : ∃ z, o=2*z+1)
    (h : Exp.exp j*o=Exp.exp p*t) : p≤j := by
  by_contra hn
  have hjp : j<p := lt_of_not_ge hn
  obtain ⟨d,hd⟩ : ∃ d, p=j+(d+1) := ⟨p-(j+1),by
    exact (add_tsub_cancel_of_le (lt_iff_succ_le.mp hjp)).symm.trans (by ring)⟩
  rw [hd,exp_add,exp_succ] at h
  have h' : Exp.exp j*o=Exp.exp j*(2*(Exp.exp d*t)) := by rw [h]; ring
  have he := cancel_left (exp_pos j) h'
  rcases ho with ⟨z,rfl⟩
  exact two_mul_ne_odd _ _ he.symm

/-- The power of two in `2^j * odd` is unique. -/
theorem exp_odd_unique {j p o o' : V} (ho : ∃ z, o=2*z+1) (ho' : ∃ z, o'=2*z+1)
    (h : Exp.exp j*o=Exp.exp p*o') : j=p :=
  le_antisymm (exp_odd_ge ho' h.symm) (exp_odd_ge ho h)

/-! ### Legendre's formula for two -/

/-- `n! * 2^σ(n) = 2^n * H` with `H` odd, at every internal `n`. -/
theorem fact_population (n : V) :
    ∃ H, (∃ z, H=2*z+1) ∧ fact n*Exp.exp (population n)=Exp.exp n*H := by
  induction n using ISigma1.sigma1_order_induction
  · definability
  case ind n ih =>
    rcases even_or_odd n with ⟨m,hm|hm⟩
    · rcases zero_or_succ m with rfl|⟨m',hm'⟩
      · exact ⟨1,⟨0,by simp⟩,by simp [hm]⟩
      · have hmn : m<n := by
          rw [hm,hm']
          have := add_lt_add_left (show (0:V)<m'+1 by simp) (m'+1)
          simpa [two_mul] using this
        rcases ih m hmn with ⟨H,hH,hfm⟩
        refine ⟨oddProd m*H,odd_mul (oddProd_odd m) hH,?_⟩
        rw [hm,population_even,fact_double,two_mul m,exp_add]
        calc
          Exp.exp m*fact m*oddProd m*Exp.exp (population m)=
              Exp.exp m*oddProd m*(fact m*Exp.exp (population m)) := by ring
          _=Exp.exp m*oddProd m*(Exp.exp m*H) := by rw [hfm]
          _=_ := by ring
    · have hmn : m<n := by
        rw [hm]
        have : m≤2*m := le_add_of_nonneg_left (by simp) |>.trans_eq (by ring)
        exact lt_of_le_of_lt this (by simp)
      rcases ih m hmn with ⟨H,hH,hfm⟩
      refine ⟨(2*m+1)*(oddProd m*H),odd_mul ⟨m,rfl⟩ (odd_mul (oddProd_odd m) hH),?_⟩
      rw [hm,population_odd,fact_succ,fact_double,exp_succ,exp_succ,show Exp.exp (2*m)=Exp.exp m*Exp.exp m by rw [two_mul,exp_add]]
      calc
        (2*m+1)*(Exp.exp m*fact m*oddProd m)*(2*Exp.exp (population m))=
            2*(2*m+1)*Exp.exp m*oddProd m*(fact m*Exp.exp (population m)) := by ring
        _=2*(2*m+1)*Exp.exp m*oddProd m*(Exp.exp m*H) := by rw [hfm]
        _=_ := by ring

/-! ### The central binomial coefficient -/

/-- `binom (2r) r * Hr^2 = 2^σ(r) * H₂` with both `Hr` and `H₂` odd. -/
theorem central_identity (r : V) :
    ∃ Hr H₂, (∃ z, Hr=2*z+1) ∧ (∃ z, H₂=2*z+1) ∧
      binom (2*r) r*(Hr*Hr)=Exp.exp (population r)*H₂ := by
  rcases fact_population r with ⟨Hr,hHr,hr⟩
  rcases fact_population (2*r) with ⟨H₂,hH₂,h2⟩
  refine ⟨Hr,H₂,hHr,hH₂,?_⟩
  rw [population_even] at h2
  have hc := central_binom_mul_fact r
  have hexp : Exp.exp (2*r)=Exp.exp r*Exp.exp r := by rw [two_mul,exp_add]
  apply cancel_left (exp_pos (2*r))
  calc
    Exp.exp (2*r)*(binom (2*r) r*(Hr*Hr))=
        binom (2*r) r*((Exp.exp r*Hr)*(Exp.exp r*Hr)) := by rw [hexp]; ring
    _=binom (2*r) r*((fact r*Exp.exp (population r))*(fact r*Exp.exp (population r))) := by
      rw [hr]
    _=(binom (2*r) r*fact r*fact r)*Exp.exp (population r)*Exp.exp (population r) := by ring
    _=(fact (2*r)*Exp.exp (population r))*Exp.exp (population r) := by rw [hc]
    _=Exp.exp (2*r)*(Exp.exp (population r)*H₂) := by rw [h2]; ring

/-- Exact 2-adic valuation: `binom (2r) r = 2^σ(r) * odd`. -/
theorem central_valuation (r : V) :
    ∃ o, (∃ z, o=2*z+1) ∧ binom (2*r) r=Exp.exp (population r)*o := by
  have hpos : 0<binom (2*r) r := binom_pos _ _ (by
    rw [two_mul]; exact le_add_of_nonneg_left (by simp))
  rcases two_adic _ hpos with ⟨j,o,ho,hb⟩
  rcases central_identity r with ⟨Hr,H₂,hHr,hH₂,hid⟩
  have hj : j=population r := by
    apply exp_odd_unique (odd_mul ho (odd_mul hHr hHr)) hH₂
    rw [←hid,hb]; ring
  exact ⟨o,ho,by rw [hb,hj]⟩

/-- Converse (construction) direction: `2^σ(r)` divides `binom (2r) r`. -/
theorem exp_population_dvd_central (r : V) : Exp.exp (population r)∣binom (2*r) r := by
  rcases central_valuation r with ⟨o,_,h⟩
  exact ⟨o,h⟩

/-- Soundness direction: `2^m ∣ binom (2r) r → m ≤ σ(r)`. -/
theorem le_population_of_exp_dvd_central (r m : V) (h : Exp.exp m∣binom (2*r) r) :
    m≤population r := by
  rcases central_valuation r with ⟨o,ho,hv⟩
  rcases h with ⟨t,ht⟩
  apply exp_odd_ge ho
  rw [←hv,ht]

theorem population_pos (r : V) (hr : 0<r) : 0<population r := by
  induction r using ISigma1.sigma1_order_induction with
  | hP => definability
  | ind r ih =>
    rcases even_or_odd r with ⟨m,hm|hm⟩
    · have hm0 : 0<m :=
        pos_of_mul_pos_right (by rw [←hm]; exact hr) (by simp)
      have hmr : m<r := by
        rw [hm]
        simpa [mul_comm] using
          (mul_lt_mul_of_pos_right (show (1:V)<2 by simp) hm0)
      rw [hm,population_even]
      exact ih m hmr hm0
    · rw [hm,population_odd]
      simp

/-- The central binomial coefficient is even at positive `r`. -/
theorem two_dvd_central (r : V) (hr : 0<r) : 2∣binom (2*r) r := by
  rcases exp_population_dvd_central r with ⟨o,ho⟩
  rcases zero_or_succ (population r) with h0|⟨p,hp⟩
  · exact absurd h0 (ne_of_gt (population_pos r hr))
  · exact ⟨Exp.exp p*o,by rw [ho,hp,exp_succ]; ring⟩

end DiophantineConsistency.ArithmeticBinomLegendre
