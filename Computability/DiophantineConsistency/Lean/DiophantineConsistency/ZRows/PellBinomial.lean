import DiophantineConsistency.ArithmeticPellRecurrence
import DiophantineConsistency.ZRows.ModelFermat

/-! # The binomial expansion of Pell coordinates and the Frobenius congruence

In every model `V` of `𝗜𝚺₁`, write `B = b + 2` and `D = delta b = (b+1)(b+3) = B² − 1` for the
represented Pell recurrence `ArithmeticPellRecurrence.run` (so `(B + √D)ⁿ = χ(n) + ψ(n)√D` with
`χ = xcoord · b`, `ψ = ycoord · b`). This module proves

* `coords`: the binomial expansions, with internal partial sums
  `xSum b n j = Σ_{k<j} binom n (2k) · B^(n−2k) · D^k` and
  `ySum b n j = Σ_{k<j} binom n (2k+1) · B^(n−(2k+1)) · D^k`:
  `χ(n) = xSum b n (n+1)` and `ψ(n) = ySum b n (n+1)` at every internal `n`;
* `ycoord_prime`: for an odd irreducible `p = 2m+1`, `ψ(p) = Q·p + Dᵐ` (Euler's form of the
  Frobenius congruence `ψ(p) ≡ D^((p−1)/2) (mod p)`), since `p ∣ binom p k` for `0 < k < p`
  (`ModelFermat.dvd_binom`);
* `dvd_delta_of_dvd_ycoord`: hence an odd irreducible `p` with `p ∣ ψ(p)` divides `D`.

This is the only binomial input of the valuation inequality (`ZRows/PellValuationIndex`). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ZRowsPellBinomial
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPow ArithmeticBinomPascal ArithmeticPellRecurrence ModelFermat

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### The two partial sums -/

def yZeroDef : 𝚺₁.Semisentence 3 := .mkSigma “out b n. out=0”
def ySuccDef : 𝚺₁.Semisentence 5 := .mkSigma
  “out previous index b n. ∃ c, !binomDef c n (2*index+1) ∧ ∃ e, !subDef e n (2*index+1) ∧
    ∃ p, !powerDef p (b+2) e ∧ ∃ q, !powerDef q ((b+1)*(b+3)) index ∧ out=previous+c*p*q”
def yBlueprint : PR.Blueprint 2 where
  zero := yZeroDef
  succ := ySuccDef

noncomputable def yConstruction : PR.Construction V yBlueprint where
  zero _ := 0
  succ parameters index previous :=
    previous+binom (parameters 1) (2*index+1)*power (parameters 0+2) (parameters 1-(2*index+1))*
      power ((parameters 0+1)*(parameters 0+3)) index
  zero_defined := .mk fun e => by simp [yBlueprint,yZeroDef]
  succ_defined := .mk fun e => by simp [yBlueprint,ySuccDef]

/-- `ySum b n j = Σ_{k<j} binom n (2k+1) · (b+2)^(n−(2k+1)) · delta(b)^k`. -/
noncomputable def ySum (b n j : V) : V := yConstruction.result ![b,n] j
def ySumDef : 𝚺₁.Semisentence 4 := yBlueprint.resultDef |>.rew (Rew.subst ![#0,#3,#1,#2])
instance ySum_defined : 𝚺₁-Function₃[V] ySum via ySumDef := .mk fun v ↦ by
  simp [yConstruction.result_defined_iff,ySumDef,ySum]
instance ySum_definable : 𝚺₁-Function₃[V] ySum := ySum_defined.to_definable

def xZeroDef : 𝚺₁.Semisentence 3 := .mkSigma “out b n. out=0”
def xSuccDef : 𝚺₁.Semisentence 5 := .mkSigma
  “out previous index b n. ∃ c, !binomDef c n (2*index) ∧ ∃ e, !subDef e n (2*index) ∧
    ∃ p, !powerDef p (b+2) e ∧ ∃ q, !powerDef q ((b+1)*(b+3)) index ∧ out=previous+c*p*q”
def xBlueprint : PR.Blueprint 2 where
  zero := xZeroDef
  succ := xSuccDef

noncomputable def xConstruction : PR.Construction V xBlueprint where
  zero _ := 0
  succ parameters index previous :=
    previous+binom (parameters 1) (2*index)*power (parameters 0+2) (parameters 1-2*index)*
      power ((parameters 0+1)*(parameters 0+3)) index
  zero_defined := .mk fun e => by simp [xBlueprint,xZeroDef]
  succ_defined := .mk fun e => by simp [xBlueprint,xSuccDef]

/-- `xSum b n j = Σ_{k<j} binom n (2k) · (b+2)^(n−2k) · delta(b)^k`. -/
noncomputable def xSum (b n j : V) : V := xConstruction.result ![b,n] j
def xSumDef : 𝚺₁.Semisentence 4 := xBlueprint.resultDef |>.rew (Rew.subst ![#0,#3,#1,#2])
instance xSum_defined : 𝚺₁-Function₃[V] xSum via xSumDef := .mk fun v ↦ by
  simp [xConstruction.result_defined_iff,xSumDef,xSum]
instance xSum_definable : 𝚺₁-Function₃[V] xSum := xSum_defined.to_definable

@[simp] theorem ySum_zero (b n : V) : ySum b n 0=0 := by simp [ySum,yConstruction]
theorem ySum_succ (b n j : V) : ySum b n (j+1)=
    ySum b n j+binom n (2*j+1)*power (b+2) (n-(2*j+1))*power (delta b) j := by
  simp [ySum,yConstruction,delta]

@[simp] theorem xSum_zero (b n : V) : xSum b n 0=0 := by simp [xSum,xConstruction]
theorem xSum_succ (b n j : V) : xSum b n (j+1)=
    xSum b n j+binom n (2*j)*power (b+2) (n-2*j)*power (delta b) j := by
  simp [xSum,xConstruction,delta]

/-! ### Pascal's rule for the two sums -/

/-- One more factor of the base, including the vanishing range `n < k`. -/
theorem term_shift (B n k : V) :
    binom n k*power B (n+1-k)=B*(binom n k*power B (n-k)) := by
  rcases le_or_gt k n with hk|hk
  · rw [← tsub_add_eq_add_tsub hk,power_succ]
    ring
  · rw [binom_eq_zero_of_lt n k hk]
    simp

theorem tsub_succ_succ (n k : V) : n+1-(k+1)=n-k := add_tsub_add_eq_tsub_right n 1 k

theorem y_pascal (b n j : V) : ySum b (n+1) j=(b+2)*ySum b n j+xSum b n j := by
  induction j using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ j ih =>
    have hs := term_shift (b+2) n (2*j+1)
    rw [tsub_succ_succ] at hs
    rw [ySum_succ,ySum_succ,xSum_succ,ih,binom_succ_succ,tsub_succ_succ]
    have e : (binom n (2*j)+binom n (2*j+1))*power (b+2) (n-2*j)*power (delta b) j=
        binom n (2*j)*power (b+2) (n-2*j)*power (delta b) j+
          (binom n (2*j+1)*power (b+2) (n-2*j))*power (delta b) j := by ring
    rw [e,hs]
    ring

theorem x_pascal (b n j : V) :
    xSum b (n+1) (j+1)=(b+2)*xSum b n (j+1)+delta b*ySum b n j := by
  induction j using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    rw [xSum_succ,xSum_succ]
    simp [power_succ]
  case succ j ih =>
    have e2 : 2*(j+1)=2*j+1+1 := by ring
    rw [xSum_succ b (n+1) (j+1),ih,xSum_succ b n (j+1),ySum_succ,e2,binom_succ_succ,
      tsub_succ_succ]
    have hs := term_shift (b+2) n (2*j+1+1)
    rw [tsub_succ_succ] at hs
    rw [power_succ (delta b) j]
    have e : (binom n (2*j+1)+binom n (2*j+1+1))*power (b+2) (n-(2*j+1))*
          (delta b*power (delta b) j)=
        delta b*(binom n (2*j+1)*power (b+2) (n-(2*j+1))*power (delta b) j)+
          (binom n (2*j+1+1)*power (b+2) (n-(2*j+1)))*(delta b*power (delta b) j) := by ring
    rw [e,hs]
    ring

/-! ### Stability past the top degree -/

theorem y_stable (b n J m : V) (h : n≤2*J) : ySum b n (J+m)=ySum b n J := by
  induction m using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ m ih =>
    rw [← add_assoc,ySum_succ,ih,binom_eq_zero_of_lt n _ (by
      apply lt_of_le_of_lt h
      calc 2*J≤2*(J+m) := by simp
        _<2*(J+m)+1 := lt_add_one _)]
    simp

theorem x_stable (b n J m : V) (h : n<2*J) : xSum b n (J+m)=xSum b n J := by
  induction m using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ m ih =>
    rw [← add_assoc,xSum_succ,ih,binom_eq_zero_of_lt n _ (by
      apply lt_of_lt_of_le h
      simp)]
    simp

/-! ### The binomial expansion of the coordinates -/

/-- **Binomial expansion of the Pell coordinates**, at every internal index. -/
theorem coords (b n : V) : xcoord n b=xSum b n (n+1) ∧ ycoord n b=ySum b n (n+1) := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    constructor
    · rw [xSum_succ]
      simp
    · rw [ySum_succ,binom_eq_zero_of_lt 0 (2*0+1) (by simp)]
      simp
  case succ n ih =>
    have hn2 : n<2*(n+1) := lt_of_lt_of_le (lt_add_one n) (by rw [two_mul]; exact le_add_self)
    have hxs : xSum b n (n+1+1)=xSum b n (n+1) := x_stable b n (n+1) 1 hn2
    have hys : ySum b n (n+1+1)=ySum b n (n+1) := y_stable b n (n+1) 1 (le_of_lt hn2)
    constructor
    · rw [x_succ,x_pascal,ih.1,ih.2,hxs]
    · rw [y_succ,y_pascal,ih.1,ih.2,hxs,hys]
      ring

/-! ### Frobenius -/

/-- The partial `ψ`-sums of an irreducible row below the top degree vanish modulo `p`. -/
theorem y_row_low {p m : V} (hp : Irred p) (hpm : p=2*m+1) (b : V) :
    ∀ j, j≤m → ∃ Q, ySum b p j=Q*p := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact fun _ => ⟨0,by simp⟩
  case succ j ih =>
    intro hj
    have hjm : j<m := lt_of_lt_of_le (lt_add_one j) hj
    obtain ⟨Q,hQ⟩ := ih (le_of_lt hjm)
    have hk : 2*j+1<p := by
      rw [hpm]
      have : 2*j<2*m := by
        rw [two_mul,two_mul]
        exact _root_.add_lt_add hjm hjm
      simpa only [add_lt_add_iff_right] using this
    obtain ⟨C,hC⟩ := dvd_binom hp (by simp : (0:V)<2*j+1) hk
    refine ⟨Q+C*power (b+2) (p-(2*j+1))*power (delta b) j,?_⟩
    rw [ySum_succ,hQ,hC]
    ring

/-- **Frobenius (Euler form)**: `ψ(p) = Q·p + delta(b)^m` for an irreducible `p = 2m+1`. -/
theorem ycoord_prime {p m : V} (hp : Irred p) (hpm : p=2*m+1) (b : V) :
    ∃ Q, ycoord p b=Q*p+power (delta b) m := by
  obtain ⟨Q,hQ⟩ := y_row_low hp hpm b m le_rfl
  refine ⟨Q,?_⟩
  have hst : ySum b p (m+1+(m+1))=ySum b p (m+1) :=
    y_stable b p (m+1) (m+1) (by rw [hpm,mul_add,mul_one]; simp)
  rw [(coords b p).2,show p+1=m+1+(m+1) by rw [hpm]; ring,hst,ySum_succ,hQ,← hpm,binom_self,
    tsub_self,power_zero]
  ring

theorem dvd_of_dvd_power {p : V} (hp : Irred p) (x : V) :
    ∀ k, p∣power x k → p∣x := by
  intro k
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    intro h
    rw [power_zero] at h
    exact absurd h (not_dvd_of_pos_lt (by simp) hp.1)
  case succ k ih =>
    intro h
    rw [power_succ] at h
    rcases hp.euclid h with h|h
    · exact h
    · exact ih h

theorem odd_of_irred {p : V} (hp : Irred p) (hp2 : p≠2) : ∃ m, p=2*m+1 := by
  obtain ⟨m,h|h⟩ := even_or_odd p
  · exfalso
    rcases hp.2 2 ⟨m,h⟩ with h2|h2
    · exact absurd h2 (ne_of_gt _root_.one_lt_two)
    · exact hp2 h2.symm
  · exact ⟨m,h⟩

/-- An odd irreducible dividing `ψ(p)` divides the discriminant. -/
theorem dvd_delta_of_dvd_ycoord {p : V} (hp : Irred p) (hp2 : p≠2) (b : V)
    (h : p∣ycoord p b) : p∣delta b := by
  obtain ⟨m,hm⟩ := odd_of_irred hp hp2
  obtain ⟨Q,hQ⟩ := ycoord_prime hp hm b
  rw [hQ] at h
  have hd : p∣power (delta b) m := by
    obtain ⟨c,hc⟩ := h
    refine ⟨c-Q,?_⟩
    rw [mul_tsub,mul_comm p Q,← hc]
    simp
  exact dvd_of_dvd_power hp _ m hd

#print axioms coords
#print axioms ycoord_prime
#print axioms dvd_delta_of_dvd_ycoord

end DiophantineConsistency.ZRowsPellBinomial
