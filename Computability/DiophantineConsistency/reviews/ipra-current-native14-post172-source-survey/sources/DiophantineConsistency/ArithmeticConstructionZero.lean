import DiophantineConsistency.ArithmeticCarrierSoundness2011

/-! **K7a — the literal polynomial vanishes on a solution of the five equations**
(the converse of `ArithmeticCarrierSoundness2011.current_equations`), in every
model of IΣ1.

The signed-pair representation of the literal current expression is shared from
`ArithmeticCarrierSoundness2011` (`literal_rep`): the split
evaluator represents `P·Q·U·W·(δ·Z) − δ` for the five factor pairs. When each
factor pair is equivalent to `1`, the representation is `δ − δ`, so the two
split sides agree.

* `expressionAt_zero` — generic natural ports;
* `current_zero` — the actual ports: `Equations β K lowPort (highPort+β) v`,
  positivity and `F ≤ q` give the zero of the literal `expression` (with positivity
  this is `ArithmeticCurrentSentence2011.PositiveZero v`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.ArithmeticConstructionZero
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticSignedPairs ObjectCurrentEquation2011 ArithmeticCarrierSoundness2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.highPrefix
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem equivalent_scale (a : V) {p q : Pair V} (h : Equivalent p q) :
    Equivalent (scale a p) (scale a q) := by
  change p.1+q.2=p.2+q.1 at h
  change a*p.1+a*q.2=a*p.2+a*q.1
  rw [← mul_add, ← mul_add, h]

/-- **Converse direction, generic ports.** -/
theorem expressionAt_zero (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hq : 2≤(p 0:V)*v 0+1) :
    let b:=(p 0:V)*v 0; let q:=b+1; let X:=v 8*q; let Y:=v 7*q^3
    let E:=X*Y; let k:=v 10+v 11; let c:=k*Y+v 10; let a:=E+Y
    let H:=4*a+3; let delta:=(a+1)*(a+3); let d:=X+a*c+v 13*H
    let M:=((p 2:V)+q*(p 3:V))*v 0
    let rp:=(b*q+v 2)*(q^2-1)+M; let rn:=b*v 1*(q^2-1)
    let tp:=(E*v 9+k+rn,rp); let vp:=(v 4*v 4*(c*v 6+rn),v 4*v 4*rp+c)
    let S:=delta*v 5*c*c
    magnitude tp*magnitude tp=(E*Y)*(E*Y+1)*k*k+1 →
    d*d=delta*c*c+1 →
    S*S*magnitude vp*magnitude vp+v 12*v 12=S*S*v 12*v 12+1 →
    ((p 1:V)+v 8)*q+q=((p 1:V)+v 8)*(v 1+v 2)+v 1+v 3*b+1 →
    v 4*v 4=delta*(v 5*c*c)*(v 5*c*c)+1 →
    (expressionAt (fun j => (p j:ℤ))).splitNatural.1.evalSemiring v=
      (expressionAt (fun j => (p j:ℤ))).splitNatural.2.evalSemiring v := by
  intro b q X Y E k c a H delta d M rp rn tp vp S hP hQ hU hW hZ
  have hr := literal_rep p v hq
  have e1 : ∀ x y : V, x=y+1 → Equivalent ((x,y) : Pair V) (natural (1:V)) :=
    fun x y h => equivalent_one.mpr h
  have hprod := equivalent_multiply (equivalent_multiply (equivalent_multiply
    (equivalent_multiply (e1 _ _ hP) (e1 _ _ hQ)) (e1 _ _ hU)) (e1 _ _ hW))
    (equivalent_scale delta (e1 _ _ hZ))
  have hm := equivalent_minus hprod (equivalent_refl (natural delta))
  have hall := equivalent_trans hr hm
  change _ + _ = _ + _ at hall
  simp only [minus, multiply, natural, scale, mul_one, mul_zero, zero_mul, add_zero,
    zero_add] at hall
  rw [one_mul] at hall
  exact add_right_cancel hall

/-- **Generic ports: a positive solution of the five equations is a zero.** -/
theorem equations_zero (p : Fin 4 → ℕ) (v : Fin 14 → V) (hv : ∀ j, 0 < v j)
    (hb1 : (1:V) ≤ (p 0:V)) (hF : v 1 ≤ (p 0:V)*v 0+1)
    (heq : Equations (p 0:V) (p 1:V) (p 2:V) (p 3:V) v) :
    (expressionAt (fun j => (p j:ℤ))).splitNatural.1.evalSemiring v=
      (expressionAt (fun j => (p j:ℤ))).splitNatural.2.evalSemiring v := by
  have hq : (2:V) ≤ (p 0:V)*v 0+1 := by
    simpa only [one_add_one_eq_two] using
      add_le_add (one_le_mul hb1 (pos_iff_one_le.mp (hv 0))) (le_refl (1:V))
  obtain ⟨ht, hP, hQ, hZ, hU⟩ := heq
  let b:=(p 0:V)*v 0; let q:=b+1; let X:=v 8*q; let Y:=v 7*q^3
  let E:=X*Y; let k:=v 10+v 11; let c:=k*Y+v 10; let a:=E+Y
  let M:=((p 2:V)+q*(p 3:V))*v 0
  let rp:=(b*q+v 2)*(q^2-1)+M; let rn:=b*v 1*(q^2-1)
  let R:=((q-1)*(q-v 1)+v 2)*(q^2-1)+M
  have hb : q-1=b := add_tsub_cancel_right b 1
  have hFq : q-v 1+v 1=q := tsub_add_cancel_of_le hF
  have hrr : rp=rn+R := by
    show (b*q+v 2)*(q^2-1)+M=b*v 1*(q^2-1)+(((q-1)*(q-v 1)+v 2)*(q^2-1)+M)
    rw [hb]
    calc (b*q+v 2)*(q^2-1)+M=(b*(q-v 1+v 1)+v 2)*(q^2-1)+M := by rw [hFq]
      _=_ := by ring
  -- the first norm: τ = E·n + k − R ≥ 1
  have htau_pos : R < E*v 9+k := by
    change (E*v 9+k-R)*(E*v 9+k-R)=1+(E*Y)*(E*Y+1)*k*k at hP
    exact tsub_pos_iff_lt.mp (pos_of_mul_pos_left (by rw [hP]; simp) (by simp))
  have hmagP : magnitude ((E*v 9+k+rn,rp) : Pair V)=E*v 9+k-R := by
    apply magnitude_of_add
    rw [hrr]
    calc E*v 9+k+rn=(E*v 9+k-R+R)+rn := by rw [tsub_add_cancel_of_le htau_pos.le]
      _=_ := by ring
  have hmagU : magnitude ((v 4*v 4*(c*v 6+rn),v 4*v 4*rp+c) : Pair V)=
      (v 4*v 4*c*v 6-(v 4*v 4*R+c))+((v 4*v 4*R+c)-v 4*v 4*c*v 6) := by
    dsimp only [magnitude]
    rw [hrr]
    have h1 : v 4*v 4*(c*v 6+rn)=v 4*v 4*c*v 6+v 4*v 4*rn := by ring
    have h2 : v 4*v 4*(rn+R)+c=(v 4*v 4*R+c)+v 4*v 4*rn := by ring
    rw [h1,h2,add_tsub_add_eq_tsub_right,add_tsub_add_eq_tsub_right]
  refine expressionAt_zero p v hq ?_ ?_ ?_ ?_ ?_
  · rw [hmagP]; exact hP.trans (add_comm _ _)
  · exact hQ.trans (add_comm _ _)
  · rw [hmagU]; exact hU.trans (add_comm _ _)
  · change ((p 1:V)+v 8)*q+q=((p 1:V)+v 8)*(v 1+v 2)+v 1+v 3*(q-1)+1 at ht
    simpa only [hb] using ht
  · exact hZ.trans (add_comm _ _)

/-- Ports given as natural parameters (no evaluation of the actual numerals). -/
theorem vector_zero (beta K MC high : ℕ) (v : Fin 14 → V) (hv : ∀ j, 0 < v j)
    (hb1 : (1:V) ≤ (beta:V)) (hF : v 1 ≤ (beta:V)*v 0+1)
    (heq : Equations (beta:V) (K:V) (MC:V) ((high+beta:ℕ):V) v) :
    (expressionAt ![(beta:ℤ),(K:ℤ),(MC:ℤ),(high:ℤ)+(beta:ℤ)]).splitNatural.1.evalSemiring v =
      (expressionAt ![(beta:ℤ),(K:ℤ),(MC:ℤ),(high:ℤ)+(beta:ℤ)]).splitNatural.2.evalSemiring v := by
  let p : Fin 4 → ℕ := ![beta, K, MC, high + beta]
  have hpe : (fun j => (p j:ℤ)) = ![(beta:ℤ),(K:ℤ),(MC:ℤ),(high:ℤ)+(beta:ℤ)] := by
    funext j
    fin_cases j <;> simp [p, Nat.cast_add]
  simpa only [hpe] using equations_zero p v hv hb1 hF heq

/-- **The actual polynomial vanishes on a positive solution of the five equations.** -/
theorem current_zero (v : Fin 14 → V) (hv : ∀ j, 0 < v j)
    (hF : v 1 ≤ (CurrentMasks2011.beta:V)*v 0+1)
    (heq : Equations (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V)
      (CurrentMasks2011.lowPort:V) ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V) v) :
    expression.splitNatural.1.evalSemiring v = expression.splitNatural.2.evalSemiring v := by
  obtain ⟨hb15, _, _⟩ := current_bounds (V := V)
  exact vector_zero CurrentMasks2011.beta CurrentKernel2011.K CurrentMasks2011.lowPort
    CurrentMasks2011.highPort v hv (le_trans (by norm_num) hb15) hF heq

end DiophantineConsistency.ArithmeticConstructionZero
