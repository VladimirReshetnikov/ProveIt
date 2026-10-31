import DiophantineConsistency.ArithmeticPellHalfIndex

/-! A positive signed rank constrains the digit F under an explicit port bound. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85PortBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A positive rank and an offset bound constrain the weighted digit and gap. -/
theorem weighted_bound_of_positive_rank (q F C D : V) (hq : 1≤q)
    (hD : D≤2*(q*q-1))
    (hrank : q*q+(q*F+C)*(q*q)<(q*q)*(q*q)+(q*F+C)+D) :
    q*F+C<q*q+2 := by
  by_contra hn
  let Q : V := q*q
  let H : V := Q-1
  let N : V := q*F+C
  have hN : Q+2≤N := le_of_not_gt hn
  have hq2 : (1:V)≤q*q := one_le_mul hq hq
  have hQ : Q=1+H := by dsimp [H]; rw [add_comm,tsub_add_cancel_of_le hq2]
  have hNH : (Q+2)*H≤N*H := mul_le_mul_of_nonneg_right hN (by simp)
  have hQQ : Q*Q=Q+Q*H := by
    calc
      Q*Q=Q*(1+H) := congrArg (fun x : V => Q*x) hQ
      _=Q+Q*H := by ring
  have hNQ : N*Q=N+N*H := by
    calc
      N*Q=N*(1+H) := congrArg (fun x : V => N*x) hQ
      _=N+N*H := by ring
  have hrev : Q*Q+N+D≤Q+N*Q := calc
    _≤Q*Q+N+2*H := by simpa only [Q,H,add_comm] using add_le_add_left hD (Q*Q+N)
    _=Q+(Q+2)*H+N := by rw [hQQ]; ring
    _≤Q+N*H+N := by simpa only [add_assoc,add_comm,add_left_comm] using add_le_add_right (add_le_add_left hNH Q) N
    _=Q+N*Q := by rw [hNQ]; ring
  exact (not_le_of_gt hrank) hrev

/-- Given an explicit port-offset bound, positive rank forces F≤q. -/
theorem F_le_q_of_positive_rank (q F C D : V) (hq : 2≤q) (hC : 0<C)
    (hD : D≤2*(q*q-1))
    (hrank : q*q+(q*F+C)*(q*q)<(q*q)*(q*q)+(q*F+C)+D) : F≤q := by
  by_contra hn
  have hF : q+1≤F := lt_iff_succ_le.mp (lt_of_not_ge hn)
  have hq1 : (1:V)≤q := le_trans (by simp : (1:V)≤2) hq
  have hc1 : (1:V)≤C := pos_iff_one_le.mp hC
  have hmul : q*(q+1)≤q*F := mul_le_mul_of_nonneg_left hF (by simp)
  have hN : q*q+2≤q*F+C := by
    have h : q*q+2≤q*(q+1)+1 := by
      calc
        q*q+2=q*q+1+1 := by ring
        _≤q*q+q+1 := by simpa only [add_assoc,add_comm,add_left_comm] using add_le_add_right (add_le_add_left hq1 (q*q)) 1
        _=q*(q+1)+1 := by ring
    exact le_trans h (add_le_add hmul hc1)
  exact (not_le_of_gt (weighted_bound_of_positive_rank q F C D hq1 hD hrank)) hN

/-- The actual-style low/high port bounds give the required offset estimate. -/
theorem port_offset_bound (beta J MC MF : V)
    (hMC : MC≤beta) (hMF : MF≤2*beta) :
    let q := 1+J*beta
    J*(MC+MF*q)≤2*(q*q-1) := by
  let b : V := J*beta
  let q : V := 1+b
  have hports : MC+MF*q≤beta+(2*beta)*q :=
    add_le_add hMC (mul_le_mul_of_nonneg_right hMF (by simp))
  have hD : J*(MC+MF*q)≤J*(beta+(2*beta)*q) :=
    mul_le_mul_of_nonneg_left hports (by simp)
  have hsq : q*q=b*(q+1)+1 := by dsimp [q]; ring
  have hH : q*q-1=b*(q+1) := by rw [hsq,add_comm]; simp
  have he : J*(beta+(2*beta)*q)+b=2*(q*q-1) := by
    rw [hH]
    dsimp [b]
    ring
  calc
    J*(MC+MF*q)≤J*(beta+(2*beta)*q) := hD
    _≤J*(beta+(2*beta)*q)+b := by simp
    _=2*(q*q-1) := he

/-- Under the actual-style port bounds, positive signed rank gives a weighted bound. -/
theorem weighted_bound_of_bounded_ports (beta J MC MF F C : V)
    (hMC : MC≤beta) (hMF : MF≤2*beta)
    (hrank : let q := 1+J*beta
      q*q+(q*F+C)*(q*q)<(q*q)*(q*q)+(q*F+C)+J*(MC+MF*q)) :
    let q := 1+J*beta
    q*F+C<q*q+2 :=
  weighted_bound_of_positive_rank _ F C _ (by simp) (port_offset_bound beta J MC MF hMC hMF) hrank

/-- Under those port bounds, positive signed rank forces the actual digit F≤q. -/
theorem F_le_q_of_bounded_ports (beta J MC MF F C : V)
    (hq : 2≤1+J*beta) (hC : 0<C) (hMC : MC≤beta) (hMF : MF≤2*beta)
    (hrank : let q := 1+J*beta
      q*q+(q*F+C)*(q*q)<(q*q)*(q*q)+(q*F+C)+J*(MC+MF*q)) :
    F≤1+J*beta :=
  F_le_q_of_positive_rank _ F C _ hq hC (port_offset_bound beta J MC MF hMC hMF) hrank

end DiophantineConsistency.AdaptiveGap85PortBound
