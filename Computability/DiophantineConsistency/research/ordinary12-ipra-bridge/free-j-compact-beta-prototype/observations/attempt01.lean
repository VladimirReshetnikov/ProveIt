import DiophantineConsistency.FreeJRadixAlignment
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FreeJCompactBeta
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.Ordinary12FreeJ
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem exp_nat_cast (n : ℕ) : Exp.exp (n:V)=(2:V)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_add,Nat.cast_one,exp_succ,ih,pow_succ,mul_comm]
private theorem cast_pred_power (r n : ℕ) (hr : 0<r) :
    ((r^n-1:ℕ):V)+1=(r:V)^n := by
  have h : (r^n-1)+1=r^n := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
    (ne_of_gt (Nat.pow_pos hr)))
  exact_mod_cast h

theorem compact_beta_facts :
    (46:V)≤((2^590069-1:ℕ):V) ∧
    ((2^590069-1:ℕ):V)=Exp.exp (590069:V)-1 := by
  have hp : (47:ℕ)≤2^590069 := calc
    47≤2^6 := by decide
    _≤2^590069 := Nat.pow_le_pow_right (by decide) (by decide)
  have hn : (46:ℕ)≤2^590069-1 := by omega
  have hmodel : (46:V)≤((2^590069-1:ℕ):V) := by exact_mod_cast hn
  have hpow : ((2^590069-1:ℕ):V)+1=Exp.exp (590069:V) := by
    rw [exp_nat_cast]
    exact cast_pred_power 2 590069 (by decide)
  refine ⟨hmodel,?_⟩
  rw [←hpow]
  simp

theorem compact_graph_alignment (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀ j,0<v j) (hz : InternalZero (literal (fun j => (p j:ℤ))) v)
    (hport : p 0=2^590069-1) :
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    ∃ N w : V, 0<N ∧ q=Exp.exp ((590069:V)*N) ∧ (590069:V)*N≤R ∧
      w=Exp.exp (R-(590069:V)*N) ∧ v 5=q*w := by
  have h46 : (46:V)≤(p 0:V) := by rw [hport]; exact (compact_beta_facts (V:=V)).1
  have he : (p 0:V)=Exp.exp (590069:V)-1 := by rw [hport]; exact (compact_beta_facts (V:=V)).2
  have hd : (4:V)≤590069 := by norm_num
  exact FreeJRadixAlignment.graph_alignment p v (590069:V) hb hl hh hv hz h46 hd he
end FreeJCompactBeta
#print axioms FreeJCompactBeta.compact_beta_facts
#print axioms FreeJCompactBeta.compact_graph_alignment
