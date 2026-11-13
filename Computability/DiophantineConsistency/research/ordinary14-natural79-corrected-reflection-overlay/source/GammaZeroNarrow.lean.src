import DiophantineConsistency.Compact44.DirectMainNorm
import DiophantineConsistency.ArithmeticPellFirstNorm

/-! Source-only narrow facts for the 80/107 gamma-zero contradiction.
No graph binding, port bound, endpoint or iPRA proof is claimed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.GammaZeroNarrowDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence DirectMainNorm ArithmeticSignedPairs
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Fact-level recurrence bound: the source of the first Pell index and the
proof that it is at least two are deliberately separate hypotheses. -/
theorem first_ordinate_lower (P n k : V) (hP : 0 < P) (hn : 2 ≤ n)
    (hcoord : 2*ycoord n (2*(P-1)+1) = k) : 8*P+4 ≤ k := by
  let B : V := 2*(P-1)+1
  have hP1 : P-1+1=P := tsub_add_cancel_of_le (pos_iff_one_le.mp hP)
  have hB : B+2=2*P+1 := by
    calc
      B+2=2*(P-1+1)+1 := by dsimp [B]; ring
      _=2*P+1 := by rw [hP1]
  have hy1 : ycoord 1 B=1 := by simpa using y_succ (0:V) B
  have hx1 : xcoord 1 B=B+2 := by simpa using x_succ (0:V) B
  have hy2 : ycoord 2 B=2*(B+2) := by
    calc
      ycoord 2 B=xcoord 1 B+(B+2)*ycoord 1 B := by
        simpa only [show (1:V)+1=2 by ring] using y_succ (1:V) B
      _=2*(B+2) := by rw [hx1,hy1]; ring
  calc
    8*P+4=2*ycoord 2 B := by rw [hy2,hB]; ring
    _≤2*ycoord n B := mul_le_mul_of_nonneg_left ((ordinate_strictMono B).monotone hn) (by simp)
    _=k := hcoord

/-- Narrow gamma-zero contradiction. The bounds `R+1<k` and `X<c` and
literal signed-magnitude norm are explicit; this does not derive them from
an 80-graph zero. There is no positive-gamma premise. -/
theorem gamma_zero_impossible (U X Y k eta R : V)
    (hU : 0 < U) (hY : 8 ≤ Y) (hk : 0 < k)
    (hgap : R+1 < k) (hcX : X < eta+Y*k)
    (hnorm :
      let a := X*Y+Y
      let c := eta+Y*k
      let H := 3+4*a
      let P := U*(X+a*c)+H*(U*(0:V)+R+1)
      let N := H*k
      magnitude (P,N)*magnitude (P,N)=U*U*(1+(H+a*a)*(c*c))) : False := by
  obtain ⟨d,hd,he,hn⟩ := direct_main_orientation U X Y k eta (0:V) R hU hY hk hnorm
  let a : V := X*Y+Y
  let c : V := eta+Y*k
  let H : V := 3+4*a
  have hH : 0 < H := by dsimp [H]; simp
  have hcs : ((a+1)*c)*((a+1)*c) < d*d := by
    rw [hn]
    dsimp [H]
    nlinarith [mul_nonneg (show (0:V)≤2*a+2 by simp) (show (0:V)≤c*c by simp)]
  have hdc : (a+1)*c < d := lt_of_mul_self_lt_mul_self₀ (by simp) hcs
  have hdx : X+a*c < d := by dsimp [c] at hcX; nlinarith
  have hUterm : U*(X+a*c) < U*d := mul_lt_mul_of_pos_left hdx hU
  have hHterm : H*(R+1) < H*k := mul_lt_mul_of_pos_left hgap hH
  have hstrict : U*(X+a*c)+H*(R+1) < H*k+U*d := by linarith
  have hbalance : U*(X+a*c)+H*(R+1) = H*k+U*d := by
    simpa [a,c,H] using he
  exact (ne_of_lt hstrict) hbalance

end DiophantineConsistency.GammaZeroNarrowDraft

#print axioms DiophantineConsistency.GammaZeroNarrowDraft.first_ordinate_lower
#print axioms DiophantineConsistency.GammaZeroNarrowDraft.gamma_zero_impossible
