import DiophantineConsistency.ArithmeticProofWordBoundLevel
import DiophantineConsistency.ArithmeticEnumBoundFair

/-! # An explicit elementary bound on the compiled C222 refutation word

Every row of `ArithmeticProofWordRowPerm222.rowValue` raises the level of its
child words by a factor six (`row_le`): MP and GEN append the children with
the level-linear append law, and every leaf, rho8 and bundle row is a fixed
circuit on payload components below the code. Since a code `raw+1` has its
children below `raw/12`, an IΣ1 order induction gives

`rawWord n ≤ lev (rowCoeff * n)` (`rawWord_le`),

so the halting reset word is below
`Bword code = 2 * 2^(2^(6*rowCoeff*code + 52))` (`refutationWord_le`).

`rowCoeff = explicitCoeff + rho8Coeff`. `explicitCoeff` is a closed,
evaluated numeral (`explicitCoeff_eq`). `rho8Coeff = cb rho8Circuit` is the
level coefficient of the rho8 circuit, which `ArithmeticProofWordRowPerm222`
selects by `Classical.choose`; it is a fixed standard natural number, but
its numeric value is not evaluated in Lean. Every statement holds in every
model of IΣ1 and asserts no new trust boundary. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
namespace DiophantineConsistency.ArithmeticProofWordBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCantor
open ArithmeticCommandWordPerm222 ArithmeticCommandAppendPerm222 ArithmeticCommandBlockPerm222
open ArithmeticCommandCircuitPerm222 ArithmeticCommandRulePerm222
open ArithmeticProofWordBoundLevel ArithmeticProofWordRowPerm222 ArithmeticProofWordPerm222
open ArithmeticCommandRho8CircuitPerm222 (eval_mpCircuit)

/-! ## The circuit tails of MP and GEN -/

def mpTailC : Circuit :=
  Circuit.consNip (Circuit.consDrop (Circuit.consNip (Circuit.consMp .input0
    (Circuit.consAx .input0 .zero .zero (.append (Circuit.nips 10) Circuit.terminator)))))

def genTailC : Circuit :=
  Circuit.consDrop (.append (.load .input0) (Circuit.consNip
    (Circuit.consAx .input0 .zero .zero (.append (Circuit.nips 9) Circuit.terminator))))

/-- The explicit part of the row coefficient. -/
def explicitCoeff : ℕ :=
  62 + cb mpTailC + cb genTailC + cb Circuit.discard + cb leaf1 + cb leaf2 + cb leaf3 +
    cb leaf4 + cb leaf5 + cb leaf6 + cb leaf7 + cb bundleCircuit

theorem explicitCoeff_eq : explicitCoeff = 6973 := rfl

/-- The level coefficient of the classically chosen rho8 circuit. -/
noncomputable def rho8Coeff : ℕ := cb rho8Circuit

noncomputable def rowCoeff : ℕ := explicitCoeff + rho8Coeff

/-- Coefficient and offset of the final word bound. -/
noncomputable def wordCoeff : ℕ := 6 * rowCoeff
def wordOffset : ℕ := 52

theorem terminator_offset : cb Circuit.terminator + 36 = wordOffset := by decide

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **The explicit word bound** `2 * 2^(2^(wordCoeff*code + 52))`. -/
noncomputable def Bword (code : V) : V := lev ((wordCoeff : V) * code + (wordOffset : V))

noncomputable def BwordDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y code. ∃ s, s = ↑wordCoeff * code + ↑wordOffset ∧ !levDef y s”

instance Bword_defined : 𝚺₁-Function₁[V] Bword via BwordDef := .mk fun v => by
  simp [BwordDef, Bword, numeral_eq_natCast]

instance Bword_definable : 𝚺₁-Function₁ (Bword : V → V) := Bword_defined.to_definable

theorem eval_mpTailC (a b c u : V) : mpTailC.eval a b c u = mpTail a := by
  simp only [mpTailC, Circuit.eval, Circuit.eval_consDrop, Circuit.eval_consNip,
    Circuit.eval_consMp, Circuit.eval_consAx, Circuit.eval_nips, Circuit.eval_terminator, mpTail]

theorem eval_genTailC (a b c u : V) : genTailC.eval a b c u = genTail a := by
  simp only [genTailC, Circuit.eval, Circuit.eval_consDrop, Circuit.eval_consNip,
    Circuit.eval_consAx, Circuit.eval_nips, Circuit.eval_terminator, genTail]

theorem eval_genCircuit_split (a u : V) : genCircuit.eval a u 0 0 = appendValue u (genTail a) := by
  rw [← eval_genTailC a u 0 0]
  rfl

theorem cantor_sum_le (a b : V) : a + b ≤ cantor a b := by
  unfold cantor
  exact le_trans (le_triangle (a + b)) le_self_add

private theorem coeff_cast_le {k : ℕ} (h : k ≤ rowCoeff) : (k : V) ≤ (rowCoeff : V) := by
  exact_mod_cast h

private theorem fixed_le (e : Circuit) (he : cb e ≤ rowCoeff) {p su sv x1 x2 x3 x4 : V}
    (h1 : x1 ≤ p) (h2 : x2 ≤ p) (h3 : x3 ≤ p) (h4 : x4 ≤ p) :
    e.eval x1 x2 x3 x4 ≤ lev (6 * su + 6 * sv + (rowCoeff : V) * (p + 1)) := by
  have hl := fun x (hx : x ≤ p) => le_trans hx (le_lev p)
  refine le_lev_of (eval_le e (hl _ h1) (hl _ h2) (hl _ h3) (hl _ h4)) ?_
  exact le_trans (mul_le_mul_of_nonneg_right (coeff_cast_le he) (Arithmetic.zero_le _))
    le_add_self

/-- Every row multiplies its child levels by at most six. -/
theorem row_le (tag p u v su sv : V) (hu : u ≤ lev su) (hv : v ≤ lev sv) :
    rowValue tag p u v ≤ lev (6 * su + 6 * sv + (rowCoeff : V) * (p + 1)) := by
  have ha : first p ≤ p := first_le p
  have ht : second p ≤ p := second_le p
  have hb : first (second p) ≤ p := le_trans (first_le _) ht
  have hc : second (second p) ≤ p := le_trans (second_le _) ht
  have hx : first (second (second p)) ≤ p := le_trans (first_le _) hc
  have hy : second (second (second p)) ≤ p := le_trans (second_le _) hc
  have h0 : (0 : V) ≤ p := Arithmetic.zero_le p
  have hal : first p ≤ lev p := le_trans ha (le_lev p)
  have hzl : (0 : V) ≤ lev p := Arithmetic.zero_le _
  unfold rowValue
  dsimp only
  by_cases g0 : tag = 0
  · rw [if_pos g0]
    exact fixed_le Circuit.discard (by unfold rowCoeff explicitCoeff; omega) h0 h0 h0 h0
  rw [if_neg g0]
  by_cases g1 : tag = 1
  · rw [if_pos g1]
    rw [eval_mpCircuit]
    simp only [Circuit.eval, mpBlockWord]
    have hT : mpTail (first p) ≤ lev ((cb mpTailC : V) * (p + 1)) := by
      rw [← eval_mpTailC (first p) 0 0 0]
      exact eval_le mpTailC hal hzl hzl hzl
    have h1 := append_le hv hT
    have h2 := dropWord_le (le_trans (by norm_num) le_add_self) h1
    have h3 := append_le hu h2
    refine le_lev_of h3 ?_
    have hC : (cb mpTailC : V) + 62 ≤ (rowCoeff : V) := by
      have : cb mpTailC + 62 ≤ rowCoeff := by unfold rowCoeff explicitCoeff; omega
      exact_mod_cast this
    calc (cb mpTailC : V) * (p + 1) + 6 * sv + 30 + 2 + 6 * su + 30
        = 6 * su + 6 * sv + ((cb mpTailC : V) * (p + 1) + 62) := by ring
      _ ≤ 6 * su + 6 * sv + ((cb mpTailC : V) + 62) * (p + 1) :=
          shift_le _ (add_const_le _ p 62)
      _ ≤ 6 * su + 6 * sv + (rowCoeff : V) * (p + 1) :=
          shift_le _ (mul_le_mul_of_nonneg_right hC (Arithmetic.zero_le _))
  rw [if_neg g1]
  by_cases g2 : tag = 2
  · rw [if_pos g2]
    rw [eval_genCircuit_split]
    have hG : genTail (first p) ≤ lev ((cb genTailC : V) * (p + 1)) := by
      rw [← eval_genTailC (first p) 0 0 0]
      exact eval_le genTailC hal hzl hzl hzl
    refine le_lev_of (append_le hu hG) ?_
    have hC : (cb genTailC : V) + 30 ≤ (rowCoeff : V) := by
      have : cb genTailC + 30 ≤ rowCoeff := by unfold rowCoeff explicitCoeff; omega
      exact_mod_cast this
    calc (cb genTailC : V) * (p + 1) + 6 * su + 30
        = 6 * su + ((cb genTailC : V) * (p + 1) + 30) := by ring
      _ ≤ 6 * su + ((cb genTailC : V) + 30) * (p + 1) := shift_le _ (add_const_le _ p 30)
      _ ≤ 6 * su + 6 * sv + (rowCoeff : V) * (p + 1) := by
          rw [add_assoc]
          exact shift_le _ (le_trans (mul_le_mul_of_nonneg_right hC (Arithmetic.zero_le _))
            le_add_self)
  rw [if_neg g2]
  by_cases g3 : tag = 3
  · rw [if_pos g3]
    exact fixed_le leaf1 (by unfold rowCoeff explicitCoeff; omega) ha ht h0 h0
  rw [if_neg g3]
  by_cases g4 : tag = 4
  · rw [if_pos g4]
    exact fixed_le leaf2 (by unfold rowCoeff explicitCoeff; omega) ha hb hc h0
  rw [if_neg g4]
  by_cases g5 : tag = 5
  · rw [if_pos g5]
    exact fixed_le leaf3 (by unfold rowCoeff explicitCoeff; omega) ha hb hc h0
  rw [if_neg g5]
  by_cases g6 : tag = 6
  · rw [if_pos g6]
    exact fixed_le leaf4 (by unfold rowCoeff explicitCoeff; omega) ha hb hc h0
  rw [if_neg g6]
  by_cases g7 : tag = 7
  · rw [if_pos g7]
    exact fixed_le leaf5 (by unfold rowCoeff explicitCoeff; omega) ha hb hc h0
  rw [if_neg g7]
  by_cases g8 : tag = 8
  · rw [if_pos g8]
    exact fixed_le leaf6 (by unfold rowCoeff explicitCoeff; omega) ha ht h0 h0
  rw [if_neg g8]
  by_cases g9 : tag = 9
  · rw [if_pos g9]
    exact fixed_le leaf7 (by unfold rowCoeff explicitCoeff; omega) ha hb hc h0
  rw [if_neg g9]
  by_cases g10 : tag = 10
  · rw [if_pos g10]
    exact fixed_le rho8Circuit (by unfold rowCoeff rho8Coeff; omega) ha hb hx hy
  rw [if_neg g10]
  by_cases g11 : tag = 11
  · rw [if_pos g11]
    exact fixed_le bundleCircuit (by unfold rowCoeff explicitCoeff; omega) ha hb hc h0
  rw [if_neg g11]
  exact Arithmetic.zero_le _

/-- GEN ignores its second child word. -/
theorem rowValue_gen (p u v : V) : rowValue 2 p u v = rowValue 2 p u 0 := by
  simp [rowValue]

private theorem final_le {K C X p raw : V} (hKC : C ≤ K) (hp12 : 12 * p ≤ raw)
    (hX : X ≤ 6 * (K * p)) : X + C * (p + 1) ≤ K * (raw + 1) := by
  calc X + C * (p + 1) ≤ 6 * (K * p) + K * (p + 1) :=
        _root_.add_le_add hX (mul_le_mul_of_nonneg_right hKC (Arithmetic.zero_le _))
    _ = 7 * (K * p) + K := by ring
    _ ≤ 12 * (K * p) + K :=
        _root_.add_le_add (mul_le_mul_of_nonneg_right (by norm_num) (Arithmetic.zero_le _)) le_rfl
    _ = K * (12 * p) + K := by ring
    _ ≤ K * raw + K :=
        _root_.add_le_add (mul_le_mul_of_nonneg_left hp12 (Arithmetic.zero_le _)) le_rfl
    _ = K * (raw + 1) := by ring

/-- **Size invariant**, by IΣ1 order induction over the proof code. -/
theorem rawWord_le_of (K : V) (hK : (rowCoeff : V) ≤ K) :
    ∀ n : V, rawWord n ≤ lev (K * n) := by
  intro n
  induction n using ISigma1.sigma1_order_induction
  · definability
  case ind n ih =>
    rcases zero_or_succ n with (rfl | ⟨raw, rfl⟩)
    · rw [rawWord_zero]
      exact Arithmetic.zero_le _
    · rw [rawWord_succ]
      have hp12 : 12 * (raw / 12) ≤ raw := mul_div_le raw 12
      have ht : second (raw / 12) ≤ raw / 12 := second_le _
      have hu0 := ih _ (lt_succ_iff_le.mpr (ArithmeticHistory222.tail_le raw))
      have hu1 := ih _ (lt_succ_iff_le.mpr (ArithmeticHistory222.minor_le raw))
      have hv1 := ih _ (lt_succ_iff_le.mpr (ArithmeticHistory222.major_le raw))
      by_cases h2 : raw % 12 = 2
      · rw [if_pos h2, h2, rowValue_gen]
        refine le_lev_of (row_le 2 _ _ 0 _ 0 hu0 (Arithmetic.zero_le _)) ?_
        refine final_le hK hp12 ?_
        rw [mul_zero, add_zero]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht (Arithmetic.zero_le K))
          (Arithmetic.zero_le 6)
      · rw [if_neg h2]
        refine le_lev_of (row_le _ _ _ _ _ _ hu1 hv1) ?_
        refine final_le hK hp12 ?_
        have hs := cantor_sum_le (first (second (raw / 12))) (second (second (raw / 12)))
        rw [cantor_projections] at hs
        calc 6 * (K * first (second (raw / 12))) + 6 * (K * second (second (raw / 12)))
            = 6 * (K * (first (second (raw / 12)) + second (second (raw / 12)))) := by ring
          _ ≤ 6 * (K * (raw / 12)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_trans hs ht)
              (Arithmetic.zero_le K)) (Arithmetic.zero_le 6)

theorem rawWord_le (n : V) : rawWord n ≤ lev ((rowCoeff : V) * n) :=
  rawWord_le_of _ le_rfl n

end Model

section Correctness
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
open ArithmeticEnumStepPerm222 ArithmeticEnumRunPerm222

/-- **The compiled halting word is below `Bword code`.** No validity premise. -/
theorem refutationWord_le (code : V) :
    ArithmeticProofWordEnumPerm222.resetWord (refutationWord code) ≤ Bword code := by
  have hT : ArithmeticCommandLeafPerm222.terminatorWord ≤ lev ((cb Circuit.terminator : V) * (0 + 1)) := by
    rw [← Circuit.eval_terminator (0 : V) 0 0 0]
    have h0 : (0 : V) ≤ lev 0 := Arithmetic.zero_le _
    exact eval_le Circuit.terminator h0 h0 h0 h0
  have hR := append_le (rawWord_le code) hT
  have hn : (1 : V) ≤ (cb Circuit.terminator : V) * (0 + 1) + 6 * ((rowCoeff : V) * code) + 30 :=
    le_trans (by norm_num) le_add_self
  have h4 : (1 : V) + 3 ≤ lev ((cb Circuit.terminator : V) * (0 + 1) +
      6 * ((rowCoeff : V) * code) + 30) :=
    le_trans (by norm_num) (four_le_lev _)
  have hz : (0 : V) ≤ lev ((cb Circuit.terminator : V) * (0 + 1) +
      6 * ((rowCoeff : V) * code) + 30) := Arithmetic.zero_le _
  have hW := axWord_le hn h4 hz hz hR
  unfold ArithmeticProofWordEnumPerm222.resetWord Bword refutationWord
  refine le_lev_of hW (le_of_eq ?_)
  have ho : (wordOffset : V) = (cb Circuit.terminator : V) + 36 := by
    rw [← terminator_offset]; push_cast; ring
  rw [ho]
  unfold wordCoeff
  push_cast
  ring


/-- **Refutation ⇒ enumerator halt within `Bword code ^ 2` steps.** -/
theorem enum_halts_le_of_refutation_code (code : V)
    (h : ArithmeticHistory222.checkDef.val.Evalb ![code,1]) :
    ∃ time ≤ Bword code * Bword code, run time (liveValue 0 4 0) = 0 := by
  obtain ⟨time, ht, hr⟩ := ArithmeticEnumBoundFair.enum_halts_le_of_refutation code 0 h
  have hw : ArithmeticEnumBoundFair.refutationResetWord code ≤ Bword code :=
    refutationWord_le code
  exact ⟨time, le_trans ht (mul_le_mul hw hw (Arithmetic.zero_le _) (Arithmetic.zero_le _)), hr⟩

end Correctness
end DiophantineConsistency.ArithmeticProofWordBound
