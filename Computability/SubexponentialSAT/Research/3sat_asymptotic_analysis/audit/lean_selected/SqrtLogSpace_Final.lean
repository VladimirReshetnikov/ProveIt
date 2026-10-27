import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLargeEntry
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Statement
import OAI.Algorithms.SubexponentialSAT.SqrtLog.StatementCanonical

/-! Exact counting and SAT on one fixed primitive run, with the unchanged
ETH square-root-log time scale and polynomial all-prefix visited space. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem compiled_exact_count_and_sat (k : ℕ) (hk : 2 ≤ k) :
    ∃ (labels : ℕ) (program : BitProgram.Program 80 1220 labels)
      (C A S : ℝ) (d e : ℕ),
      program.outputStack = 1216 ∧
      0 < C ∧ 0 < A ∧ 0 < S ∧ 0 < d ∧ 0 < e ∧
      ∀ (n : ℕ) (F : SAT.CNF (Fin n)), SAT.WidthAtMost k F →
        ∃ (time : ℕ) (final : LocatedCfg (GuardedCompiler.primitive program)),
          Computation.Trace (locatedStep (GuardedCompiler.primitive program)) time
            (locatedInit (GuardedCompiler.primitive program) (Encoding.encodeCNF F)) final ∧
          final.config.tapes (256 : Fin 1220) =
            Turing.Tape.mk₁ ((countWord (SAT.count F)).map some) ∧
          final.config.tapes (1216 : Fin 1220) =
            Turing.Tape.mk₁ [some (decide (0 < SAT.count F))] ∧
          final.config.state = Sum.inl (decide (0 < SAT.count F)) ∧
          BinaryArithmetic.toNat (countWord (SAT.count F)) = SAT.count F ∧
          (countWord (SAT.count F)).length ≤ n + 1 ∧
          (time : ℝ) ≤ OAI.Algorithms.SubexponentialSAT.SqrtLog.Statement.runtimeBound C A d
            (Encoding.formulaBitLength F) n ∧
          ∀ (prefixSteps : ℕ)
            (intermediate : LocatedCfg (GuardedCompiler.primitive program)), prefixSteps ≤ time →
            Computation.Trace (locatedStep (GuardedCompiler.primitive program)) prefixSteps
              (locatedInit (GuardedCompiler.primitive program) (Encoding.encodeCNF F))
              intermediate →
            (visitedSpace intermediate : ℝ) ≤
              S * ((Encoding.formulaBitLength F : ℝ) + 1) ^ e := by
  obtain ⟨cutoff, C, A, d, S, e, hC, hA, hlarge⟩ := NativeLargeEntry.run k hk
  obtain ⟨hC', hA', hd', htimeBound⟩ :=
    NativeOuterBudgets.runtime_with_fallback C A d hC (by linarith)
  obtain ⟨hS', he', hspaceBound⟩ :=
    NativeOuterBudgets.space_with_fallback (S : ℝ) e (Nat.cast_nonneg S)
  refine ⟨_, Native.countingProgram cutoff k (NativeLeafProgram.command k),
    C + 28700, A + 1, (S : ℝ) + 5022741, d + 2, e + 2,
    rfl, hC', hA', hS', hd', he', ?_⟩
  intro n F hw
  by_cases hn : n ≤ cutoff
  · obtain ⟨time, final, htrace, hhalt, hcount, hanswer, htime, hprefix⟩ :=
      Native.entry_small_primitive (Native.outerCommand k (NativeLeafProgram.command k)) F hn
    refine ⟨time, final, htrace, hcount, hanswer, hhalt,
      countWord_toNat _, countWord_count_length F, ?_, ?_⟩
    · exact (Nat.cast_le.mpr htime).trans (htimeBound n (Encoding.formulaBitLength F)).2
    · intro prefixSteps intermediate hp htr
      have hsmall := hprefix prefixSteps intermediate hp htr
      have hpoly : 1220 * (2 * Encoding.formulaBitLength F +
          4100 * (Encoding.formulaBitLength F + 1) ^ 2 + 15) ≤
          5022740 * (Encoding.formulaBitLength F + 1) ^ 2 := by
        have hbase : Encoding.formulaBitLength F + 1 ≤
            (Encoding.formulaBitLength F + 1) ^ 2 := Nat.le_self_pow (by decide) _
        omega
      exact (Nat.cast_le.mpr (hsmall.trans hpoly)).trans
        (hspaceBound (Encoding.formulaBitLength F)).2
  · obtain ⟨time, final, htrace, hhalt, hcount, hanswer, htime, hprefix⟩ :=
      hlarge n F hw (by omega)
    refine ⟨time, final, htrace, hcount, hanswer, hhalt,
      countWord_toNat _, countWord_count_length F,
      htime.trans (htimeBound n (Encoding.formulaBitLength F)).1, ?_⟩
    intro prefixSteps intermediate hp htr
    have hreal : (visitedSpace intermediate : ℝ) ≤
        (S : ℝ) * ((Encoding.formulaBitLength F : ℝ) + 1) ^ e := by
      exact_mod_cast hprefix prefixSteps intermediate hp htr
    exact hreal.trans (hspaceBound (Encoding.formulaBitLength F)).1

/-- One fixed primitive machine exactly counts every bounded-width formula,
decides satisfiability, meets the square-root-logarithmic time bound, and uses
only polynomially many visited tape cells at every execution prefix. -/
theorem exact_count_and_sat (k : ℕ) (hk : 2 ≤ k) :
    ∃ (machine : Computation.PrimitiveMachine)
      (countTape answerTape : Fin machine.tapeCount)
      (C A S : ℝ) (d e : ℕ),
      0 < C ∧ 0 < A ∧ 0 < S ∧ 0 < d ∧ 0 < e ∧
      ∀ (n : ℕ) (F : SAT.CNF (Fin n)), SAT.WidthAtMost k F →
        ∃ (time : ℕ) (final : LocatedCfg machine),
          Computation.Trace (locatedStep machine) time
            (locatedInit machine (Encoding.encodeCNF F)) final ∧
          final.config.tapes countTape =
            Turing.Tape.mk₁ ((countWord (SAT.count F)).map some) ∧
          final.config.tapes answerTape =
            Turing.Tape.mk₁ [some (decide (0 < SAT.count F))] ∧
          final.config.state = Sum.inl (decide (0 < SAT.count F)) ∧
          BinaryArithmetic.toNat (countWord (SAT.count F)) = SAT.count F ∧
          (countWord (SAT.count F)).length ≤ n + 1 ∧
          (time : ℝ) ≤ OAI.Algorithms.SubexponentialSAT.SqrtLog.Statement.runtimeBound C A d
            (Encoding.formulaBitLength F) n ∧
          ∀ (prefixSteps : ℕ) (intermediate : LocatedCfg machine),
            prefixSteps ≤ time →
            Computation.Trace (locatedStep machine) prefixSteps
              (locatedInit machine (Encoding.encodeCNF F)) intermediate →
            (visitedSpace intermediate : ℝ) ≤
              S * ((Encoding.formulaBitLength F : ℝ) + 1) ^ e := by
  obtain ⟨labels, program, C, A, S, d, e, _hout, hC, hA, hS, hd, he, hrun⟩ :=
    compiled_exact_count_and_sat k hk
  refine ⟨GuardedCompiler.primitive program, (256 : Fin 1220), (1216 : Fin 1220),
    C, A, S, d, e, hC, hA, hS, hd, he, ?_⟩
  exact hrun

theorem exact_count_eth (k : ℕ) (hk : 2 ≤ k) :
    ∃ (labels : ℕ) (program : BitProgram.Program 80 1220 labels)
      (C A S : ℝ) (d e : ℕ),
      program.outputStack = 1216 ∧
      0 < C ∧ 0 < A ∧ 0 < S ∧ 0 < d ∧ 0 < e ∧
      ∀ (n : ℕ) (F : SAT.CNF (Fin n)), 20 ≤ n → SAT.WidthAtMost k F →
        ∃ (time : ℕ) (final : LocatedCfg (GuardedCompiler.primitive program)),
          Computation.Trace (locatedStep (GuardedCompiler.primitive program)) time
            (locatedInit (GuardedCompiler.primitive program) (Encoding.encodeCNF F)) final ∧
          final.config.tapes (256 : Fin 1220) =
            Turing.Tape.mk₁ ((countWord (SAT.count F)).map some) ∧
          final.config.tapes (1216 : Fin 1220) =
            Turing.Tape.mk₁ [some (decide (0 < SAT.count F))] ∧
          final.config.state = Sum.inl (decide (0 < SAT.count F)) ∧
          BinaryArithmetic.toNat (countWord (SAT.count F)) = SAT.count F ∧
          (countWord (SAT.count F)).length ≤ n + 1 ∧
          (time : ℝ) ≤ C * ((n + F.card + 1 : ℕ) : ℝ) ^ d *
            (2 : ℝ) ^ (A * rho n) ∧
          ∀ (prefixSteps : ℕ)
            (intermediate : LocatedCfg (GuardedCompiler.primitive program)), prefixSteps ≤ time →
            Computation.Trace (locatedStep (GuardedCompiler.primitive program)) prefixSteps
              (locatedInit (GuardedCompiler.primitive program) (Encoding.encodeCNF F))
              intermediate →
            (visitedSpace intermediate : ℝ) ≤
              S * ((n + F.card + 1 : ℕ) : ℝ) ^ e := by
  obtain ⟨labels, program, C, A, S, d, e, hout, hC, hA, hS, hd, he, hrun⟩ :=
    compiled_exact_count_and_sat k hk
  refine ⟨labels, program, C * ((8 * k + 7 : ℕ) : ℝ) ^ d,
    4 * A, S * ((8 * k + 7 : ℕ) : ℝ) ^ e, 2 * d, 2 * e,
    hout, by positivity, by positivity, by positivity, by omega, by omega, ?_⟩
  intro n F hn hw
  obtain ⟨time, final, htrace, hcount, hanswer, hhalt, hdecode, hlength, htime, hspace⟩ :=
    hrun n F hw
  refine ⟨time, final, htrace, hcount, hanswer, hhalt, hdecode, hlength,
    htime.trans (runtimeBound_le_eth F hw hn hC.le hA.le d), ?_⟩
  intro prefixSteps intermediate hp htr
  calc
    (visitedSpace intermediate : ℝ) ≤
        S * ((Encoding.formulaBitLength F : ℝ) + 1) ^ e :=
      hspace prefixSteps intermediate hp htr
    _ ≤ S * (((8 * k + 7 : ℕ) : ℝ) ^ e *
        ((n + F.card + 1 : ℕ) : ℝ) ^ (2 * e)) :=
      mul_le_mul_of_nonneg_left (encoding_pow_le_declaredSize F hw e) hS.le
    _ = _ := by ring

theorem sat_polynomial_space (k : ℕ) (hk : 3 ≤ k) :
    ∃ (labels : ℕ) (program : BitProgram.Program 80 1220 labels)
      (C A S : ℝ) (d e : ℕ),
      program.outputStack = 1216 ∧
      0 < C ∧ 0 < A ∧ 0 < S ∧ 0 < d ∧ 0 < e ∧
      ∀ (n : ℕ) (F : SAT.CNF (Fin n)), SAT.WidthAtMost k F →
        ∃ (answer : Bool) (time : ℕ)
          (final : LocatedCfg (GuardedCompiler.primitive program)),
          Computation.Trace (locatedStep (GuardedCompiler.primitive program)) time
            (locatedInit (GuardedCompiler.primitive program) (Encoding.encodeCNF F)) final ∧
          final.config.tapes (256 : Fin 1220) =
            Turing.Tape.mk₁ ((countWord (SAT.count F)).map some) ∧
          final.config.tapes (1216 : Fin 1220) = Turing.Tape.mk₁ [some answer] ∧
          final.config.state = Sum.inl answer ∧
          answer = decide (0 < SAT.count F) ∧
          (answer = true ↔ SAT.Satisfiable F) ∧
          (time : ℝ) ≤ OAI.Algorithms.SubexponentialSAT.SqrtLog.Statement.runtimeBound C A d
            (Encoding.formulaBitLength F) n ∧
          ∀ (prefixSteps : ℕ)
            (intermediate : LocatedCfg (GuardedCompiler.primitive program)), prefixSteps ≤ time →
            Computation.Trace (locatedStep (GuardedCompiler.primitive program)) prefixSteps
              (locatedInit (GuardedCompiler.primitive program) (Encoding.encodeCNF F))
              intermediate →
            (visitedSpace intermediate : ℝ) ≤
              S * ((Encoding.formulaBitLength F : ℝ) + 1) ^ e := by
  obtain ⟨labels, program, C, A, S, d, e, hout, hC, hA, hS, hd, he, hrun⟩ :=
    compiled_exact_count_and_sat k (by omega)
  refine ⟨labels, program, C, A, S, d, e, hout, hC, hA, hS, hd, he, ?_⟩
  intro n F hw
  obtain ⟨time, final, htrace, hcount, hanswer, hhalt, _hdecode, _hlength, htime, hspace⟩ :=
    hrun n F hw
  refine ⟨decide (0 < SAT.count F), time, final, htrace, hcount, hanswer,
    hhalt, rfl, ?_, htime, hspace⟩
  simpa only [decide_eq_true_eq] using SAT.count_pos_iff F

theorem original_sat_main : OAI.Algorithms.SubexponentialSAT.SqrtLog.Statement.MainTheorem := by
  intro k hk
  obtain ⟨labels, program, C, A, S, d, e, _hout, hC, hA, _hS, hd, _he, hrun⟩ :=
    sat_polynomial_space k hk
  refine ⟨GuardedCompiler.primitive program, C, A, d, hC, hA, hd, ?_⟩
  intro n F hw
  obtain ⟨answer, time, final, htrace, _hcount, _hanswer, hhalt, _hpositive, hsat, htime, _hspace⟩ :=
    hrun n F hw
  refine ⟨answer, time, ⟨final.config, ?_, hhalt⟩, hsat, htime⟩
  exact ⟨time, le_rfl, locatedTrace_erase htrace⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

#print axioms OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.compiled_exact_count_and_sat
#print axioms OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat
#print axioms OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_eth
#print axioms OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.sat_polynomial_space
#print axioms OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.original_sat_main
