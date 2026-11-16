import NativeChecker
import UpstreamCommandAudit
import CheckerRuleSyntax

/-! Rule-level comparison to source-extracted PA196 checker expressions.
The preceding-table callback represents `nth previous`; this theorem does not
identify the transcribed fuel recursion with Foundation's model-valued table. -/
namespace PA196CertificateStack.NativeChecker
open PA196.Arithmetic
open PA196.Arithmetic.CheckerRule

theorem rule_matches_extracted_source (previous : Nat → Nat) (tag payload : Nat) :
    rule previous tag payload = Scalar.evalNat CheckerRule.rule previous tag payload := by
  have h : tag = 0 ∨ tag = 1 ∨ tag = 2 ∨ tag = 3 ∨ tag = 4 ∨ tag = 5 ∨
      tag = 6 ∨ tag = 7 ∨ tag = 8 ∨ tag = 9 ∨ 10 ≤ tag := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
  all_goals
    try
      have hx : ∃ n, tag = n + 10 := ⟨tag-10, by omega⟩
      obtain ⟨n, rfl⟩ := hx
  all_goals
    simp [rule, CheckerRule.rule, CheckerRule.mp, CheckerRule.gen,
      CheckerRule.leaf1, CheckerRule.leaf2, CheckerRule.leaf3, CheckerRule.leaf4,
      CheckerRule.leaf5, CheckerRule.leaf6, CheckerRule.leaf8, CheckerRule.rawBundle,
      CheckerRule.requireZero, CheckerRule.minor, CheckerRule.major, CheckerRule.accepted,
      CheckerRule.zero, CheckerRule.one, CheckerRule.r1, CheckerRule.r2, CheckerRule.r3,
      CheckerRule.r4, CheckerRule.a, CheckerRule.b, CheckerRule.c, CheckerRule.u, CheckerRule.h,
      Scalar.evalNat, HeadGraphs.implicationExpr, HeadGraphs.universalExpr,
      HeadGraphs.head1Expr, HeadGraphs.head2Expr, HeadGraphs.head3Expr, HeadGraphs.head4Expr,
      HeadGraphs.head5Expr, HeadGraphs.head6Expr, HeadGraphs.rho8Expr, HeadGraphs.bundleExpr,
      HeadGraphs.eqVacExpr, HeadGraphs.memVacExpr, HeadGraphs.pointExpr, HeadGraphs.separationExpr,
      HeadGraphs.im, HeadGraphs.al, HeadGraphs.mem, HeadGraphs.eqn, HeadGraphs.neg,
      HeadGraphs.conj, HeadGraphs.ex, M6.PA.ActualArithmeticGraph.evalNat,
      Native.I, Native.M, Native.U, Native.E, Native.N, Native.ex, Native.conj,
      Native.head1, Native.head2, Native.head3, Native.head4, Native.head5, Native.head6,
      Native.rho8, Native.bundle, Native.eqVac, Native.memVac, Native.point,
      Native.separation, Native.separationTail, PA196UpstreamCommandAudit.pair_eq,
      left, right, PA196UpstreamCommandAudit.decode_eq] <;> try omega

end PA196CertificateStack.NativeChecker

#print axioms PA196CertificateStack.NativeChecker.rule_matches_extracted_source
