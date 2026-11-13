#!/usr/bin/env python3
"""Build a Carrier65-free literal graph client for the current14 base."""
import hashlib
from pathlib import Path

HERE = Path(__file__).resolve().parent
PREVIOUS = HERE.parent/'rational-carrier64-lean-identity/RationalCarrier64.lean'
OUT = HERE/'RationalCarrier64Current.lean'
source = PREVIOUS.read_bytes()
if hashlib.sha256(source).hexdigest() != '8676e328432ca3fd070dbd4abe6ae097137138aff4b2ceeead955e671f8b9a3b':
    raise RuntimeError('unexpected prior literal source')
s = source.decode()
s = s.replace('import DiophantineConsistency.Carrier65',
              'import DiophantineConsistency.CurrentEquationSyntax2011\nimport Mathlib.Tactic.Ring', 1)
s = s.replace('DiophantineConsistency.RationalCarrier64',
              'DiophantineConsistency.RationalCarrier64Current')
start = s.index('/-- Binding to the existing 65-operation arithmetic front. -/')
s = s[:start] + '''/-- Bind the literal 65-row graph directly to the current14 syntax. -/
theorem value65_eq_expressionAt (p : Fin 4 → ℤ) (v : Fin 14 → ℤ) :
    value65 p v = (ObjectCurrentEquation2011.expressionAt p).eval v := by
  simp only [value65, head, rank65, suffix, ObjectCurrentEquation2011.expressionAt,
    Expr.eval_add, Expr.eval_sub, Expr.eval_mul, Expr.eval_pow,
    Expr.eval_var, Expr.eval_constant, pow_succ, pow_zero, one_mul, mul_assoc]

#print axioms values_equal
#print axioms zero_iff
#print axioms value65_eq_expressionAt

end DiophantineConsistency.RationalCarrier64Current
'''
OUT.write_text(s)
print(hashlib.sha256(s.encode()).hexdigest())
