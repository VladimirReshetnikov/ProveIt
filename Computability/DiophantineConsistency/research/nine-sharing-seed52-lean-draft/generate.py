#!/usr/bin/env python3
"""Generate unverified Lean syntax and candidate degree/normalization proofs."""
import json,hashlib,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];src=D/'research/nine-sharing-quartic65-52-candidate/seed.json';b=src.read_bytes();assert hashlib.sha256(b).hexdigest()=='db5fc39eb7c8075ff7417b084a0c9a4755b497b1be388fe9d0aa1e65bad356ff';data=json.loads(b);assert data['jones_witness_count']==52 and len(data['residuals'])==39
ports={'beta':0,'K0':1,'MC':2,'MF':3}
def render(t):
 op=t[0]
 if op=='num':return f'(Expr.constant ({t[1]} : ℤ))'
 if op=='port':return f'(Expr.constant (p {ports[t[1]]}))'
 if op=='var':return f'(Expr.var {t[1]})'
 symbol={'add':'+','sub':'-','mul':'*'}[op];return f'({render(t[1])} {symbol} {render(t[2])})'
terms=[render(x['expr']) for x in data['residuals']]
header='''import DiophantineConsistency.NineFreshJones

/-! UNVERIFIED DRAFT. Generated from the externally audited 52-witness
sharing candidate. This file has not been compiled; model bridge and iPRA
endpoint are explicitly not provided. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed52

/-- The first residual; at zero witnesses its value is `-(p 0 + 1)^2`. -/
def firstResidual (p : Fin 4 → ℤ) : Expr (Fin 53) :=
  '''+terms[0]+'''\n
/-- The remaining 38 quadratic residuals in graph order. -/
def remainingResiduals (p : Fin 4 → ℤ) : List (Expr (Fin 53)) :=
  [\n'''
body=',\n'.join('    '+x for x in terms[1:]);footer='''\n  ]

/-- Sum of squared residuals; coordinate 0 is not used. -/
def seed (p : Fin 4 → ℤ) : Expr (Fin 53) :=
  firstResidual p * firstResidual p +
    QuarticSyntax.sumExpressions ((remainingResiduals p).map fun e => e * e)

/-- Candidate syntax-degree calculation; not yet checked by Lean. -/
theorem seed_weightedDegree (p : Fin 4 → ℤ) :
    (seed p).weightedDegree (fun _ => 1) ≤ 4 := by
  simp [seed, firstResidual, remainingResiduals, QuarticSyntax.sumExpressions,
    Expr.weightedDegree]

/-- Candidate polynomial-degree bound; not yet checked by Lean. -/
theorem seed_degree (p : Fin 4 → ℤ) : (seed p).toPolynomial.totalDegree ≤ 4 := by
  have h := Expr.degree_evalRing_le (seed p) (fun _ => 1)
    (MvPolynomial.X : Fin 53 → MvPolynomial (Fin 53) ℤ) (by intro i; simp)
  rw [Expr.evalRing_X] at h
  exact h.trans (seed_weightedDegree p)

/-- Jones normalization valuation: the distinguished input is arbitrary. -/
def zeroWitness (x : ℤ) (j : Fin 53) : ℤ := if j = 0 then x else 0

/-- Candidate first-residual evaluation; not yet checked by Lean. -/
theorem firstResidual_zeroWitness (p : Fin 4 → ℤ) (x : ℤ) :
    (firstResidual p).eval (zeroWitness x) = -(p 0 + 1) ^ 2 := by
  simp [firstResidual, zeroWitness, Expr.eval]
  ring

/-- Candidate nonnegativity helper for every finite squared residual sum. -/
theorem eval_sumSquares_nonneg (es : List (Expr (Fin 53))) (v : Fin 53 → ℤ) :
    0 ≤ (QuarticSyntax.sumExpressions (es.map fun e => e * e)).eval v := by
  induction es with
  | nil => simp [QuarticSyntax.sumExpressions, Expr.eval]
  | cons e es ih =>
    simp only [List.map_cons, QuarticSyntax.sumExpressions, Expr.eval_add, Expr.eval_mul]
    exact add_nonneg (mul_self_nonneg _) ih

/-- Candidate all-input normalization, assuming the first port is positive. -/
theorem seed_normalized (p : Fin 4 → ℤ) (hp : 0 < p 0) (x : ℤ) :
    (seed p).eval (zeroWitness x) ≠ 0 := by
  have hne : (firstResidual p).eval (zeroWitness x) ≠ 0 := by
    rw [firstResidual_zeroWitness]
    nlinarith
  have hs : 0 < (firstResidual p).eval (zeroWitness x) *
      (firstResidual p).eval (zeroWitness x) := mul_self_pos.mpr hne
  have ht := eval_sumSquares_nonneg (remainingResiduals p) (zeroWitness x)
  have hpos : 0 < (seed p).eval (zeroWitness x) := by
    simpa only [seed, Expr.eval_add, Expr.eval_mul] using add_pos_of_pos_of_nonneg hs ht
  exact ne_of_gt hpos

-- Unresolved: prove the all-IΣ₁-model zero bridge, then instantiate
-- NineFreshJones.nine_iff and transfer the current iPRA endpoint.
end DiophantineConsistency.SharingSeed52
'''
out=header+body+footer;target=P/'SharingSeed52.lean';assert not target.exists();target.write_text(out);print('seed_json_sha256',hashlib.sha256(b).hexdigest(),'lean_source_sha256',hashlib.sha256(out.encode()).hexdigest(),'residual_count',len(terms))
