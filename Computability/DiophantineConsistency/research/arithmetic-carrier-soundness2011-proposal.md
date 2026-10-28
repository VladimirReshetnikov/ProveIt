# Literal maintained carrier soundness: proposed next pair

Read-only plan, 2026-10-27. Proposed files are
`ArithmeticCarrierSoundness2011.lean` and its focused `Checks` only.
No new Lean source, overlay, compiler invocation or dependency refresh has
been made for this plan. This is internal IΣ1 model mathematics, not an HA
proof, a consistency equivalence, or a canonical/cofinal witness theorem.

## Exact target and import boundary

Use precisely these four imports:

```
DiophantineConsistency.ArithmeticNegativeNorms
DiophantineConsistency.ArithmeticSignedPairs
DiophantineConsistency.ArithmeticPellFirstIndex
DiophantineConsistency.CurrentEquationSyntax2011
```

The last module owns the EXISTING literal
`ObjectCurrentEquation2011.expressionAt`, `expression`, `positiveShift` and
`naturalExpression`. It already imports `ArithmeticExpression`,
`NatExpr.evalSemiring`, the full current kernel data and current mask data.
There is no new copy of the polynomial, coefficient tuple, or syntax.
Do not import the wide native/object semantics module merely to name
`ObjectCurrentEquation2011.InternalZero`: use its exact defining equality
of the two existing split evaluations directly.

For an arbitrary internal `V` with `ORingStructure V` and IΣ1, define a
convenience proposition `Equations beta K MC MF v` by the five equalities
below, with these SAME fourteen coordinates:

```
v = [J,F,alpha,z,f,i,T,s,w,N,eta,zeta,y,gamma]
q = beta*J+1; X=w*q; Y=s*q^3; E=X*Y; k=eta+zeta
c=k*Y+eta; a=E+Y; delta=(a+1)*(a+3); H=4*a+3
d=X+a*c+gamma*H
R=((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J
tau=E*N+k-R; I=delta*i*c*c
u=(f*f*c*T-(f*f*R+c))+((f*f*R+c)-f*f*c*T)

(K+w)*q+q = (K+w)*(F+alpha)+F+z*(q-1)+1
tau*tau = 1+(E*Y)*(E*Y+1)*k*k
d*d = 1+delta*c*c
f*f = 1+delta*(i*c*c)*(i*c*c)
I*I*u*u+y*y = 1+I*I*y*y
```

This is exactly the argument package of
`ArithmeticPellFirstIndex.maintained_first_indices` and
`ArithmeticPellPowerRecovery.maintained_power`; the latter additionally
requires beta≥15. Neither existing theorem is used to establish the norms.
`scalar_window` from FirstIndex is used only AFTER transport is derived.

Planned public statements (names may be mechanically adjusted, not scope):

* `expressionAt_equations (p : Fin 4 → ℕ) (v : Fin 14 → V)` takes
  `0 < (p 0 : V)`, `(p 2 : V) < p 0`, `(p 3 : V) < 2*p 0`,
  `∀j, 0<v j`, and
  `(expressionAt (fun j => (p j : ℤ))).splitNatural.1.evalSemiring v =`
  `(expressionAt (fun j => (p j : ℤ))).splitNatural.2.evalSemiring v`.
  It returns `Equations (p 0) (p 1) (p 2) (p 3) v`.
* `current_equations (v : Fin 14 → V)` takes ONLY `∀j,0<v j` and the
  corresponding actual `expression.splitNatural` equality. It returns
  `Equations beta K lowPort (highPort+beta) v`, with natural constants cast
  into V. All three generic port bounds are proved from the actual data.
* `current_natural_equations (v : Fin 14 → V)` takes ONLY the actual
  `naturalExpression.splitNatural` equality. It returns the same five
  equations at `(fun j => v j+1)`. The one positive shift is structural.

An optional direct `ArithmeticExpression.sat_equation` wrapper merely
rewrites the same zero equality. No no-zero or proof-reflection conclusion
is proposed. A later one-line client may feed the five equations into the
accepted maintained indices/power results; importing PowerRecovery and
claiming that composed endpoint are not part of this minimal pair.

## Signed binding BEFORE any transport or rank bound

Let `B=beta*J`, `q=B+1`, and `Q2=q*q-1`. Positivity of beta,J gives q≥2
and `Q2+1=q*q` without transport. Everything else stays a formal difference.
Define canonical raw-rank components

```
M=(MC+q*MF)*J
Rplus=(B*q+alpha)*Q2+M
Rminus=B*F*Q2
Tpair=(E*N+k+Rminus, Rplus)
Vpair=(f*f*(c*T+Rminus), f*f*Rplus+c)
t=ArithmeticSignedPairs.magnitude Tpair
vabs=ArithmeticSignedPairs.magnitude Vpair
S=delta*i*c*c
```

There is NO assumption that q−F, rank, tau, c*T−rank, or V is positive.
Do not substitute truncated subtraction for any signed subexpression here.
The first literal product `ell*(ell+k)` is exactly
`(E*Y)*(E*Y+1)*k*k`, since `ell=E*k*Y`.

The canonical five factor pairs, in the ORIGINAL multiplication order, are

```
P = (t*t,                  (E*Y)*(E*Y+1)*k*k)
Q = (d*d,                  delta*c*c)
U = (S*S*vabs*vabs+y*y,     S*S*y*y)
W = ((K+w)*q+q,            (K+w)*(F+alpha)+F+z*B)
Z = (f*f,                  delta*(i*c*c)*(i*c*c))
```

The literal fifth factor is `delta*Z`, since its literal S is
`i*delta*c^2`. The literal whole expression is therefore equivalent to
`scale delta (product5 P Q U W Z) - natural delta` as a signed pair.
This identity is derived from the ACTUAL expression evaluator, not a
hypothesis. A positive zero supplies
`Equivalent (scale delta (product5 P Q U W Z)) (natural delta)`.

Required small local algebra helpers: pair addition and subtraction
congruence, square-to-magnitude equivalence, and magnitude invariance under
cross-sum equivalence/common diagonal addition. These follow by the two
order cases and justified `tsub_add_cancel_of_le`, or cancellation/ring.
No Grothendieck completion, internal integers, sign oracle, or external
integer semantic theorem is needed. In particular, the existing
`Expr.eval_splitNatural` and its standard-Nat integer specialization are
NOT the internal soundness proof.

A structural `pairEval e v := (e.splitNatural.1.evalSemiring v,
 e.splitNatural.2.evalSemiring v)` lemma gives actual add/sub/multiply
operations and natural-constant leaves. Prove and rewrite each literal cut
separately using `Equivalent` congruence, preserving opaque ports. This
avoids expanding the entire large expression in a monolithic ring goal.
All four formal ports must be rebound, including the last port exactly
once as `highPort+beta`; do not shift it again.

## Extraction and subsequent natural subtraction

The discriminant is positive and equals `a^2+4*a+3` by ring. The first
parameter `E*Y` is at least2 from q≥2 and positive w,s. Apply the actual
accepted exclusions:

* `consecutive_ne_negative (E*Y) t k` excludes P=−1;
* `main_ne_negative a d c` excludes Q=−1;
* `square_aux_ne_negative S vabs y` excludes U=−1;
* `strong_ne_negative a f i c` excludes Z=−1.

`scaled_product5_positive` derives P=Q=U=Z=1 AND W=1. No separate
transport premise or exclusion of W=−1 is supplied. W=1 is precisely the
first additive equation, after `B=q-1`.

Only now invoke `scalar_window`: it derives `0<q-F-alpha`, `24≤R`,
and `R+2<E`. The gap implies `F+alpha<q`, so `F≤q` and actual subtraction
laws give `Rplus=Rminus+R`. With positive N,k and E>R+2, `E*N+k>R`;
thus `Tpair.1=Tpair.2+tau`, and its magnitude really is the natural tau.
For V, no sign choice is made: after removing the common `f*f*Rminus`
diagonal, its magnitude is exactly u above. Hence the extracted P,Q,U,Z
units become the remaining four additive equations, with the same v and
rank. This ordering avoids circular use of a scalar/window/source package.

## Actual current constant bounds inside this narrow boundary

Use the existing `CurrentMaskData2011` definitions, not the enormous
closed decimal values or a supplied certificate. `radix=2^47`,
`beta=radix^2011-1`, and the exact maintained width is47*2011=94517.

1. radix≥16 and radix>1 follow from elementary powers; derive beta≥15
   (and beta>0) without reducing the 94,517-bit constant.
2. `0∈lowSupport` by its existing irreducible-definition equation. The
   j=0 term gives `1≤supportValue radix lowSupport`. The literal mask
   definition with b=2 then gives `lowPort<beta` by natural subtraction.
3. The existing highPrefix has length1006; all its digits are <radix.
   `Nat.ofDigits_append_replicate_zero` and
   `Nat.ofDigits_lt_base_pow_length`, BOTH already in imported Digits.Defs,
   give `highPort<radix^1006`. Since radix≥2,
   `2*radix^1006≤radix^1007≤radix^2011`; thus `highPort<beta`.
   Therefore `highPort+beta<2*beta`.

These are ordinary fixed-Nat inequalities cast into every internal model
using its ordered-semiring numeral laws. The beta≥15 proof is exposed as
useful data, but no power-recovery theorem is newly imported or claimed.
K is a natural coefficient already supplied by the exact kernel data; no
additional property of K or tile sorting is used in these bounds.

## Cache, source pins, and limitations

The companion audit constructs the exact reachable union from the accepted
109-module FirstIndex inventory and the source-authenticated narrow syntax
replay, plus accepted NegativeNorms and SignedPairs leaves. The preliminary
DAG count is135 custom modules,95 Foundation,420 custom artifacts,50 actual
external boundary modules (150 primary/companion artifacts),570 provider
artifacts, zero refresh. The generated inventory is authoritative after
rehashing and checks all overlaps, headers including implicit Init, exact
first-provider mappings and package identity. No overlay is made.

Select the accepted ROOT NegativeNorms provider `tiuhx55b`, the independently
replayed SignedPairs peer provider `f4gz2l0f` selected by ROOT, accepted ROOT
FirstIndex `obnhr4v8`, and accepted narrow ROOT syntax provider `0kiizsdx`.
The latter's five data/syntax objects are fresh independently accepted
objects; its other dependencies are authenticated exact-source cache reuse,
not newly replayed here. Additional external names remain explicit package
boundaries; no claim of rebuilding or rechecking their full transitive
source closures is made. Compiler remains4.32, M6000/j1/async=false,
512MiB reserve, two new leaves only if ROOT approves the proposal.

Critical source pins are in the audit, including FirstIndex
`86e3a3698a1a78e713e80d876f8ccee0067dd8900854dcf6958cbe78abf96631`,
NegativeNorms `33d86c09729bda75824591bf840e67ae13d9bf81ed09a5d0f46d2232cc1a63a6`,
SignedPairs `802f596f97526763820fb8bb4cd0f6619b2544eae7039577bc9f37bcb6d435a2`,
and literal syntax `744ed9b68cc2b9d94a8df0d19f5337afb1574ca2ec254dbef66fa11031d2ee7d`.

Focused checks should retain arbitrary nonstandard tuples, exercise signed
rank/V and positiveShift structural lemmas, print axioms of the actual
current-zero endpoint, and explicitly bind its five conclusions to the
existing maintained-index input shape. No desired index, power, source
validity, transport or norm appears as a public premise. Actual literal
binding is part of this pair; whole equation-to-machine/consistency,
cofinal simultaneous witnesses and the ultimate PA/HA results remain later.
