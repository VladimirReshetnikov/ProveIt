# Independent review of the round21 twelve-integer norm

**Verdict:** PASS for the supplied ordinary mathematical reduction and literal norm, with the mandatory comparison qualification below. Reviewed `roots/PROOF.md` (hash at review `7959553286c77aa3d65c086f53d83ab6bd73bad417fc98e70e497a962c7afac6`) and literal DAG `integer12_degree512.json` SHA256 `7ef6b5f7094ce2bbaf5a0cfbd73754d9abd02156cb7dfa5774942db532e389e9`.

This is a separate AI-assisted review, not external human endorsement or a new proof-assistant theorem.

## Actual checks

1. `check_roots12_norm.py` imports no producer module. It treats the five norm-input cuts as independent squares, evaluates the **actual emitted DAG tail**, independently multiplies all sixteen signed linear factors, and compares all495 collected coefficients. They agree. The norm is homogeneous degree8 in the five squared inputs and monic in the auxiliary input to power8. Receipt:`ROOTS12_NORM_CHECK.json`.
2. All161 emitted nodes are live; exactly132 are arithmetic:82multiplications,25additions,25subtractions. All12 inputs and6 coefficient leaves are retained by the literal graph.
3. Recursive operation fingerprints compare all31 common front registers with the already checked round20 thirteen-variable DAG. They agree exactly up to commutative operand ordering. Receipt:`ROOTS12_FRONT_CHECK.json`. This covers the actual shared front, not merely equal names.
4. Actual gatewise degree upper bounds of `(s,aa,bb,cc,dd)` are `(48,42,48,46,64)`. The auxiliary64-degree input is uniquely maximal. Its leading form is
   `dd0=2^12*3^4*q0^6*a0^10*r^6*c^12*R0^2`,
   with `q0=6beta*j`, `a0=12q0*w*v`, `R0=-q0^3(12wC-q0z)`.
   It is nonzero for the actual positive fixed beta. Homogeneity and the monic dd^8 term prove exact degree512, without sampled-line inference. Setting C=0 isolates coefficient `2^448*3^304*beta^192` at `j^192 w^80 v^80 r^48 c^96 z^16`.

## Full mathematical audit

### Nonzero divisions are proved before use

The inherited affine residues give even nonzeroq, `|X|>=8`, and `a=(X+1)Y` either0 or of magnitude at least7. Hence `Delta=(a+2)^2−1>=3`, H odd/nonzero and U nonzero. The identities `Q=(Delta I)^2` and `I integer` giveQ0 orQ>=9, so `delta=Q−1` never0. NeitherCy norG can vanish. Dt andFs are positive. These facts hold on every input, not only zeros.

### Four-root separation is sound over signed rational square classes

The authentic beta is1mod3; the printed affine chart forces Delta0mod3, Fs=Dt=1mod3, Q0mod3 and delta=Cy=−1mod3. Thus squared valuations of `sqrt(Fs),3sqrt(Dt),9sqrt(Cy/delta),27sqrt(G)` are0,2,4,and at least6.

For a common signed squarefree classd, the first three roots have v3(d)=0 and rational coefficient valuations0,1,2 respectively. A guard coefficient in the same class has valuation at least3. Unique least valuation prevents cancellation in every irrational group, including a negative class containing two imaginary radicals. A group containing only the guard cannot cancel. The rational termrho participates only in class1; the argument must not claim class1 itself vanishes without that term. The supplied proof's intended conclusion—every radical is rational—is correct. It does not presume auxiliary integrality or distinct generic squareclasses.

### Rational Pell descent is valid and handles all boundary cases

If `Qu²−(Q−1)t²=1`, integerQ>1, integeru, rationalt, the reduced denominator m satisfiesm²|(Q−1). For |u|>1 choose positive signs; `u<t<Qu/(Q−1)`. The norm-preserving transformation
`u'=(2Q−1)u−2(Q−1)t`, `t'=(2Q−1)t−2Qu`
has integeru', `0<|u'|<u`, and preserves reduced denominatorm because `2Q−1≡1modm`. Descent terminates at|u|1, where|t|1. Thereforet integer. For actualQ0, `Cy/delta=1` directly gives integer t=±1. No premature nonzero-c or nonzero-I assumption is required.

### Total maps on every zero, not just canonical witnesses

From a new zero obtain signed integers f,tau,t,g with their stated squares and
`rho=f+3tau+9t+27g`. Restore old15 coordinates by
`f_old=f`, `y_old=t−V`, `p3=(g−1)/2`,
`n_old=n−k−f−tau−9t−27g`.
The guard square makesg odd. The first old residual follows from
`Z_old/U+2L+k=2tau`; strong and auxiliary residuals are exact substitutions. The guard identity is `(G−1)/4=budget−p1²−p2²−1`.

Conversely, an old zero supplies integer
`tau=(Z_old/U+2L+k)/2`, `g=2p3+1`, `t=V_old+y_old`;
set `n_new=n_old+k+f_old+tau+9t+27g`.
Then the required norm factor vanishes. Rational-square integrality and evenness justify the tau division. Every other common coordinate is retained. The maps establish equivalence of zero existence; no claim of a single polynomial bijection after deleting three root witnesses is needed.

The supplied norm has exact scale `delta^8 U^16`; both factors are nonzero. Its zero condition is therefore precisely the required product-zero condition. There is no hidden variable division in the final polynomial.

## Mandatory comparison qualification

Current fixed12 baselines are500degree/139ops (source121) and1084/123(source113), not merely the obsolete2400/215 and2912/209 constructions. New512/132 is a fixed12 degree/cost tradeoff, not first12 or lowest12degree. Across variable counts it is dominated by existing11/398/121 and11/328/130. See `BASELINE.md` and `TWELVE_BASELINES.json`. The proof draft's opening historical comparison should be updated accordingly before release.

## Scope and remaining release checks

The six fixed ports and inherited calibration are unchanged; the inherited round20 roots packet was replayed normally and under-O in this audit. This review does not reprove the entire native/compiler/refutation ancestry or produce a new Lean/Rocq/object-ZFC derivation. The producing agent's own full new register checker, mutation controls, coefficient reconstruction and sealed release inventory should still run; their success must not be inferred from this independent norm/semantic review alone.
