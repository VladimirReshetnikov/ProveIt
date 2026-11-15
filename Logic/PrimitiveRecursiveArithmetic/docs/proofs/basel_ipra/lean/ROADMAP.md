# Lean formalization roadmap and exact status

## Status

The accompanying paper supplies a human-readable finite arithmetic proof.
The Lean files here are **uncompiled specifications and a formalization
outline**, not a completed Lean proof of the Basel theorem. This environment
did not have an available Lean installation. No source file uses `sorry` or
declares an axiom. The conditional bridge theorem takes an internal iPRA proof
as an argument; it does not manufacture one.

`BaselSpec.lean` defines the actual natural-number computations, the exact
finite theorem, and named missing proof obligations. The record
`FiniteProofObligations` has no supplied inhabitant. `ObjectTheoryTarget.lean`
uses the actual API of the repository's deep embedding and specifies the
eventual object-theory proof. `CompiledBaselProgram` also has no supplied
inhabitant: compiling and certifying the program is an explicit remaining
task. Compilation itself may require minor syntax adjustments because these
files have not been run through Lean.

## Pinned repository and verified APIs

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspected commit: `b03925cccc76d55b9dc2a00864a5e0544b64aa7f`.

Toolchain: `leanprover/lean4:v4.32.0`.

Library sources:
`Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/`.

Namespace: `LeanProofs.ConciseIPRA`.

Relevant modules and APIs:

| File | API used or available |
| --- | --- |
| `PR.lean` | `PR`, `PTm`, `PRAAx`, `PRA.qfInd`, `PRA.comp`, `PRA.precZero`, `PRA.precSucc` |
| `Deduction.lean` | `Prf`, `Prf.eqSubst`, `Prf.allI`, `Prf.subst`, `Prf.weaken`, `Prf.trans` |
| `BiInterpretation.lean` | `teq_iff_pra`, `pra_iff_teq` |
| `NativeBiInterpretation.lean` | `pra_iff_native`, `NFm.ofPRA`, `native_iff_pra` |
| `Lindenbaum.lean` | quotient `Q Γ`, certified internal equation induction `Q.eqInd`, `Q.exact` |
| `TeqArith.lean` | internal selector and addition; `AddCommMonoid (Q Γ)` |
| `TeqOrder.lean` | truncated subtraction, order witnesses, powers of two |
| `TeqPair.lean` | pairing and projections |
| `TeqRec.lean` | primitive recursion simulated by a scalar iterator |
| `TeqReflect.lean` | `chi_iff`, `Teq.qfInd`: QF formulas reflected to equations |

These are object-theory APIs. A Lean theorem only about `Real.pi`, `tsum`, or
the standard natural-number interpretation would not meet the required final
certification boundary.

## 1. Representation and exact target

A rational is represented by a triple `(p,m,d)` with `d > 0`, meaning
`(p-m)/d`. There is no gcd normalization, rational quotient, or sign search.
Addition, subtraction and multiplication are the explicit natural polynomial
formulas in `BaselSpec.lean`. The denominator of every constructed value is
positive, proved by QF induction on its construction counter.

For `r(k)=2k+7`, `N(k)=2^r(k)`, define

```
A(N) = sum(j < N) (-1)^j / (2j+1)
S(n) = sum(1 <= j <= n) 1 / j^2
p(k) = 4 A(N(k))
q(k,n) = 6 S(n) - p(k)^2.
```

For the intermediate raw-fraction version, if `q(k,n)` is represented by
`(P,M,D)`, the matrix is

```
N(k) <= n ->
  (P * 2^k <= M * 2^k + D) /\
  (M * 2^k <= P * 2^k + D).
```

The recommended final compiler target is even more direct. Set

```
D(n) = (2n)!
C(k,n) = sum(j < N(k)/2)
  (D(n)/(4j+1) dotminus D(n)/(4j+3))
B(n) = sum(1 <= j <= n) (D(n)/j)^2
Delta(a,b) = (a dotminus b) + (b dotminus a).
```

All divisions here are natural division. Under `n>=N(k)`, each denominator
divides `D(n)`, so `C(k,n)/D(n)=A(N(k))` and `B(n)/D(n)^2=S(n)`.
The cutoff is even, and each paired numerator difference is nonnegative.
Thus the exact final matrix is

```
N(k) <= n -> 2^k * Delta(6*B(n), 16*C(k,n)^2) <= D(n)^2.
```

`Spec.BaselStatement` is this statement; `FractionBaselStatement` records the
raw-fraction counterpart. Natural order is compiled using truncated
subtraction, so the matrix is quantifier-free in the language with all PR
symbols. `checkBasel k n` returns zero exactly when the final matrix holds;
at a false antecedent it returns zero. Its compiled symbol has arity two.
`baselFormula c` is literally `forall k, forall n, c(k,n)=0`.

The program contains no arbitrary function argument. The specification helper
`Fraction.sum` is specialized to each fixed summand before compilation. Finite
tuples and loop states are encoded using an explicit primitive recursive
pairing; one may reuse the scalar-theory pairing and iterator compiler.

## 2. Arithmetic foundation and compiler

Implement or import internal proofs for addition, multiplication, monus,
bounded division, factorial, parity, powers, pairing and coordinate
extraction. Natural division by a positive `d` can be implemented by a loop
bounded by its numerator `a`; for example, scan `q<=a` and retain the last
`q` with `d*q<=a`. Every call here has a positive displayed divisor.
A convenient route extends
the existing Lindenbaum quotient `Q Γ` by multiplication and signed fraction
operations; a `CommSemiring` instance whose laws were proved internally then
permits `ring`-style normalization while retaining the object-theory boundary.
Alternatively, work directly with `PTm` and `PRA.qfInd`.

For each fixed recursive program, construct a syntax tree in `PR` using only
zero, successor, projections, composition and primitive recursion. Prove its
two recursion equations internally. Prove externally that `evalPR` of that
syntax tree agrees with the executable specification. Both are needed:
external semantic agreement alone does not establish internal correctness.

Raw fractions can grow very large, but size is irrelevant to primitive
recursiveness. For bounded-quantifier encodings one can use a deliberately
generous primitive recursive bound. Fix a number `C >= 2` greater than all
input coordinates, indices and summand numerators/denominators. Let
`B(0)=C`, `B(t+1)=8*(B(t)+C+1)^2`. After `t` elementary coordinate arithmetic
operations every coordinate is at most `B(t)`, provided the actual operation
count is at most `t`. Supply this operation count from each fixed loop's
syntax, by primitive recursion. No efficient bound is required.

## 3. General finite lemmas: explicit QF invariants

The following are the only forms of induction required. Any finite family of
equalities or inequalities in an invariant is combined into one Boolean test,
with value zero for success. A bounded universal quantifier is implemented by
a loop accumulating the conjunction of its instances. Do not use induction
directly on an invariant containing an unbounded `forall`.

### QF-A: rational operations and denominator positivity

At stage `t`, the accumulated triple has positive denominator and represents
the intended finite expression. The representation assertion is a
cross-multiplied equality between two explicit triples, not a quantified
statement about rational numbers. Positivity and congruence follow from
natural arithmetic. Every division is by a displayed positive natural.

### QF-B: reindexing finite sums

For `sum` recurrence and rectangular interchange use equality of partial
accumulators. For the triangular reindexing hold the outer cutoff `N` fixed.
After diagonal `d`, the accumulator contains exactly the pairs
`i+j+1 <= d`, and its alternative accumulator is the sum of the first `d`
closed-form diagonal contributions. Each new diagonal has a finite inner
loop with invariant the partial-fraction identity accumulated for `i<t`.

For a fixed diagonal length `d`, use

```
1 / ((2i+1)(2d-2i-1))
  = (1/(2i+1) + 1/(2d-2i-1)) / (2d),  0 <= i < d.
```

Summing gives `H_d/d`. The triangle contains the diagonals `1 <= d < N`.
All inverse signs are handled by the positive denominator hypotheses and
cross-multiplication.

For grouping the square by index difference, the state after `d` consists of
the diagonal and both orientations of differences `1,...,d`. The next
difference uses

```
2 / ((2i+1)(2i+2d+1))
  = (1/(2i+1) - 1/(2i+2d+1)) / d.
```

Its inner-loop invariant telescopes the first `t` terms. The terminal identity
is `A_N^2 = O_N - T_N + E_N`. No variable-length permutation is treated as
an unexplained axiom.

### QF-C: alternating decreasing sequences

For a bounded nonnegative decreasing sequence `a_0,...,a_{L-1}`, let `s_t`
be its alternating partial sum of length `t` and process two terms at a
time. The invariant, when the displayed indices exist, is
`0 <= s_(2q) <= s_(2q+1) <= a_0`, together with the partial-sum recursion.
The next even sum increases because `a_(2q)>=a_(2q+1)`; the next odd sum
decreases because `a_(2q+1)>=a_(2q+2)`; the difference between the new
adjacent sums is nonnegative. These are finite rational inequalities using
the supplied bounded monotonicity test. Treat both parities of `L`, and
the empty sequence, explicitly.

For each row of `D_N`, keep `N` and the row index `i<N` as parameters. Its
tail starts at `j=N-1-i`, with first magnitude
`1/((2i+1)(2N-2i-1))`. QF-C bounds that entire alternating row by this
magnitude. Accumulating the row bounds and using QF-B gives
`|D_N| <= H_N/N`.

### QF-D: alternating increasing sequences

Reverse a finite nonnegative increasing sequence and apply QF-C; a reversal
changes at most the overall sign. Its alternating sum has absolute value at
most its final magnitude. For

```
b_d = (H_N - H_(N-d))/d,  1 <= d < N,
```

the monotonicity step is the cross-multiplied inequality

```
sum(last d reciprocal odd terms) <= d / (2(N-d-1)+1).
```

Each of the `d` terms is at most the newly adjoined term. This is a bounded
sum invariant. At `N>=2`, `b_(N-1)=(H_N-1)/(N-1) <= H_N/N`, because
`H_N<=N`, itself a sum of `N` terms each at most one. Handle `N=1` separately;
then `E_N=0`. This proves `|E_N| <= H_N/N` without an unbounded sign choice.

### QF-E: telescoping tails and dyadic blocks

The telescoping invariant after `t` terms is the cross-multiplied form of

```
sum(j=N+1,...,N+t) (1/(j-1) - 1/j) = 1/N - 1/(N+t).
```

Since `1/j^2 <= 1/(j-1)-1/j`, this bounds ordinary tails. For the block
`N+1,...,2N`, also use `1/j^2 >= 1/(4N^2)` term by term. Thus

```
1/(4N) <= S_(2N)-S_N <= 1/(2N),
0 <= S_n-S_N <= 1/N                     (n>=N).
```

Odd/even reindexing gives `4O_N=4S_(2N)-S_N` by a sum invariant. Hence
`|O_N-3S_n/4| <= 1/(2N)` for `n>=N`.

For the harmonic estimate use induction on `r`, with QF invariant
`2H_(2^r) <= r+2`. The block from `2^r` to `2^(r+1)-1` has `2^r` terms,
each at most `1/(2*2^r)`, so the increment is at most `1/2`.

### QF-F: final precision budget

Combine `D+E=2A_N^2-O_N`, the two error bounds, and QF-E to obtain

```
|6S_n - 16A_N^2| <= (16H_N+4)/N          (n>=N>=1),
|6S_n - 16A_(2^r)^2| <= (8r+20)/2^r      (n>=2^r).
```

Use QF induction on `k` for `16k+76 <= 128*2^k`. The base is `76<=128`.
For the step, `16(k+1)+76 = (16k+76)+16 <= 2(16k+76)`; combine with the
induction hypothesis. Substitute `r=2k+7` and cross-multiply positive powers
of two to obtain `FractionBaselStatement`.

Finally, certify the common-denominator implementation: QF induction proves
factorial positivity and `j | (2n)!` for `1<=j<=2n`, with explicit quotient
witnesses (or bounded division). An induction on the paired odd summands
proves `C/D=A_N`, and an induction on the square reciprocal summands proves
`B/D^2=S_n`. The integer absolute-difference test then gives exactly the
recommended `checkBasel` target. These representation lemmas are named in
`FiniteProofObligations`; they are remaining proof work, not supplied axioms.

## 4. Deliver the internal theorem, then transfer

The eventual final deliverables are a concrete `CompiledBaselProgram` and

```lean
theorem basel_ipra : InternalBaselProof compiledBaselProgram := ...
```

Here the ellipsis is roadmap notation, not Lean source supplied as a proof.
All induction in the actual proof must go through `PRA.qfInd`, or through
the certified scalar-theory equation induction followed by `teq_iff_pra`.
Calling unrestricted Lean `Nat.rec` to construct a finite syntax tree is
fine; using unrestricted Lean induction to assert object arithmetic without
a derivation certificate is not.

`native_of_internal` then transfers the proof to `NPrf` using the existing
`pra_iff_native`. No Busy Beaver or Diophantine consistency theorem is needed.

## 5. Build and audit when implementation is completed

Place these files in a new Lake library under the repository, add that source
directory and depend on the existing `ConciseIPRA` library. Run `lake env lean`
on each file (or the corresponding `lake build` target) at the pinned
toolchain. This package does not claim such a run has occurred.

For the eventual completed proof inspect `#print axioms basel_ipra`, and
inspect that the statement is `Prf PRAAx [] ...`, not merely `Spec.BaselStatement`.
A metatheoretic dependency on Lean's quotient soundness or propositional
extensionality does not introduce such a rule into the deeply embedded
object theory. The relevant proof object must nevertheless have no `sorryAx`,
no custom axioms standing in for the finite lemmas, and no extra arithmetic
axiom family added to `PRAAx`.

The separate identification of the rational `p(k)` with the usual real pi
can be formalized externally by the alternating arctangent series. It is an
interpretation bridge, not a substitute for the internal finite theorem.
