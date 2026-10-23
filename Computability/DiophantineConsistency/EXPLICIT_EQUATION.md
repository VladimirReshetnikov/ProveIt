# A closed executable equation for ZFC consistency

The constructed equation is

```lean
ExplicitZFC.expression.eval (fun i => (u i : ℤ)) = 0
```

where `u : Fin 9 → ℕ`. Its coefficients are fixed integers. There are no
input parameters, consistency assumptions, supplied representations, or
compiler-correctness hypotheses in the final theorem:

```lean
ExplicitZFC.noNaturalZero_iff_conZFC :
  (¬ HasNaturalZero ExplicitZFC.polynomial) ↔ ConZFC
```

The exact definitions and proofs are in
[`ExplicitZFC.lean`](Lean/DiophantineConsistency/ExplicitZFC.lean).
`polynomial` is the ordinary `MvPolynomial (Fin 9) ℤ` denoted by the syntax.
`eval_polynomial` proves their values equal at every integer tuple.
`noSyntaxZero_iff_conZFC` states the same correctness theorem directly for
the executable expression. `ConZFC` means precisely
`¬ BProv ZFCax_s [] Form.fBot`, for the repository's actual ZFC axiom predicate.

This is an external Lean theorem about syntactic ZFC consistency. A
derivation of the equivalence inside the object-language ZFC calculus is
still a separate open task. No global simplicity minimum is claimed.

## Fixed coefficient recipe

Every data stage below is an ordinary executable Lean definition.

1. [`DirectEnumerator.program`](DIRECT_PROGRAM.md) supplies a concrete
   scalar primitive-recursive program and a proof that its value is the
   existing `haltingTest`. The test returns one exactly when the literal
   six-register proof enumerator has halted within the supplied bound.
   Its code is constructed directly from arithmetic formulas and bounded
   recursion, without choosing a program from a computability theorem.
2. `ScalarPRCode.Realizes.optimize` preserves every program value while
   deleting redundant instructions. The complete structural graph compiler
   constructs its finite integer residual syntax. Fix output one and move
   its input into the witnesses to represent existence of an accepting bound.
3. Split that integer residual into positive and negative natural
   expressions. Fold constants, delete zero/unit gates, and pack only the
   source witnesses that still occur. Use one natural value per remaining
   gate, those retained natural witnesses, a
   guard equal to one, and the sum of squared quadratic gate residuals.
   This constructs a normalized quartic `Q` with witness count `ν ≥ 1`.
4. Apply the literal Jones index recipe and the proved nine-variable
   reduction. [`ExecutableJones`](COMPILER_JONES.md) computes the index
   directly from finite sparse coefficient sums, emits the coding
   polynomials by their defining finite sums, and fixes the distinguished
   ordinary input to one.

The resulting syntax is a fixed finite object; construction never runs the
unbounded refutation search. The expanded numerical coefficients have not
been printed or materialized as a release payload. Executability here is a
proved finite recipe, with no practical runtime or output-size claim.

## Compact polynomial form

The final arithmetic relation combiner has the particularly short form

```
K = B*(2*D-1),
T = B*n + C - K*(C + V0*V1),
F = (T^2 + K^2*A0 - K^2*V0^2*A1)^2 - 4*T^2*K^2*A0.
```

The equation is `F=0`. These letters are polynomial abbreviations, not
additional unknowns. Their exact computations from the nine inputs are
`ExecutableJones.syntaxVars` and the `NinePolynomial.RingVars` definitions:

```
U=N^2*w, Y=N^2*s, M=R*Y, P=2*M^2*U,
k=R+1+h*(P-1), a=M*(U+1), b'=2*R+1,
W=b*w, c=b'+W+phi, J=4*a-5,
Q=3*W*c-2*(W^2-1), d=(a^2-1)*c^2+1,
E=i*J*d*c^2, f=(a^2-1)*E^2+1,
G=a+f*(c*d+1-a), H=b'+j*c, I=(G^2-1)*H^2+1,
A0=(P^2-1)*k^2+1, A1=d*f*I,
V0=A0^2+2, V1=A1^2+2,
B=(J*f)^2, C=(Q*f+J*(H-c))^2,
Gamma=32*b*(b^5)^(5^nu),
D=Gamma*(k^2-4*(c-k*Y)^2)-8*g*k^2.
```

Here `b,g,h,i,j,w,s,phi,n` are the shifted nine free coordinates used by
`ExecutableJones.syntaxVars` after fixing its input to one. In particular,
with fixed Jones index `z,y`, `b=y+1+u0`, `g=u1+1`, `h=u2+1`, `s=u3+1`,
`w=u4+1`, `phi=u5`, `i=u6+1`, `j=u7+1`, and `n=u8`.
The fixed formulas for `N,R` use the coding sums of `Q` and are spelled out
by `ExecutableJones.syntaxVars` and `NinePolynomial.rankCode`.
[`RefinedPair.value_eq`](Lean/DiophantineConsistency/RefinedPair.lean)
proves that this compact finalizer equals the existing proved Jones
relation-combining polynomial; its correctness is not inferred from sample
evaluations.

## Correctness and validation

The checked equivalences are: the equation has a natural zero iff the
constructed quartic has a natural zero iff its supplied program accepts
some bound iff the actual ZFC syntax has a finite refutation. Negating
this chain gives the consistency theorem. All intermediate arithmetic
graphs include zero inputs, zero bounds, and the relevant zero-divisor
conventions.

Run the standard build and consolidated audits from the repository root:

```sh
lake build DiophantineConsistency
lake env lean Computability/DiophantineConsistency/Lean/checks/ZFCAxioms.lean
lake env lean Computability/DiophantineConsistency/Lean/checks/CompilerAxioms.lean
```

The closed correctness theorems audit with only `propext`, `Classical.choice`,
and `Quot.sound`. The concrete coefficient data are supplied by executable
constructors; the mathematical proof layer uses classical library theorems.
Further work targets additional code sharing, direct quadratic
coding, and the separate object-language ZFC proof.
