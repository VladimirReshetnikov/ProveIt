# Reusing the beta-row majorant as the shared factorial bound

Ordinary arithmetic research. Lean formalization remains paused.

This sibling preserves the frozen `shared-crt-prime-lift` candidate and
its integer companion. It changes the actual direct compiler's factorial
argument from `E(t,z,u)+F(t,z,u)+t` to `E(t,z,u)+F(t,z,u)`. The new bound
is justified by a beta remainder row and an already retained endpoint
equation, before any CRT or positive-power theorem is invoked.

The emitted equations are over **nonnegative integers**. They retain the
same numerical C222 predicate, sealed refutation target, and named
C222-to-ZF/constructible-choice calibration. No native coefficient tuple
is introduced. This is an ordinary proof formalizable in ZFC, not a new
Lean development or an encoded internal object-ZFC derivation.

## 1. The prime-lift lemma with an arbitrary sufficient height

Let `E,F` be fixed polynomials with nonnegative coefficients in an index,
external natural parameters `z`, and finitely many local coordinates.
Fix `N,z` and coordinate bounds `u_j`. Choose a natural `H` satisfying

```
H >= N,  H >= E(N,z,u),  H >= F(N,z,u).
```

Put `T=H!`, `d_i=1+(i+1)T`, and `B=product(i<N,d_i)`. Then the bounded
row family is equivalent to the prime-lift certificate

```
for every i<N there exists w with w_j<=u_j and E(i,z,w)=F(i,z,w)

iff there exist natural C,A_j such that
 B | binom(A_j,u_j+1) for each j,
 B | 1+(C+1)T,
 E(C,z,A)=F(C,z,A) modulo B.
```

The encoded columns may additionally be required to be positive, or even
greater than their local witness bounds. No factorial coprimality
assumption is needed. The full argument is retained in
`PRIME_LIFT_PROOF.md`; the following records why its proof uses precisely
the three sufficient-height inequalities above.

For soundness, if `i<N`, any prime `p|d_i` satisfies `p>H` because it
does not divide `H!`. The binomial range condition implies that `p`
divides the falling numerator, so `A_j=w_j mod p` for some `w_j<=u_j`.
No cancellation of the factorial and no inequality `p>u_j` is used.
The index condition gives `C=i mod p`. The decoded evaluations are each
at most their corresponding value at `(N,z,u)`, hence at most `H<p`.
Their congruence therefore implies equality.

For completeness, `H>=N` makes the `d_i` pairwise coprime. For column
`j`, multiply each `d_i` by the complete prime-supported part of
`(u_j+1)!` at the primes dividing `d_i`. The strengthened moduli remain
pairwise coprime. CRT gives a column congruent to every chosen bounded
witness modulo its strengthened modulus. A sufficiently large multiple
of their product makes that column positive without changing any of the
congruences. The falling numerator is divisible by the original modulus
times its supported factorial part. Cancelling the supported part as an
integer factor, followed by cancellation of the coprime remaining part
modulo `d_i`, proves `d_i|binom(A_j,u_j+1)`. Combine the original
pairwise coprime moduli. Construct `C` independently with `C=i mod d_i`.
These congruences also give the index and evaluation conditions.

When `N=0`, `B=1`; the row family is vacuous and arbitrary positive
columns and any `C` suffice. `H=0` is permitted in this abstract empty
case. A positive-power specialization still needs its own input-positivity
proof; it is supplied separately below for the concrete source.

## 2. The actual literal split contains the needed square

Keep the received outer variables `t,x,y,m,M0`, with

```
t=t0+1,  m=m0+1.
```

The same three local formula labels are bounded by `m`, and the other ten
local coordinates by an independent natural `U`. Thus
`u=(m,m,m,U,...,U)`. Let `E,F` be the pair computed by the actual pinned
`source_pair_calculus` at index `t` with these bounds. It is essential
here to use the literal pair, rather than replace it by an arbitrary
different positive/negative split of the same signed polynomial.

For a local index `i`, the beta remainder constraint is formed from

```
d(i)=1+(i+1)y,
(left,right)=(d(i), S+r+1).
```

The literal implementation does **not** cancel the constants in this
pair. Its pair-square contributes

```
positive part: d(i)^2+(S+r+1)^2,
negative part: 2d(i)(S+r+1).
```

The positive contribution is added to the other nonnegative pieces of
`E`. Therefore, for every natural assignment to the bound arithmetic,

```
D=1+(t+1)y,  E(t,z,u)>=D^2,  F(t,z,u)>=0.
```

`majorant_audit.py` reconstructs the actual factorial argument and emits
an all-addition path of length four from its `E` node to the `D^2` node.
Every unselected sibling is a natural gate value. The audit also checks
that `D^2` is exactly the multiplication gate `D*D` and that the bound's
dependency cone contains only the outer natural coordinates and `U`.
No encoded column, encoded index, power output, or CRT witness occurs in
this bound.

Set

```
H=E(t,z,u)+F(t,z,u).
```

The two evaluation inequalities required by the general lemma are
immediate. Moreover `D>=1`, so `H>=D^2>=1` before interpreting any
factorial or positive-power graph, even off the source zero set.

## 3. The endpoint supplies the index inequality in the right order

One retained endpoint row is precisely

```
y=M0+r0+2.
```

Here `M0` and `r0` are natural coordinates, so this row implies `y>=2`.
The exact audit flattens only the addition gates in this row and checks
its coefficients; it does not use a power graph, a binomial graph, a
factorial graph, or a bound on the later CRT encoding.

Consequently, at every complete natural zero, and also at every proposed
outer certificate satisfying the endpoints,

```
D=1+(t+1)y >= 2t+3,
H>=D^2 >= t.
```

This proves the remaining hypothesis `H>=N` for `N=t`. There is no
circular dependency: first use the ordinary addition/multiplication
definitions and the endpoint row to establish `H>=t`; next interpret
the arithmetic macro graphs and apply the prime-lift lemma.

The statement `H>=t` is not claimed for arbitrary assignments that
violate the endpoints. For example, set every free input other than
`t0` to zero. Then `y=0`, so the local source's index disappears from
the literal `E,F` arithmetic and `H` is constant in `t0`. Choosing
`t0=H` gives `t=H+1>H`. The audit verifies this counterexample exactly
without printing its large constant. This separates unconditional
`H>=1` from endpoint-dependent `H>=t`.

An expanded-source split could cancel the constants in the beta row and
have a different majorant. That alternative is not used here. Even then
the endpoint would give a sufficient index bound from `((t+1)y)^2`, but
the positive-factorial argument would require a separate proof. The
delivered candidate and certificate bind the actual unchanged literal
calculus throughout.

## 4. Soundness and completeness of the new source

At a zero of the new sum of residual squares, every residual vanishes.
The nonnegative affine gates have their unique natural restorations;
the independent checker verifies this for the complete exported row
multiset. The actual gate-path identity proves `H>=1`, and the endpoint
proves `H>=t` as above.

All 55 positive-power calls retain their ordinary static input-positivity
induction. The first factorial argument is positive because `H>=1`;
the other is `t>=1`. The range-binomial upper arguments are
`A_j=alpha_j+1>0`, and their lower arguments `u_j+1` are positive even
when `U=0`. All sixteen binomial graphs and both factorial graphs
therefore retain the same licensed semantics. Interpreting them yields
the exact new `T=H!`, product `B`, and range/index/evaluation conditions.
The general prime-lift lemma recovers every bounded source row.
The unchanged numerical C222 flow/calibration then supplies the same
refutation predicate as for the received source.

Conversely, choose a finite calibrated C222 proof and its outer carrier,
accumulator and beta witnesses, then choose `U` at least the finite
maximum of the ten private per-row coordinates. Keep the same endpoints.
Compute the new `E,F,H`; the preceding argument gives all three
sufficient-height inequalities. The prime-supported CRT construction
gives positive encoded columns and an index for these newly computed
moduli. Choose witnesses for the unchanged arithmetic graphs and all
addition/multiplication gates. Their arguments are positive as proved
above. This yields a complete natural zero of the new equation.

The old CRT encodings need not be preserved: changing `H` changes `T`,
the product `B`, and the constructed columns. Existence is preserved by
reconstructing them. No direct substitution of the old encoded values
is claimed.

## 5. Exact finite construction and limits

The generator authenticates the complete original shared-certificates
ZIP, SHA256
`61582dab90e880049e61ff1a5c49386747cd063de15e18411a20f327b9559ba1`.
It makes only two original compiler changes: private bounds `m+U` become
`U`, and the factorial argument `E+F+t+m+U+1` becomes `E+F`. All source
predicates, literal calculus formulas, arithmetic graph constructors,
auditors and exporter are unchanged. Both complete ordinary quartics
are materialized, not just counted by an abstract cost recurrence.

| Variant | Natural variables | Quadratic rows | Quartic terms | Height |
|---|---:|---:|---:|---:|
| Frozen prime-lift affine | 3,609 | 2,949 | 15,752 | 127,285,349 |
| **Beta-majorant affine** | **3,603** | **2,943** | **15,670** | **127,285,252** |
| Frozen prime-lift retained | 6,180 | 5,520 | 17,421 | 1,992 |
| **Beta-majorant retained** | **6,179** | **5,519** | **17,417** | **1,992** |

All four polynomials in the table have exact degree four. The received
pre-prime-lift variants had 3,614 and 6,183 variables, respectively.
The extra affine savings beyond the single removed retained gate come
from the unchanged exporter's support cap and newly eligible affine
substitutions. Exact whole-row restoration, rather than this explanation,
certifies the new default equation.

These are local improvements of the named received constructions, not
claims of global minimality. The no-zero/refutation equivalence uses the
same explicitly named ordinary C222-to-ZF and ZF-to-ZFC calibration.
This artifact does not prove absence of zeros, consistency of ZFC, or a
new fully checked derivation inside the encoded object-ZFC calculus.
