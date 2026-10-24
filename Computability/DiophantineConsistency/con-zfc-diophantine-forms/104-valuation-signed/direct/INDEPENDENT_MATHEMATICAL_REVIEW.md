# Independent review: the 1,190-integer direct quartic

**Review date:** 2026-10-24.  
**Reviewer:** a separate assistant reviewer from the author of the guard-selection and projection builder.  
**Verdict:** the two new transformations pass ordinary mathematical review and independent exact finite verification. Their composition preserves existence of a zero of the frozen synchronized 522-natural-coordinate source. Consequently they preserve that source's inherited equivalence with ZFC refutability.

This review concerns the frozen artifact at `research_input/alternative/synchronized_guards` in the working package. The principal checked output is `output/equation.json`. Its SHA-256 is

```
ecedebee7a8147c89f2401a658f7d7efad27952681de417dbc55af3e63ccb083
```

The independently reproduced metrics are:

| Stage | Domain | Variables | Quadratic residuals | Expanded monomials | Exact degree | Coefficient height |
|---|---|---:|---:|---:|---:|---:|
| Frozen synchronized parent | Nonnegative integers | 522 | 400 | 20,225 | 4 | 83,900,628 |
| Selective guards | All integers | 1,224 | 634 | 23,590 | 4 | 83,900,628 |
| Signed monic projection | All integers | **1,190** | **600** | **26,411** | **4** | **83,900,628** |

The maximum absolute coefficient in a residual of the last two stages is 4,556. These are literal counts and coefficients of the supplied complete polynomials, rather than symbolic asymptotic estimates.

## 1. Scope and source identity

The natural parent is the literal `equations/natural522/equation.json` from `docs/incoming/ConZFC_Synchronized_Certificates_2026-10-24.zip` at ProveIt snapshot `85ae4070019efd66ea3e58e9a67d287528094e8b`. Its frozen bytes have SHA-256

```
8b983a7357d16201ac5b7dfa6e12e809692ee26a29383ae84e2af2b891994f48
```

I verified that the guarded input retains the parent's complete 522-variable prefix and complete 400-row prefix byte-for-byte after JSON decoding. No natural arithmetic condition, Pell condition, numerical-calculus instruction, or consistency-calibration row is rewritten by the domain conversion.

The source's ordinary theorem identifies a natural zero with a refutation in the calibrated calculus C222, then uses `KEndpoint.c222_iff_zf_refutation` and `ConstructibleChoice.zf_refutation_iff_zfc_refutation`. Its calibration snapshot is `08200eb10fde2db408c69dffd840d6920a569b1f`, which differs from the comparison repository snapshot above. The new transformations do not alter this logical interface. This review does not independently reproduce the full inherited calculus proof, the transitive Lean dependency closure, or an object-language ZFC derivation. It establishes the new finite polynomial transformations and their ordinary mathematical justification.

## 2. Three-coordinate nonnegativity guard

For every integer x,

\[
x\geq0\quad\Longleftrightarrow\quad
\exists a,b,c\in\mathbb Z:\quad x=a^2+b^2+c(c+1).
\]

The reverse direction follows from the fact that `c(c+1)` is nonnegative for every integer c. For the forward direction, `4x+1` is positive, is not divisible by 4, and is congruent to 1 or 5 modulo 8. Legendre's three-square theorem therefore supplies a representation of `4x+1` as a sum of three integer squares. Reducing modulo 4 shows that exactly one of the three coordinates is odd. Reorder the coordinates, write the odd coordinate as `2c+1` and the two even ones as `2a,2b`, and divide the resulting identity by 4 after subtracting 1.

Thus every literal added residual

\[
x-a^2-b^2-c-c^2
\]

expresses precisely nonnegativity of x, with all four coordinates unrestricted integers. The verifier checks all 234 such guards, their row allocation, and pairwise disjoint fresh auxiliary triples. These guards introduce exactly 702 coordinates. Their existence theorem permits many witnesses; no uniqueness of guard witnesses is claimed or required.

## 3. Why the remaining 288 coordinates need no guards

The inference rule is slightly more general than a monic nonnegative graph rule. Suppose a literal existing row is

\[
kx+R(\mathbf y)=0,\qquad 0\ne k\in\mathbb Z,
\]

and x has no occurrence inside R. Multiplying by k gives

\[
k^2x=P(\mathbf y),\qquad P=-kR.
\]

If P has nonnegative integer coefficients, each monomial is nonnegative whenever every coordinate occurring to an odd exponent is already known to be nonnegative. Coordinates occurring only to even exponents need no sign hypothesis. Hence the row implies `x>=0`, because `k^2>0`.

This is a sign inference, not a division-based reconstruction. It places no requirement that k be a unit and does not introduce a rational coordinate or a divisibility assumption.

The supplied certificate contains 288 ordered applications of this rule. At each step the independent verifier checks the entire original row, the exact positive multiplier `k^2`, all coefficients of `P=-kR`, the absence of x from P, and the exact set of coordinates occurring with odd multiplicity. Every dependency must already be guarded or inferred at an earlier step. The resulting known-nonnegative set is exactly the set of all 522 source coordinates.

The checker also enumerates every eligible target of this scaled literal-row rule from the frozen source. Exactly 234 coordinates cannot be a target of any eligible rule; every such coordinate must be guarded in any certificate using only this rule family. They are exactly the supplied guard set. The count 234 is therefore minimal within this specified syntactic rule family on the unchanged literal source rows. This restricted statement gives no lower bound for methods using polynomial combinations of rows or other nonnegativity arguments.

A useful non-unit example is source row 215:

\[
4A-5-T_{\mathrm{base7}}=0.
\]

The stored implication is

\[
16A=20+4T_{\mathrm{base7}}\geq0.
\]

The coordinate `base7.T` is guarded. This implication makes the separate guard on `shared.A` unnecessary, saving three unrestricted integer coordinates. It is legitimate even though the source relation has coefficient 4 rather than coefficient 1.

To prove the whole conversion, consider an integer zero of the sum of squares of the 634 guarded rows. Every row vanishes. The guard lemma and the ordered implications make every original coordinate nonnegative, so its projection is a natural zero of the unchanged 400-row source. Conversely, every natural source zero extends to an integer guarded zero by choosing the three-square witnesses independently for each of the 234 guards. The inference rows are original rows, so they add no extra condition. This proves existence equivalence in both directions.

## 4. Signed monic coordinate elimination

At each elimination step a current row is exactly

\[
\pm\bigl(x-P(\mathbf y)\bigr)=0,
\qquad P\in\mathbb Z[\mathbf y],
\]

with no x inside P. Deleting x and this row while substituting P for x in every other row induces a bijection between the integer zero sets. Its inverse restores `x=P(y)`. Negative coefficients in P are harmless because this phase takes place entirely over unrestricted integers.

The certificate makes 34 such eliminations: 23 affine and 11 quadratic. The independent checker recomputes every substitution using its own sparse polynomial arithmetic, checks the exact monic pivot up to sign, and verifies that every surviving residual remains of degree at most two after each step. It also verifies all retained-variable and retained-row maps and the complete final literal residual list. No unconstrained free coordinates are removed in this instance.

Restoring the 34 eliminated coordinates in reverse order recovers exactly the guarded system from any final zero. The nonnegativity proof in Section 3 then applies to that recovered system. A final coordinate is not silently assumed nonnegative merely because a metadata label calls it a witness or gate.

## 5. Single-polynomial equivalence and degree

Let the final 600 integer quadratic residuals be `q_0,...,q_599`. The delivered equation is the ordinary polynomial

\[
P_{1190}(\mathbf z)=\sum_{i=0}^{599}q_i(\mathbf z)^2=0,
\qquad \mathbf z\in\mathbb Z^{1190}.
\]

Over the integers a finite sum of squares is zero exactly when every summand is zero. Combining Sections 2–4 with the unchanged source theorem proves, in ordinary mathematics formalizable in ZFC,

\[
\exists\mathbf z\in\mathbb Z^{1190}\;P_{1190}(\mathbf z)=0
\quad\Longleftrightarrow\quad
\neg\operatorname{Con}(\mathrm{ZFC}).
\]

Classical negation therefore gives the requested absence-of-solutions equivalence. Nothing in the new proof assumes either the consistency or the inconsistency of ZFC.

The independent expansion uses the diagonal terms and twice the distinct cross terms of each squared residual. It checks every coefficient against `output/expanded_polynomial.json`. This supplies the exact degree 4, all 26,411 monomials, and coefficient height 83,900,628. There is no polynomial norm, denominator clearing, bounded search, or exponentiation operator in this final equation.

## 6. Independent finite verification

The reviewer-authored verifier is `verify_direct_independent.py`. It uses only the Python standard library and imports neither the construction builder nor its projection or expansion routines. It checks:

- frozen parent bytes and both certificate-to-equation hashes;
- unchanged source variables and rows;
- all 234 exact guards, with fresh auxiliary triples;
- all 288 exact ordered nonnegativity implications;
- the restricted 234-guard lower bound for this literal-row rule family;
- every one of the 34 signed monic eliminations and inverse formulas;
- exact final row and coordinate maps;
- both complete expanded polynomials and every stated metric.

It also verifies that the domain declaration agrees between each residual system and its expanded polynomial, and that every declared coordinate actually occurs in the residual system and in the fully expanded polynomial.

Four corruption controls are rejected with certificate hash checking deliberately disabled for the relevant semantic test: a negative inference coefficient, a wrong guard sign, an altered restoration polynomial, and an altered expanded coefficient. Both normal execution and `python3 -O` execution pass; the verifier's substantive checks do not depend on Python assertions.

Receipts are `DIRECT_INDEPENDENT_CHECKS.json` and `DIRECT_INDEPENDENT_CHECKS_OPTIMIZED.json`. The final expanded polynomial has SHA-256

```
3f33f1bd12c4b74f56dd350eee67f9f8b0f49a0d41ae94bda4d01607e592cbb9
```

The projection certificate has SHA-256

```
6d7472eb7705147a2a359e279b7c0fb4a2cecc8c90479ae23c96a2e1a3eb3abc
```

## 7. Assessment and limits

The new integer equation is a genuine reduction of the reviewed direct-calculus integer frontier: it uses 500 fewer unrestricted integer variables than the supplied 1,690-variable batched comparison, and 898 fewer than the synchronized parent's 2,088-variable integer companion. The 522-variable natural equation remains a different domain comparison. No conclusion about globally minimal variable count, degree, coefficient height, or worldwide priority follows from these finite comparisons.

The principal new reusable observation is that domain conversion can exploit an ordered proof of nonnegativity already present in the actual polynomial equations. The positive-multiplier version also uses non-unit linear coefficients without assuming divisibility. Coupled with signed polynomial projection, this gives an explicit quartic in unrestricted integer coordinates while leaving the calibrated proof encoding untouched.

**Signed review scope:** separate mathematical and finite-arithmetic reviewer; new transformation proof and exact artifacts approved at the hashes above; inherited C222-to-ZFC calibration relied on as identified in the source package.
