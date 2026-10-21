# A pairing-parametric native ZFC calculus

## Positive result and exact scope

The inherited unrestricted numerical calculus is unchanged up to an
explicit recursive isomorphism if Cantor pairing is replaced everywhere
in its formula constructors by

\[
D(a,b)=2^a(2b+1)-1.
\]

The dominated-fourth-parameter version remains equiconsistent as well.
Its proof requires a second argument: numerical domination is not
preserved by the recursive isomorphism, but the existing finite recovery
certificate works for the new pairing because every restricted leaf uses
either fourth parameter zero or an actual implication subterm of its
first parameter. This is a formalism and abstract-enumerator result, not
a state-count claim or a binary-machine verification.

## 1. Pairing hypotheses

Let \(P_0,P_1:\mathbb N^2\to\mathbb N\) be effective bijections satisfying
\(P_i(0,0)=0\) and \(P_i(a,b)\ge\max(a,b)\). Put

\[
J_{i,t}(a,b)=4P_i(a,b)+t\qquad(t=0,1,2,3),
\]

where tags zero through three are implication, membership, universal
quantification, and equality respectively. Truth and falsity remain the
numerical codes zero and one. For positive constructor outputs, both
inputs are strictly smaller than the output. The unique recursive alias
at zero is \(J_{i,0}(0,0)=0\).

Dyadic pairing satisfies the hypotheses. The inverse of \(n\) is

\[
a=\nu_2(n+1),\qquad
b=\frac{(n+1)/2^a-1}{2}.
\]

Existence and uniqueness are the unique decomposition of a positive
integer into a power of two times an odd integer. We have
\(D(a,b)\ge 2^a-1\ge a\) and \(D(a,b)\ge2b\ge b\).

## 2. Hereditary recoding

Define \(\phi(0)=0\). For positive \(n\), write
\(n=4P_0(a,b)+t\) using its residue modulo four and the inverse pairing,
and recursively put

\[
\phi(n)=4P_1(\phi(a),\phi(b))+t.
\]

This is well founded on the natural number \(n\). It obeys the displayed
constructor equation also at zero because both pairings have the zero
alias. Define \(\psi\) by interchanging \(P_0\) and \(P_1\).
Strong induction shows \(\psi(\phi(n))=n\): decode the outer constructor
and apply the inductive hypothesis to its two smaller arguments. The
analogous argument gives \(\phi(\psi(n))=n\). Thus \(\phi\) is a
bijection, fixes all four codes \(0,1,2,3\), and intertwines all four
constructors.

No ordinary formula grammar is assumed here. Every natural code is
recoded, including natural numbers used simultaneously as formula codes
and bound-variable indices. In particular, the native merged equality
row with binder label \(R(A,B)\) is respected exactly:
\(\phi(R_0(A,B))=R_1(\phi(A),\phi(B))\). Relabeling only the decoded
variables while leaving their integer codes fixed would be insufficient.

Every retained unrestricted axiom and the set-theoretic bundle is an
expression in these constructors and the fixed constants. Their
instances therefore map to the corresponding new instances. The bundle
gate \(C\ne A,B\) is preserved by injectivity. The same is true of any
finite support exclusion expressed by equality or inequality of the
recoded labels. Truth, modus ponens, and theorem-only generalization are
preserved. Induction on finite derivations, in both directions, gives

\[
\mathcal C_{P_0}\vdash n
\quad\Longleftrightarrow\quad
\mathcal C_{P_1}\vdash\phi(n).
\]

Since \(\phi(1)=1\), the two unrestricted calculi are equiconsistent.
All constructions and finite-derivation inductions formalize in ZFC.

## 3. Domination must be reproved, not transported

The order on numerical codes is not preserved. For Cantor-to-dyadic
recoding, \(\phi(16)=20\) and \(\phi(20)=16\). Thus a direct claim that
\(U\le A\) is preserved would be false.

Instead use the inherited full-rho8 certificate. Its sole normalization
is \(I(0,0)=0\). Every dominated-row leaf has either \(U=0\), or \(U\)
is a literal implication subterm of \(A\). For any pairing satisfying
the above hypotheses, implication dominates each argument. Induction
through an implication context therefore proves the required
\(U\le A\) for every numerical assignment, regardless of nested zero
aliases. Forward substitution and MP then verify the same finite proof.

Consequently each unrestricted rho8 instance is derivable in the new
dominated calculus; the converse inclusion is immediate. The rigorous
comparison is

\[
\mathcal C^{\rm dom}_{P_0}
=\mathcal C_{P_0}
\cong\mathcal C_{P_1}
=\mathcal C^{\rm dom}_{P_1},
\]

where equality means equality of theorem sets for the fixed pairing, and
the middle isomorphism is hereditary recoding. The certificate contains
3728 proof nodes and 5160 shared terms. Re-running its independent forward
checker gives `pairing_certificate_check.json`; numerical evaluation of
the enormous dyadic formula codes is unnecessary.

## 4. Abstract scheduler and strong compiler

Replace the pairing consistently in formulas, theorem stacks, and packed
candidate words. The abstract commands retain their contracts: push/pop
are inverse, constructors make the new native formulas, and proof-list
field reads use the new inverse pairing.

If \(f(n)\) is the second component of the dyadic inverse, then
\(f(n)\le\lfloor n/2\rfloor\). A nonzero proof pointer \(r\) always
fetches candidate \(r-1\); each subsequently decoded suffix pointer is
bounded by a component of a smaller packed code. Thus proof pointers
drain by the same well-founded argument as before. The finite list packer
and its inverse remain exact. The current cofinal reset family

\[
P(3,P(1,P(1,P(Y,R))))
\]

is at least \(Y\) under either pairing, so it supplies a refuting candidate
above every finite initial cutoff whenever a refutation exists. The
strong compiler's ordinary numerical facts remain true; for example
\(I(t,1)>0\) still makes its forced MP failure work, and AX can choose
\(U=A=C\) to force a zero gate when resetting.

The existing Cantor-diagonal *arbitrary-tail* scheduling theorem is not
automatically transferred: changing pairing changes the order in which
candidate words run. It is not needed for a theorem-safe entire stack.
In particular, if a new binary startup reaches the accepted candidate's
logical tuple

\[
[np,tw,ws,ac,d,h,s_1,s_2,pl]=[3,0,0,0,3,0,0,0,0],
\]

then its top, whole stack, and cache are truth-safe under the dyadic
encoding. The additive value three is unrestricted, and cutoff three is
permitted by cofinal completeness. This statement is conditional on the
actual startup tuple of the changed binary machine; the old finite trace
does not certify a modified transition table.

## 5. Remaining concrete obligations

A small-machine construction must supply the dyadic pairing, unpairing,
field-reader, and constructor macro implementations with the same
register/stack contracts; instantiate the modified source compiler;
allocate and verify the exact binary decoder; prove the whole-source
runtime contracts; and verify the complete blank-tape startup. The
abstract pairing theorem removes the need for a new ZFC-consistency
calibration of a wholly different logical theory. It does not remove
these arithmetic and machine-implementation obligations.
