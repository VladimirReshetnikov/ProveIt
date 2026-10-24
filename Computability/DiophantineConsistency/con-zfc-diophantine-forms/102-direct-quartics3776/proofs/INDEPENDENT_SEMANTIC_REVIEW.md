# Independent semantic review of the direct C222 construction

Snapshot reviewed: `278bc68df1af125d62f9cbfe28c9fd3ebcf50d5b`.
Calibration source pin: `9a33342a03d19cf5b061b2083c6b5d3f27f752ed`.

## Conclusion and precise proof status

The reviewed direct construction has a defensible **ordinary mathematical proof
formalizable in ZFC**, using the named source-calibration and arithmetic
representation theorems. The remaining lack of a newly emitted object-language
ZFC derivation or a new end-to-end Lean theorem is a formalization deliverable
boundary; it is not, by itself, an unproved mathematical implication. This is
different from the older native machine/coefficient routes whose reviews retain
additional semantic calibration hypotheses.

This conclusion imports the explicit C222 calibration theorem and the finite
Pell/power graph theorem as established mathematical results. It is not an
independent reproof or rebuild of their complete Lean dependency closures. Their
ordinary proofs are set theoretic and arithmetic, and use no premise asserting
that ZFC is consistent. Avoid the invalid shortcut “Lean proved it, therefore
ZFC proves it”; the reason ZFC suffices is the actual mathematical content of
these constructions.

## The exact semantic endpoint

The pinned `KCode222.lean` defines an inductive numerical calculus `C222` on
natural numbers, with truth 0, falsity 1, modus ponens, generalization, eight
displayed numerical rule families, and the guarded seed bundle. The declarations
in `KEndpoint.lean` are:

```
c222_of_zf_refutation
c222_iff_zf_refutation
```

The latter is the unconditional equivalence

```
KCode222.C222 Code254.F <-> BProv ZFax_s [] Form.fBot.
```

Its declaration has no Turing machine, interpreter, simulator, coefficient port,
or native encoding premise. The proof uses the C222 upper bound and the direct
seed-model lower bound. `ConstructibleChoice.lean` then supplies

```
zf_refutation_iff_zfc_refutation :
  BProv ZFax_s [] Form.fBot <-> BProv ZFCax_s [] Form.fBot.
```

The reverse direction is the usual constructible-model relative consistency
argument, expressed via first-order soundness and completeness. It does not
require a transitive or externally well-founded model. The model construction
in the C222 lower chain uses the **internally** well-founded part of a quotient
structure; it must not be paraphrased as producing an externally transitive
model from mere consistency.

## Flow certificate: no acyclicity assumption is missing

For finitely many valid single-conclusion instances, let the conclusion label
of instance i be c_i and its two truth-padded premise labels be p_i,q_i. At each
positive label j impose

```
number of c_i equal to j
  = [j=1] + number of p_i equal to j + number of q_i equal to j.
```

A proof tree gives these counts. Conversely take the closure from truth and
the selected premise-free rules, using just the finite supported rule family.
If label 1 is outside the closure, sum the displayed balance over the finitely
many supported labels outside the closure. For each rule with conclusion
outside, at least one premise is outside, so its contribution to conclusion
count minus premise count is at most zero. Rules with conclusion inside also
have nonpositive contribution. The right side nevertheless contributes one.
This contradiction proves derivability. Cycles, duplicated premises, repeated
rule occurrences, and truth labels do not invalidate the argument.

## Sharp product carrier

Let t,m>=1 bound the number of rule instances and all labels, and put
M=(m+1)^t. Let

```
A(X)=product_i(1+c_i X),
B(X)=(1+X) product_i(1+p_i X)(1+q_i X).
```

If A(M)=B(M), B has at most t nonconstant factors: otherwise
B(M)>M^(t+1), whereas A(M)<M^(t+1), since
1+mM<(m+1)M. Consequently A(1),B(1)<=M. Their constant coefficients are one;
every other coefficient is strictly less than M. If A-B had a least nonzero
coefficient, evaluation at M and reduction modulo M after removing its power
of M would make it divisible by M, a contradiction. Thus A=B. Multiplicity
of each rational root -1/j gives exactly the flow balance at positive j.

The accumulator endpoints and transitions telescope to A(M)=B(M), because all
linear factors are positive. Completeness expands a proof tree in the order of
its open obligations and takes each accumulator entry to be their product.
The finite proof and label bound are chosen before the carrier, trace, beta
encoding, and independent bounds on CRT row witnesses. This order avoids a
circular witness bound.

## Shared CRT prime lifting

For nonnegative-coefficient polynomials E,F, row index bound N, and coordinate
bounds u_j, set

```
H=E(N,z,u)+F(N,z,u)+N, T=H!,
D_i=1+(i+1)T, B=product_{i<N}D_i.
```

The D_i are pairwise coprime: a common divisor is coprime to T and divides an
index difference, which divides H!. For soundness, choose p|D_i. Then p>H.
The condition B|choose(A_j,u_j+1), multiplied by (u_j+1)!, implies that p
divides a factor A_j-r for some r in [0,u_j]. The full falling-factorial
identity uses signed differences and remains true when A_j<=u_j, because it
then includes a zero factor. Thus a bounded decoded coordinate w_j congruent
to A_j modulo p exists. Index divisibility gives C congruent to i modulo p.
The row congruence and monotonic E,F bounds yield equality of values in [0,H],
since p>H.

Completeness does not assume H>=u_j+1. For R_j=(u_j+1)!, let R_ij contain
exactly all prime powers of R_j at primes dividing D_i. Use CRT modulo
D_i R_ij to choose A_j congruent to the desired coordinate of row i. These
strengthened moduli remain pairwise coprime. The numerator of the binomial
is divisible by D_i R_ij. Cancel R_ij and then the coprime factor R_j/R_ij
to obtain D_i|choose(A_j,u_j+1). Positive encoded columns are chosen by adding
a large multiple of the product of strengthened moduli. A plain B shift is
not valid without factorial coprimality. Prime factorization here constructs
proof witnesses only; it introduces no hidden prime-factorization operator in
the final polynomial.

Every step of this argument is finite and uniform. In a model of ZFC, “finite”
and “natural number” have that model's meanings; induction, finite products,
factorization, and CRT remain theorems for all its internal natural numbers.
The proof is not restricted to each separately verified external numeral.

## Signed quotient transformation

Suppose a natural system has private variables q_+,q_-,u,v used exactly as

```
u=M q_+, v=M q_-, E+c(u-v)=0,
```

where c is a nonzero integer and M is a nonnegative expression in retained
natural coordinates. Replace these rows by

```
E+c M z=0, z in Z.
```

Projection takes z=q_+-q_-. Conversely set q_+=max(z,0),
q_-=max(-z,0), u=M q_+, v=M q_-. This restores all three rows with natural
values. No positivity or nonzero condition on M is required. The private-use
condition is essential. In the actual transformation, signed coordinates
must be absent from every retained nonnegative gate/modulus expression; this
is a finite syntactic check. Nonnegative affine bridge eliminations restore
their omitted coordinates uniquely. The polynomial is the sum of squares of
all retained residuals, so over integers zero enforces each row exactly.

The standard three-variable certificate

```
x=a^2+b^2+c(c+1)
```

represents precisely x>=0. Necessity is immediate, including negative c.
For sufficiency, 4x+1 is not of the form 4^r(8s+7), so Legendre's three-square
theorem applies. Modulo four, exactly one representing square is odd; write
its root 2c+1 and the other roots 2a,2b, then divide by four.

## Guard inference and normalization

An exact residual written as x A-B=0, with x absent from A and B, supplies
the following implications once A>0 is established: B>=0 implies x>=0;
B>0 implies x>=1; B-A>0 implies x>=2. The final implication uses integrality.
To certify a polynomial sign, substitute X_i=T_i+L_i for previously proved
nonnegative lower bounds L_i. Nonnegative coefficients suffice if every
unconstrained coordinate occurs to even exponent in every remaining monomial.
A positive constant coefficient makes the sign strict. Each derivation uses
only bounds proved before that step, preventing circular sign arguments.

Some seed nonnegativities come from diagonal sign symmetries. Verify that
changing the specified coordinate signs takes each exact core residual to
itself or its negative. If each involution changes exactly its own pivot
among the semantic coordinates, and no pivot is explicitly guarded, all
chosen guard equations are preserved. The diagonal involutions commute and
do not change each other's pivots. Starting with an arbitrary candidate
zero, apply whichever involutions make their pivots nonnegative; only then
use the ordered sign derivations. The conclusion is that an integer zero
has a suitable normalized zero in its orbit. It is not a claim that every
raw zero is already componentwise nonnegative.

## Monic polynomial projection over the integers

Let one exact residual of an integer system be epsilon*(x-G(y)), with
epsilon equal to 1 or -1, and with x absent from the integer polynomial G.
Delete this row and replace x by G in every other row. Projection maps every
old zero to a new zero; inserting x=G maps every new zero to an old zero.
These maps are inverse, so the zero sets are in bijection, not merely
equinumerous by an existence argument. A sequence of eliminations is inverted
in reverse order, each restored value being an integer polynomial in values
already available.

If all original residuals have degree at most two, this degree bound is
preserved in either of two situations: G is affine; or G is quadratic and x
occurs only as a scalar-linear term in every other current residual. In the
second case no mixed or repeated occurrence of x is allowed. Literal sparse
substitution checks this criterion and the resulting residual degree at
each step. Removing identically zero rows is valid. The final equation is
again the sum of the squared residuals, of degree at most four. Its exact
degree and coefficient height are properties of the fully collected
polynomial and are checked by full symbolic expansion.

The integer domain is essential: a monic polynomial lift need not preserve
nonnegativity. These eliminations are therefore applied after the finite
natural-coordinate guards have been installed. They preserve the guarded
integer zero set; they are not justified as unguarded natural projections.

## How to state the result

Once the literal finite residual system and its audits are fixed, the proved
chain is:

```
integer zero of the new polynomial
  <-> natural zero of the frozen shared-CRT parent
  <-> finite valid C222 flow certificate
  <-> C222 derives 1
  <-> sealed ZF refutation
  <-> sealed ZFC refutation.
```

Every theorem imported from an earlier source should be named, pinned, and
bundled or linked. The new result can be stated as an ordinary theorem of ZFC
on these proved dependencies. Separately disclose that no new kernel-checked
end-to-end certificate or explicitly printed object-language ZFC proof is
provided. It would be misleading to describe the absence of that artifact as
an additional conjectural semantic assumption, or to describe finite tests as
the source of the unbounded mathematical proof.

## Prior art for alternative encodings

Sun's 2026 preprint already gives ten unrestricted integer variables, and
ProveIt's package 31-sun10 already specializes it. Thus a new direct quartic
with thousands of variables is a tradeoff and a reduction relative to that
direct family, not a minimum-variable result.

A theoremhood-based route without a Turing-machine encoding was already
explicitly developed by M. Carl and B. Z. Moroz, *On a Diophantine
representation of the predicate of provability*, MPIM preprint 2007-132,
https://webdoc.sub.gwdg.de/ebook/serien/e/mpi_mathematik/2007/132.pdf.
Their polynomial specializes the pure-predicate-calculus provability relation
at an implication from finite Goedel--Bernays axioms to falsity. It is useful
historical context, not a newly discovered idea or evidence of a smaller
literal equation.
