# Independent mathematical review of the padded direct compiler

Review date: 23 October 2026. This review was prepared independently of the
preprocessing and signed-compiler authors. It concerns the actual direct C222
proof-certificate route, not a simulated Turing-machine execution. It is an
ordinary mathematical review, not a new Lean/Rocq certificate or external human
peer review.

## 1. Scope and imported statements

The reviewed baseline is the direct compiler in the incoming Round 12 package.
Its twelve-rule numerical Horn source is supplied literally in
`source/horn_shared_source.json`. The final new preprocessing is
`source/build_direct.py`; the new outer arithmetic adapter is `build.py`.

The review imports the identified ordinary correctness theorems for the fixed
C222 calculus, its ZF-refutation calibration, the ZF/ZFC consistency translation,
and the finite arithmetic graphs for Pell coordinates, powers, binomials,
factorials, and the CRT product. Those imported statements are separate from the
new algebraic reductions. The new reductions use finite induction and integer
arithmetic and are formalizable in ZFC. Composing them with the imported ordinary
calibration proves the requested consistency biconditional at that mathematical
level. Referring to external Lean declarations does not itself emit a derivation
in the repository's encoded object-language ZFC calculus.

The baseline review is retained at
`provenance/BASELINE_MATHEMATICAL_AUDIT.md`.
That source already supplies the unordered-flow certificate and fixed-height
method. The present contribution must not claim those inherited ideas as newly
introduced.

## 2. Projecting deterministic local coordinates

For every one of the twelve alternative rule branches, each constructor wire is
defined, in topological order, as a polynomial with nonnegative integer
coefficients in the branch's four base parameters and previously defined wires.
The remaining labels are determined as follows:

* Axiom branches have both premise labels zero and the stated polynomial
  conclusion label.
* Truth has labels `(0,0,0)`.
* Modus ponens can use base parameters `a,b` as its first premise and conclusion;
  its second premise is the explicit implication constructor `Imp(a,b)`.
* Generalization can use `b` as the premise, zero as the second padded premise,
  and the explicit universally quantified constructor with parameter `a` as
  conclusion.

Substituting these labels and constructor values eliminates all their defining
equalities without division. Conversely, every old branch zero has exactly these
wire and label values, after the stated harmless renaming of modus-ponens and
generalization parameters. Thus this is a two-way existential equivalence.

The bundled axiom's side condition is retained. It is

    ((c-a)(c-b))^2 = (d+1)^2,    d >= 0.

For naturals `a,b,c`, this has a natural `d` precisely when `c != a` and `c != b`:
in the forward direction the right side is positive; in the reverse direction
choose `d = |(c-a)(c-b)| - 1`. Removing this fourth parameter without another
representation of the side condition would be incorrect. The new builder does
not remove it.

Each branch retains its own accumulator update. The local polynomial is a
product of the twelve branch sums of squares, plus the sum of the beta-row
squares. All factors in the product and the added terms are nonnegative at every
integer assignment. Therefore local vanishing means all beta rows vanish and at
least one branch has both its required guard and its own update equal to zero.
Sharing the four base parameters among inactive alternatives causes no problem:
only a selected alternative must vanish. Conversely a selected valid rule
supplies its parameters and makes its factor zero.

The intermediate preprocessing therefore has four base parameters and six
adjacent-beta quotient/remainder/slack coordinates. The final version removes
the two slack coordinates as follows. In the beta completeness construction the
common scale `y` can be chosen above every accumulator value. Impose the stronger
coordinate bounds `0 <= S,S_next <= y`. For each nonnegative row index `i`,

    S <= y < 1+(i+1)y,

and the corresponding next-index inequality also holds. The two division
equations therefore already determine the beta remainders; their private bound
slacks are unnecessary. Conversely, the discarded slacks can be restored as
`1+(i+1)y-S-1 >= 0`, with the appropriate index. Thus the final local block has
exactly eight existential columns: four base parameters and two remainder/
quotient pairs. The other five local inputs `(N,x,y,M0,i)` are outer parameters
and the bounded row index.

## 3. Padding and the height bound are not circular

Let a finite refutation tree have an ordered expansion with `L` rule instances.
There are finitely many values of its four base parameters. Choose `N` at least
`L`, at least every such parameter, and at least one. Append `N-L` truth rows.
Truth has labels `(0,0,0)` and its update is exactly `S_next=S`; it can use all
four parameters zero. It therefore preserves the target, the flow balance, and
the accumulator endpoints. This is the reason `N` can bound all four base
parameters. No claim is made that an arbitrary unpadded proof length already
bounds its syntax parameters.

For each branch `b`, let its three explicit nonnegative label polynomials be
`p_b,q_b,v_b`. Define the single polynomial

    H(N) = sum_b [p_b(N,N,N,N) + q_b(N,N,N,N) + v_b(N,N,N,N)].

Monotonicity of polynomials with nonnegative coefficients shows that every label
in a row whose four parameters are at most `N` is at most `H(N)`. The bundle's
guard need not hold at `(N,N,N,N)` for this bound: the displayed label
polynomials are defined and nonnegative there regardless of guard truth.

Choose

    M0 = 2^(2 H(N) N + 1),    M = M0 + 1.

For any list of `N` selected rows, form

    A(X) = product_i (1+v_i X),
    B(X) = (1+X) product_i (1+p_i X)(1+q_i X).

Every coefficient of either polynomial is nonnegative. The sums of their
coefficients are at most `(H(N)+1)^N` and `2(H(N)+1)^(2N)`, respectively. The
elementary inequality `h+1 <= 2^h` for natural `h`, including `h=0`, bounds both
by `M0`. Thus every coefficient of `A-B` has absolute value at most `M0<M`.
If `A(M)=B(M)`, choose the least nonzero coefficient of `A-B`. Dividing out its
power of `M` and reducing modulo `M` makes that nonzero coefficient divisible by
`M`, contradicting its absolute bound. Hence `A=B` as integer polynomials.
Multiplicity at each distinct rational root `-1/j`, `j>0`, gives the exact Horn
flow balances. The inherited finite single-conclusion flow argument recovers a
refutation even when the selected rows contain cycles or repeated premises.

For completeness the choices are made in this order: proof tree and parameters;
padding length `N`; height `H(N)` and base `M`; accumulator values; beta code and
scale exceeding all accumulator values; a finite bound on the two beta
quotients; the CRT certificate and its
arithmetic witnesses. In particular the bound `U` for beta witnesses is chosen
after `M` and is not used to define `M`. There is no circular height condition.

For soundness the CRT certificate recovers all four parameters at most `N`, so
the same height argument applies to any polynomial zero, without assuming that
it arose from canonical completeness choices.

## 4. Heterogeneous coordinate bounds in the CRT block

Fix outer parameters and let `e-f` be the supplied local polynomial expressed
as a difference of polynomials with nonnegative integer coefficients. Use the
bound vector

    b = (N,N,N,N,y,U,y,U).

Set `L=e(N,b)+f(N,b)+N+U+y+1`, `T=L!`, `D_j=1+(j+1)T`, and
`B=product_(j<N) D_j`. The literal arithmetic graphs implement this product via
the pinned factorial/binomial/remainder identity. The existential certificate
uses, for each encoded coordinate `a_l`, the reduced requirement

    B divides binomial(a_l,b_l+1),

as well as `B | 1+(index+1)T` and the encoded local congruence modulo `B`.
This cancellation is sound in both directions. Indeed `L>=b_l+1`, so
`F_l=(b_l+1)!` divides `T`. Each `D_j` is one modulo `F_l`, and their product
`B` is therefore one modulo `F_l`. Thus `gcd(B,F_l)=1` and

    B | F_l binomial(a_l,b_l+1)  iff  B | binomial(a_l,b_l+1).

The extra factorial graph is not silently treated as free: it has been removed
by this exact divisibility equivalence. The stronger factorial argument is
displayed in the literal circuit and participates in every CRT construction.

For soundness fix `j<N` and a prime `p` dividing `D_j`. Such a prime exists
because `D_j>=2`. It cannot divide `T`, so `p>L`. The falling-factorial
certificate supplies `w_l <= b_l` congruent to `a_l` modulo `p`. If
`a_l < b_l+1`, take `w_l=a_l`; otherwise use a factor
`a_l-s`, `0<=s<=b_l`, divisible by `p`. This argument also covers `p<=b_l`:
there is no omitted hypothesis that every coordinate bound must itself be
smaller than `p`.

The index certificate gives `index=j (mod p)`, since `T` is a unit modulo `p`.
Polynomial congruence gives `e(j,w)=f(j,w) (mod p)`. Monotonicity and
`j<N` give both values at most `L<p`, so they are equal as integers. This
establishes the full bounded row condition.

For completeness choose `U` above the two beta-quotient values in the finite
rows. The `D_j` are pairwise coprime: a common prime divides `j-i` while being
coprime to `T`, whereas `0<|j-i|<N` divides `N!` and hence `T`. CRT encodes the
selected coordinate values and the indices. Every falling-factorial certificate
follows because one factor vanishes modulo each `D_j`; the coprimality argument
then gives the reduced binomial certificate. The bound vector may be
heterogeneous; no step requires all eight entries
equal.

When `N=0`, this bounded block is correctly vacuous and `B=1`. The two outer
endpoint equations nevertheless use the same beta modulus and force the same
remainder to equal both `M0+2` and `1`. Since `M0` is natural, this is impossible.
Thus no zero-length false refutation is admitted.

## 5. Genuine signed arithmetic and one congruence quotient

The outer compiler can evaluate signed polynomial expressions directly over
the integers. The original positive-pair representation sends `(A,B)` to
`A-B`. Its addition and multiplication formulas are exactly the ring identities

    (A-B)+(C-D) = (A+C)-(B+D),
    (A-B)(C-D) = (AC+BD)-(AD+BC).

The signed adapter uses these represented integers themselves, rather than
separately storing the positive and negative circuits. Sum-of-squares and
product disjunctions keep their exact represented values. Arithmetic-helper
outputs and inequality slacks retain their declared natural domains unless a
specific sign inference below proves otherwise. Negative intermediate circuit
wires are permitted and explicitly quantified as unrestricted integers.

Every congruence occurrence uses a fresh private signed integer `q` and the
residual `a+m q-b`, instead of natural `q0,q1` and residual
`a+m q0-b-m q1`. From old witnesses take `q=q0-q1`. Conversely from a signed
witness take `q0=max(q,0)` and `q1=max(-q,0)`. This preserves the entire residual
value, not just whether it vanishes. Therefore it also preserves appearances
inside inactive disjunction branches. The argument holds for `m=0` as well:
both encodings reduce to `a=b`.

It is essential that these quotients are private to their indicated congruence
residuals. The inspected adapter allocates a new variable at each `mod` call;
no independent meaning is assigned to a dropped natural quotient.

The local `e,f` polynomials remain natural polynomials. They are not replaced by
a signed majorant. This is necessary for the monotonicity argument in Section 4.

## 6. Optional Euclidean-quotient sign inference

The optional optimization may remove the nonnegativity guard on a Euclidean
quotient `q` only after retaining `r,s>=0` and the two rows

    n = q d+r,    d=r+s+1,

with the dividend `n>=0` already proved from its input dependencies. Indeed
`q<=-1` would imply `n<=-d+r=-s-1<0`. Thus every solution automatically has
`q>=0`, and the omitted guard can be restored by the standard representation of
nonnegative integers. In the reverse direction an old nonnegative quotient is
already a valid unrestricted quotient.

For multiple omitted guards the dividend signs must be established in order;
one may use only explicitly guarded inputs and previously justified quotients.
An inference ledger and independent checks of its defining rows are required.
Declaring all division quotients automatically nonnegative without checking
their dividends would not be sound. The checker accompanying this review
verifies that condition when inference records are supplied.

## 7. Affine elimination and the final quartic

In a topologically ordered signed arithmetic DAG, retain one unrestricted wire
for each genuinely nonlinear multiplication. Substitute additions,
subtractions, and constant multiples into affine forms in earlier wires. The
delivered compiler also retains selected long affine forms as separate wires
with linear defining rows, to limit expression expansion. These wires are
counted, and this is a storage/variable tradeoff rather than a mathematical
necessity. Each retained multiplication has a quadratic defining residual.
Topological
induction proves that any common zero has exactly the intended wire values;
conversely every semantic input assignment determines the unique required
wires. No wire nonnegativity is needed for this integer-arithmetic argument.

For each semantic input that must remain nonnegative, append one row

    x = a^2+b^2+c(c+1),    a,b,c in Z.

Its right side is nonnegative on all integers. It is surjective onto the
naturals: `4x+1` is positive and is `1` or `5` modulo `8`, hence is a sum of
three squares by Legendre's theorem; exactly one summand is odd modulo four.
Writing that square as `(2c+1)^2` and the others as `(2a)^2,(2b)^2` gives the
formula. This is the nonnegative representation, without the additional `+1`
used for strictly positive inputs.

The single defining polynomial is the sum of the squares of all quadratic
rows. Over the integers its zeros are exactly their common zeros. Its degree
is at most four; the delivered nonzero degree-four coefficients certify
exactness. All gate and sign-witness variables must be counted. Affine
abbreviations are not additional existential variables.

## Conclusion

No mathematical defect was found in the eight-column projection, padding-based
label bound, heterogeneous CRT compilation with factorial cancellation, or signed arithmetic reduction
under the stated interfaces. The optional quotient-sign optimization is valid
with the checked dividend dependency order. The conclusion is an explicit
ordinary quartic and a ZFC-formalizable reduction to the same fixed direct
refutation source. It is not a claim to the fewest-variable unrestricted
Diophantine consistency equation, and it does not close the repository's
separate object-language proof-certificate obligations.

Finite replay establishes the stated literal identities and size measurements;
it neither decides consistency nor proves an unbounded imported calibration
theorem by testing.

## Final artifact audit

The final eight-column signed construction was independently checked from its
literal JSON files without importing or executing either builder. The receipt
`checks/DIRECT_FINAL_INDEPENDENT.json` records:

* 7,617 unrestricted integer variables, 4,379 quadratic residuals, and exactly
  148,220 nonzero monomials in the collected quartic.
* 3,198 retained nonlinear wires and 31 retained affine wires.
* 201 private signed congruence quotients replacing 402 natural coordinates.
* 27 omitted Euclidean-quotient nonnegativity guards, each justified from a
  previously nonnegative dividend and the retained remainder/slack rows.
* Exact polynomial comparison of all 40 indexed-Pell criteria, 40 natural-power
  criteria including their zero cases, and 27 division/remainder criteria.
* Exact agreement of all 120 arithmetic-call interfaces, all source bound and
  height expressions, both CRT instantiations, all coordinate certificates, and
  the ordinary global equations with the separately audited natural front end.
* Semantics-preserving pruning, every affine and nonlinear restoration row,
  every retained semantic guard, and the complete expanded sum of squares.

The maximum absolute coefficient is 8,974,652,400,619,654,748,160. The final
polynomial file's SHA-256 is
`af06bc5c92b9ab6b1cb4d0da94933c2280720537a3088585649f7793466da382`.
The checks use exact integer arithmetic, not sampled equality tests.

The checker accepts a directory containing the four final arithmetic JSON
files and an explicit path to the natural source circuit:

    python3 check_signed_independent.py FINAL_DIRECTORY \
      --natural-source NATURAL_SOURCE_CIRCUIT \
      --receipt DIRECT_FINAL_INDEPENDENT.json

Its source contains no removable acceptance assertions. The check does not
re-establish the imported unbounded Pell, factorial, CRT-product, or logical
calibration theorems; those remain the mathematical dependencies identified in
the main proof.
