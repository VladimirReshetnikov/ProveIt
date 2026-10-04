# Scoped review of incoming arithmetic Reports 39, 41, 43, 45 and 46

These five archives were received at commit
`c5612efa171fa62470285049ee45d1d06ee25578`. The [receipt](review_incoming_arithmetic_reports_39_46.json)
pins their historical Git blobs and all 408 members. All five complete
READMEs and eleven additional proof/source notes were read in full; their
exact member paths and hashes are recorded. This is a review of that scope,
not approval of every manuscript, analytic appendix or saved diagnostic.
Archived programs were never executed, and package test counts were not
reproduced. No enormous full counterexample tuple was materialized.

The established complete universal polynomial remains **84=47M+37A**, with
18 positive witnesses and exact degree187. The independent-gamma83 ordinary
input language remains unresolved. Several historical uses of “83” and
“82” in these reports denote different polynomials:

| Candidate | Operations | Positive witnesses | Exact degree | Present status |
|---|---:|---:|---:|---|
| Current universal polynomial |84=47M+37A|18|187|Established|
| Independent-gamma chart |83=47M+36A|18|187|Language unresolved|
| Free-coefficient chart in Reports43/46 |83=46M+37A|18|111|Inherited compiler language refuted by the separate odd-prime family|
| Square/product chart in Reports45/46 |82=45M+37A|18|185|Inherited compiler language refuted|
| Historical normalized first-index deletion in Report41 |81=46M+35A|17|168|Full all-input counterfamily in Report41|
| Historical ordinary auxiliary first-index deletion in Report41 |82=45M+37A|17|124|Full all-input counterfamily in Report41|

The receipt finds 48 byte-identical member occurrences of current WIP
snapshots. In particular, Report43 carries the exact free-coefficient83,
current84 and parent85 JSON sources; Report45 carries the exact square/product82
JSON source; Report46 carries both that source and the later prime-collapse
receipt. Identical basenames such as `README.md` do not identify identical
artifacts; the receipt records these collisions separately.

## Report39: a Jacobi obstruction to removing the main comparison

The read Jacobi addendum strengthens an inherited all-but-main projection
construction. Its elementary identity is valid: for an even square q with
3 not dividing q, put h0=4q^3+3, X=q^3 w, H=4q^6 w+h0. Then

    Jacobi(X,H) = Jacobi(w,h0).

The factor q^3 is a square coprime to H. Also gcd(w,H)=gcd(w,h0), and
H and h0 are both 3 modulo8. Removing powers of two gives matching signs;
quadratic reciprocity on the remaining odd part gives the displayed equality,
including the common-zero case. Since Jacobi(2,H)=-1, every congruence
2^p=X modulo H with p odd requires Jacobi(w,h0)=-1.

The genuine compiler family has w=1+(q-1)r. Restricting r to multiples
of h0 (or 4h0) makes its Jacobi symbol +1 and therefore excludes every odd
main index. This is a concrete obstruction, not an inference from a search.
It also excludes the second positive21 residual branch because its raw
residue lies strictly between0 andH and the root is larger thanH.

The addendum retains the parent's shrinking-target existence argument on
this fixed arithmetic progression. Its transformed second derivative and
discrepancy estimates have the expected scaling. The parent analytic proof
and its long independent audit were not read in full in this intake, so
this review authenticates and checks the new Jacobi filter but does not
recertify the complete analytic existence argument. The result establishes
nonredundancy of specific comparisons; it supplies neither a full zero of
a smaller polynomial nor an improved universal operation count.

## Report41: first-index deletion fails with every remaining block present

The full counterfamily and exact source correspondence were read. Unlike
the older source-only deletion scout or a scaled inner obstruction, this
construction retains ordinary input, fixed compiler masks, packing,
transport, positive outer slack and the complete auxiliary extension.

The central arithmetic is consistent. Choosing t=L! makes q=2^t equal1
modulo the odd part of t: every required odd-prime-power totient divides
t. The CRT chooses a small e=3 modulo4 and positive Z so that the packed
R is e modulo t. A multiple1100 in the radix count also forces55 to
divideR, hence p=R=55u with u=1 modulo4. Taking n=40u and
Y=2^(33u-1) gives the exact dyadic resonance. Strict Pell estimates then
place c/k betweenY andY+1, making both split witnesses positive.
The shared recurrence supplies positive rho=g_I and sigma=g_p-g_I;
the congruence p=e modulo t supplies the positive transport quotient.
The auxiliary index2cp makes the normalized and ordinary strong extensions
integral, and the odd-index residue identities give an integral positive
supplied Bezout coordinate. All six retained factors are +1.

The deleted index quotient is not integral: k-R-1 has remainder25u-1
modulo E, strictly between0 andE. Thus the witness-level failure comes
with full positive zeros at every positive input on the inherited compiler
recipe, including a rejecting program. Infinitely many choices of L are
available. The report's corrected strict Pell bound is only used at indices
at least3; the false strict endpoint at index2 in an earlier note is not
used by this family.

This is an actionable transfer to the current84 source, because deleting
its same four first-index rows leaves an 80-operation candidate. A separate
literal-source successor and proof must pay and verify that transfer; the
historical81/82 counts alone do not establish it. No deletion is incorporated
into the established universal polynomial.

## Report43: valid structural filters, with a superseded open-language label

The three read structural notes prove a useful elementary descent. For
H>=2, N=H v^2-(H-1)y^2 cannot lie strictly between -(H-1) and0;
if0<N<H, it is a positive square. The integral inverse Pell step decreases
v and preserves N until it reaches a diagonal seed. At N=-(H-1), all
nonnegative-v solutions arise from the explicitly described zero seed.
The full product bounds then force a negative auxiliary factor into the
single branch f=1, S=A, Ns=-1, Na=-Delta. The retained five factors are
units in that branch, so the inherited compiler bounds apply. The separate
residue argument excludes it for both odd and even main indices. The
remaining positive auxiliary value is a square dividingDelta. The descent
also makes its square root divide both auxiliary coordinates.

For A even, the represented-divisor classification is also consistent:
a nonzero represented norm dividing A^2-1 is either a positive square or
negative with square complementary divisor. Passing to the squarefree
kernel and squaring the corresponding unit proves the assertion; the
parity of the fundamental unit is essential. This classifies values, not
which values satisfy all other source constraints. Neither evenness ofA
nor squarefreeness ofDelta is asserted for every candidate zero.

The README's open-language status is historical. The later
[odd-prime full collapse](free_coefficient83_prime_outer_collapse.md)
already refutes this free-coefficient83 compiler language and is itself
included in Report46. These structural lemmas remain compatible with that
result. They do not apply automatically to the independent-gamma83 source.
The inner-family and other squarefree addenda were not reviewed in full here.

## Report45: a second full family for the refuted square/product chart

The complete counterfamily was read. It treats all three compiler mask
residues modulo3 and uses a sufficiently large power-of-five radix
exponent. The two principal branches set (p,n)=(4u,3u) or(20v,14v);
CRT choices give p=e modulo t, R=3 modulo4 and positive outer slack.
Exact dyadic resonance again supplies positive split witnesses. The
retained first-index and transport factors have the same sign, so their
product is1; the shared input-loader quotient remains positive. Setting
i=1 and the actual square/product strong witness toDelta*c^4+1 gives
both remaining factors +1 with the positive odd-index auxiliary extension.

This is a different construction of full false-input zeros for the exact
82-row source already refuted by the WIP all-input proof. Its even main
rank and sometimes negative matching index/transport signs are useful new
structure. They should not be confused with a normalization theorem for
every zero or with a saving in a valid universal polynomial. The proof's
branch CRT bounds and positivity estimates were cross-read algebraically;
its archived finite receipts were not replayed.

## Report46: exact family height and a scoped even-rank obstruction

The full even-rank proof, source notes, height proof and auxiliary-minimum
proof were read. The even-rank theorem fixes a five-factor outer tuple
with A>=4 even, p even, c=psi_A(p), R odd and retained product1. It
excludes a positive free-coefficient83 auxiliary extension of that tuple.
The proof passes to the fundamental Pell unit rather than incorrectly
assuming every strong solution is a power of A+sqrt(Delta). Its residue
lemma separates odd and even indices modulo chi_a(m), and the gcd with
the square factor ofDelta excludes nonunit positive auxiliary squares.
The exceptional negative branch is excluded by parity. The small-norm
lemma used here was read directly in Report43. This does not contradict
the odd-prime full counterfamily, which changes the outer tuple.

For the Report45 family, put L=p+yexp+1, C=(p-1)L, and
N=(R-1)(2pL-1). The largest of all18 witnesses is y_aux, and

    2^N < y_aux < 2^(N+1),   bit_length(y_aux)=N+1.

The uniform error estimate uses exponents at most4p^2 and
4p^2*2^(1-p)<=1/32 for p>=16. It gives strict bounds for the
auxiliary pair, the supplied Bezout coordinate, and the other witnesses;
the proof includes11 exact bit lengths and7 certified upper bounds.
Its exact cubic expressions have leading coefficient4/3 or25/14 inR.
With R near2^(4t), the witness value is doubly exponential in t and,
eventually for a fixed compiler, in the numerical input x. This does not
mean doubly exponential in the binary input length: the input convention
matters. The stepwise choice t=5^r cannot be replaced by one smooth
constant multiple ofx in a leading asymptotic.

The auxiliary-minimum argument keeps the entire outer tuple fixed. Since
8 dividesc and0<R<c/2, the admissible positive odd indices are R or-R
moduloc, and the smallest isR. Negative roots fail the literal residue.
Allowing every positivei still gives its unique joint minimum at i=1
and auxiliary indexR, by monotonicity of the positive Pell expansions.
This is not a lower bound on all witnesses of the polynomial or all outer
families. The subsequent analytic logarithm/inverse expansions and their
claimed precision were not reviewed here.

The useful consequences for this search are therefore a full obstruction
to first-index deletion, exact filters for free-coefficient factor values,
and controlled witness-size information for one already-refuted chart.
None changes the established84 bound or resolves gamma83.

## Independent provenance and scope cross-read

A second reviewer reloaded all five historical blobs and independently
verified408 member hashes, all16 declared full-read hashes and line counts,
and48 exact current-WIP byte matches. The full note was cross-read, including
Report41 and the current source/cost distinctions. Its historical normalized81
ledger is46M+35A; the corrected table above preserves that distinction from
the current80=45M+35A successor. This second read does not independently
recertify the unread Report39 analytic dependencies or every argument in
Reports43/45/46. No archive code was executed.

The separate [current80 successor](complete80_first_index_deletion_collapse.md)
now completes the literal transfer described above; its
[independent review](review_complete80_first_index_deletion_collapse.md)
and installed normal/optimized receipts pass.
