# Two newer recurrence interfaces and the missing kernel obligations

This bounded primary-source audit establishes no improvement to the proved
43-operation ternary Pell kernel. It isolates two short arithmetic components,
their exact costs, and the conditions that prevent a direct substitution.
Numerals and comparisons are free; arithmetic with numerals is counted.

The companion is `../verification/explore_modern_kernel_interfaces.py`, with
its adjacent JSON receipt. Its arithmetic counts are for the displayed DAGs,
not lower bounds over all possible constructions.

## 1. What a replacement must actually prove

The current interface in `EXPLORATION_UNIT_TWO_TERNARY_KERNEL.md` takes
positive `D0,r`, under the preliminary conditions

    D0 >= 81, r >= 27, r < 2D0, D0 < r^2,

and establishes both that `D0` is a power of three and that

    D0 divides binom(2r,r).

Its appropriate fixed sign has a complete positive-witness converse for
each parity of `r`. These two conclusions, and the converse, are the paid
interface. Mere exponentially growing solutions, an unspecified recurrence
index, or a formula with exponentiation remaining in it is insufficient.

The earlier `EXPLORATION_RADICAL_PELL_REPLACEMENTS.md` already counts a
general exponentiation construction at51 operations and a norm-four
binomial bridge at69. That note concerns direct expansions, not absolute
lower bounds; this audit does not repeat those expansions.

## 2. A short index congruence with a crucial cutoff

Cantone, Cuzziol and Omodeo, *On Diophantine singlefold specifications*
(2024), Lemma6.2, gives the following criterion in the positive-index
case used here. For `1<=n<a` and
`ell<chi_a(a)`, one has

    ell = chi_a(n)
      iff ell^2 - (a^2-1)(n+(a-1)t)^2 = 1 for some t>=0.

Their Lemma6.1 obtains exponentiation from quotients of indexed Pell
coordinates; Section3's binomial formula retains exponentiation. These
are precise representation interfaces, not a new43-operation implementation.
[Primary paper, pp.599–601](https://lematematiche.dmi.unict.it/index.php/lematematiche/article/download/2703/1218/7841).

The polynomial core of the displayed criterion has a nine-operation DAG:

    a2=a*a; disc=a2-1; am1=a-1; offset=am1*t;
    y=n+offset; y2=y*y; dy2=disc*y2; rhs=dy2+1; ell2=ell*ell.

The final comparison is `ell2=rhs`. This is5 multiplications and4 additions.
Domain conversions and both size conditions have deliberately not been
counted. In particular the cutoff is not a free algebraic comparison: its
right side is itself an indexed Pell value at a variable index.

Here is an exact obstruction to dropping that cutoff. Define the usual
Pell coordinates by

    chi_a(0)=1, psi_a(0)=0,
    chi_a(k+1)=a chi_a(k)+(a^2-1)psi_a(k),
    psi_a(k+1)=chi_a(k)+a psi_a(k).

Reduction modulo `a-1` gives `chi_a(k)=1` and `psi_a(k)=k` modulo `a-1`.
For any `1<=n<a` and integer `s>=1`, take

    k=n+s(a-1), ell=chi_a(k),
    t=(psi_a(k)-n)/(a-1).

The quotient is a positive integer and the nine-operation equation holds,
but `k!=n`. Since `k>=a`, this solution violates precisely the omitted
cutoff. Taking even `s` preserves the parity of the desired index as well.
For example `a=3,n=1,k=5` gives `ell=3363`, `psi_3(5)=1189`, `t=594`,
whereas the intended value is `chi_3(1)=3`.

This family refutes that specific inexpensive replacement. It does not
rule out a new way to certify the cutoff, or a different index test using
information already available in the packed system.

## 3. A short cubic orbit predicate does not expose the index

Dougherty-Bliss, Kenney and Zeilberger, *Creating Decidable Diophantine
Equations* (2024 manuscript; published2025), Definition1 and Theorem1,
describe the integer solutions of the cubic

    PT(x,y,z)=x^3+2x^2y+x^2z+2xy^2-2xyz-xz^2+2y^3-2yz^2+z^3=1

as consecutive triples of the Tribonacci recurrence, extended to integer
indices. The recurrence begins `T0=T1=0,T2=1` and advances by summing
three consecutive terms.
[Primary author manuscript, Section3](https://sites.math.rutgers.edu/~zeilberg/mamarim/mamarimPDF/hilbert10.pdf).
The authors' [publication page](https://sites.math.rutgers.edu/~zeilberg/mamarim/mamarimhtml/hilbert10.html)
records the 2024 manuscript and its appearance in the December 2025
issue of the American Mathematical Monthly, pp. 947–959.

Our factorization is

    PT=(x+2y)(x^2+y^2-z^2) + x*y^2 + z*(x^2-2xy+z^2).

Sharing `2y` with `2xy=x*(2y)` yields8 multiplications and7 additions,
or15 operations. The checker verifies this exact polynomial identity and
its invariance under `(x,y,z) -> (y,z,x+y+z)`.

That count can be useful for a different representation based directly
on recurrence coordinates. It is not comparable to the43-operation
kernel as a complete replacement: the cubic does not mention the desired
index `r`, does not certify a power-of-three scale, and has no supplied
central-binomial residue. Connecting those quantities would require a
new theorem and a paid arithmetic interface. In particular one cannot
identify an arbitrary external input index with the existential orbit
index merely because the triple grows exponentially.

## 4. Exact evidence and current result

The regression verifies the two complete primitive DAGs and their symbolic
residuals;480 wrong-index examples for `2<=a<=16`, including352 that keep
the desired index parity; the exact cubic recurrence invariant; and80
recurrence triples. The wrong-index family in Section2 is proved for all
its stated parameters, separately from that finite evidence.
The local proofs, source and arithmetic counts have received independent
review and fresh runs. Both primary PDFs were also checked directly
against the cited lemma, definition and theorem; the cubic orbit
classification is a cited result, not a new proof established by the
eighty tested triples.

This audit finds no smaller kernel. It leaves a concrete useful question:
can the packed-system bounds supply the exponential index cutoff by a
cheaper independent relation? The cited short core alone cannot do so.
The historical51/69-operation alternatives, the new9-operation incomplete
index core, and the15-operation orbit core have different contracts and
must not be substituted for one another in a universal certificate.
