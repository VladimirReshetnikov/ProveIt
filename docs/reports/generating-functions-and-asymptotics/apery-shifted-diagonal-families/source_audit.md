# Source audit and exact scope

Consultation date: **September 20, 2026**. Public pages were retrieved through web
browsing, not inferred from an old recollection of OEIS. This is a source audit,
not an assertion that an OEIS conjecture label establishes worldwide novelty.
The notes below are a selective transcription of the relevant labels and formulas,
not archived copies of the complete pages.

## A143007: the cubic target

Source: https://oeis.org/A143007

The formula field contains the label **“Conjectural result for other diagonals”**
followed by the family proved in Theorem 1.1 of `article.pdf`:

    zeta(3) = H_k^(3) + sum_{n>=1}
      (2*n+k)*(3*n^2+3*n*k+k^2) /
      (n^3*(n+k)^3*T(n-1,n+k-1)*T(n,n+k)).

The comments also describe the extension from the main diagonal as suggested by
calculation. The main diagonal is A005259. The binomial expression in the entry,

    sum_j C(n+j,2*j)*C(2*j,j)^2*C(m+j,2*j),

is termwise equal to the four-binomial definition used in the article. The entry
also supplies the alternative sum checked independently by `verify.py`:

    sum_j C(n,j)^2*C(n+m-j,m-j)^2.

The target is the zeta acceleration family, NOT the separate supercongruence
statement elsewhere in the same entry.

## A108625: the two quadratic targets

Source: https://oeis.org/A108625

The formula field separately labels **“Conjectural result for superdiagonals”**
and **“Conjectural result for subdiagonals”**. These are Theorems 1.2 and 1.3 in
the article. The superdiagonal numerator is `5*n^2+6*k*n+2*k^2`; the subdiagonal
numerator is `5*n^2+4*k*n+k^2`. Their boundary terms are, respectively, `H_k^(2)`
and `2*E_k^(2)`, and the subdiagonal includes the extra factor `(-1)^k`.
Both families are stated for k = 0,1,2,... in the entry.

The entry calls its array T. The article renames it U, retaining the same
coordinates. Its formula field explicitly gives

    U(n,m) = sum_j C(n,j)*C(n+j,j)*C(m,j).

It also gives the alternative expression

    U(n,m) = sum_j C(n,j)^2*C(n+m-j,m-j),

which is checked independently in the supplementary code. The main diagonal is
A005258. The separate supercongruence and other conjectural formulas in this
entry are not addressed by this article.

## Classical sequences

- https://oeis.org/A005258 identifies the three-binomial diagonal as the classical
  Apéry sequence beginning 1,3,19,147,1251,... .
- https://oeis.org/A005259 identifies the squared-binomial diagonal as the classical
  Apéry sequence beginning 1,5,73,1445,33001,... .

The article does not claim to resolve the irreducibility conjectures appearing
in either classical entry. An initially considered square-sum identity in A005258
was NOT selected as the final target and is not represented as proved here.

## Existing literature and priority

**Ofir David, The conservative matrix field**, arXiv:2303.09318v3, 2023.

- Abstract and revision record: https://arxiv.org/abs/2303.09318
- Full HTML consulted: https://arxiv.org/html/2303.09318v3
- Version 3 was revised December 4, 2023.
- Examples 16, 19, and 25 and Section 5 discuss related conservative fields.
  Example 25 displays the same cubic factors up to a sign convention and the
  quadratic pair used here after duality. Its Section 5 establishes convergence
  and relates a diagonal trajectory to Apéry's irrationality argument.

The self-contained scalar finite-sum proof in this archive does not rely on those
matrix-field results as black boxes. Nevertheless, this substantial overlap
precludes any unsupported claim that the method, its polynomials, or all its
consequences originate in this article. An OEIS label can persist after an
identity follows from a broader theorem in the literature.

**Armin Straub, Multivariate Apéry numbers and supercongruences of rational
functions**, Algebra & Number Theory 8 (2014), no. 8, 1985–2008.

- https://arxiv.org/abs/1401.0854
- https://doi.org/10.2140/ant.2014.8.1985

This is cited as context for multivariate Apéry arrays. Its arithmetic theorems
are not required by the three series proofs.

**Roger Apéry, Irrationalité de zeta(2) et zeta(3)**, Astérisque 61 (1979), 11–13.
The bibliography is verified through the records linked from the classical OEIS
entries; the present article does not claim to reproduce that paper's entire
irrationality proof.

## What has and has not been established

Established in the article: all three infinite identities for every fixed
nonnegative integer shift; exact finite identities; error signs and rational
bounds; convergence along all unbounded monotone paths; shifted cubic recurrences;
and sharp fixed-shift leading asymptotic constants.

Not claimed: priority over all prior literature, uniform asymptotics for a growing
shift, a new proof of irrationality from error estimates alone, any formal
proof-assistant certification, or resolution of unrelated conjectures in the
same entries. No OEIS entry was edited during this task.
