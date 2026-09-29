# Source and proof audit

Date: September 28, 2026, America/Los_Angeles.
Scope: targeted repository and primary-literature inspection. This is neither
an exhaustive priority search nor an audit of all ProveIt declarations.

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: `74f7f5bdba1aa728b340509701a0fa4e45e8dbf3`
Git tree of that commit: `1fec4a2ce4d660b5a3015deded56a20aff6a3068`.

The relevant material includes:

- `Combinatorics/Ramsey/Lean/DavisEntringerGrahamSimmons1977/`
- `Combinatorics/Ramsey/Lean/LeSaulnierVijay2011/Statements.lean`

The latter contains the count M(n), parity lower recurrences, literature bounds,
and separately named proposition-valued questions. Reading a statement catalogue
does not establish that each declaration has a proof. The article therefore
cites the published mathematical results directly. No repository mutation,
full Lean build, or complete axiom-dependency inspection was performed.

## Primary sources used

1. J. A. Davis, R. C. Entringer, R. L. Graham, and G. J. Simmons,
   *On permutations containing no long arithmetic progressions*, Acta
   Arithmetica 34 (1977), 81–90.
   https://matwbn.icm.edu.pl/ksiazki/aa/aa34/aa3417.pdf
   Role: historical counting problem and parity-splitting construction.
   The lower recurrence is proved independently in Section 2 of this article.

2. Arun Sharma, *Enumerating Permutations that Avoid Three Term Arithmetic
   Progressions*, Electronic Journal of Combinatorics 16(1) (2009), R63.
   https://doi.org/10.37236/152
   https://www.combinatorics.org/ojs/index.php/eljc/article/download/v16i1r63/pdf/
   Role: Theorem 2.8, theta(n) <= 21 theta(floor(n/2)) theta(ceil(n/2)),
   for n >= 3, extended to n=2 by direct evaluation. The theorem was inspected
   in the original PDF, including the rendered page containing it. Its full
   combinatorial proof is imported, not reproduced in the new article.

3. Timothy D. LeSaulnier and Sujith Vijay, *On permutations avoiding arithmetic
   progressions*, Discrete Mathematics 311 (2011), 205–207.
   https://doi.org/10.1016/j.disc.2010.10.006
   Role: connection with ProveIt's corresponding statement catalogue.
   Infinite-permutation density conjectures are not claims resolved here.

4. Bill Correll, Jr., and Randy W. Ho, *A note on 3-free permutations*,
   Integers 17 (2017), A55; arXiv:1712.00105.
   https://arxiv.org/abs/1712.00105
   Role: enumeration and earlier count data. The supplied Python program is
   independently written, but no novelty is claimed for subset-state DP.

5. Boon Suan Ho, *3AP-free permutations have no exponential growth rate*,
   arXiv:2602.13617v1, February 14, 2026.
   https://arxiv.org/abs/2602.13617v1
   https://arxiv.org/html/2602.13617v1
   Role: prior proof that theta(n)^(1/n) does not converge, obtained by
   separating dyadic-ray limits. This result and its numerical separation
   expressions are not claimed as original here. The monotonicity question is
   kept separate and is not solved by the article.

6. Hsien-Kuei Hwang, Svante Janson, and Tsung-Hsi Tsai,
   *Identities and periodic oscillations of divide-and-conquer recurrences
   splitting at half*, arXiv:2210.10968v1 (2022).
   https://arxiv.org/abs/2210.10968v1
   https://arxiv.org/html/2210.10968v1
   Role: general periodic-profile theory, especially Theorem 2.10.
   Sections 3–4 give a self-contained specialization and explicit constants;
   they do not claim invention of this analytic method.

7. The OEIS Foundation Inc., A003407.
   https://oeis.org/A003407
   https://oeis.org/A003407/b003407.txt
   Role: numerical values 0 <= n <= 200. Attribution: Alois P. Heinz, with
   terms through 90 from Bill Correll, Jr., and Randy W. Ho. The supplied
   numerical transcription is used as external input for large-size
   certificates. It is not an independently validated count table beyond 32.

## Claim dependency map

**Basic continuous profile and bounded multiplicative error (Section 3):**
parity lower recurrence + Sharma upper recurrence + elementary interpolation
and a uniformly convergent series. The analytic construction is classical.
No finite count table beyond initial values is needed.

**Complete cluster interval and finite-band bounds (Section 4):**
the profile and continuity. The fact that the interval is nondegenerate uses
Ho's prior result or the independently checked phase-gap certificate.
The numerical endpoints use the published table. They are enclosures, not
exact extrema, and no numerical-record improvement is claimed.

**Exact fundamental period (Section 5):**
profile envelope + 32 strict integer inequalities involving theta(128) and
theta(n), 152 <= n <= 182 + two interval-containment inequalities + elementary
facts about periods of continuous functions. The finite certificate excludes
every noninteger period, not merely a tested finite list of candidate periods.
It does not locate a global maximum or minimum.

**All positive real scale factors (Section 6):**
exact period group + log-Lipschitz modulus to handle flooring + density of
mantissa intervals. The conclusion includes c < 1, with floor(c*n) positive
for all sufficiently large n. The o(n) comparison is required along all n,
not only a selected subsequence.

**Explicit 2:1 gluing gain/loss (Section 6):**
iterated even lower and upper recurrences + two exact integer inequalities
involving published counts at 128, 129, 172, and 192. These subsequences hold
for every integer t >= 0. They do not require enumeration at their large
iterated sizes and do not rely on numerical plots.

**Statistical and sampling results (Sections 7–8):**
continuous nonconstant profile + bounded correction + Riemann-sum arguments
and elementary irrational-rotation equidistribution. All ordinary cutoff
limit laws are identified; they need not all be pairwise distinct. No
absolute continuity or absence of atoms is asserted.

**Local ratio information (Section 9):**
exact toll recurrence and bounded toll. The resulting lower ratio bound
falls below one and hence does not prove monotonicity.

## Executed verification

`verification.json` records a successful run of `python verify.py --max-n 32`:

- all 199 splitting inequalities within the supplied range 2..200;
- the two Ho separation inequalities;
- the exact fundamental-period and explicit-gluing integer certificates;
- exact extremizing-index selection and strict rational root enclosures for
  the three bands [32,64], [64,128], and [100,200];
- independent subset-state counts for every n in 0..32;
- independent direct permutation enumeration for n in 0..8.

All assertions passed. Verification uses Python integers, not floating-point
comparisons, for certificates and extremum selection. Decimal approximations
and the figure have only an explanatory role. A program assertion is not a
Lean kernel proof. The program rejects execution with Python optimization,
which would otherwise remove assertions.

## Remaining uncertainty and nonclaims

The mathematical deductions are presented with proofs but remain unrefereed.
The new period, rigidity, gluing, and statistical statements were not found
in the sources inspected; exhaustive global novelty is not established.
The large externally supplied counts retain their own evidential boundary.
No famous named conjecture is declared solved merely because a related
structural question has been answered. No Lean theorem inventory was changed.

The article explicitly leaves open stepwise monotonicity, sharp profile
regularity, exact extrema, level-set measure, finer correction terms,
optimized enumeration and formal certification. Proposed generating-function
questions are research directions, not proved singularity theorems.
