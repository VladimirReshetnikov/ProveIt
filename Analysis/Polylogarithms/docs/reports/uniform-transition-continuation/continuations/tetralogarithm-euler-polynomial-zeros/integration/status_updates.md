# Proposed manuscript status updates

These recommendations use ProveIt commit
`4c173c06cc32c9cea554b39be1837ad2ae897fc1` as the baseline. They describe
results proved in the accompanying article; they do not report edits already
made to the repository. The separate `manuscript_wording.patch` changes only
one unsupported sentence fragment. Preserve existing equation labels when
integrating the proofs, so references from earlier reports remain valid.

## Exact source locations

Paths below are relative to the repository root. An archive member is named
separately from its enclosing ZIP; a label inside an archive is not a label
already integrated into the manuscript.

| Source ID | Repository path and, where applicable, archive member |
| --- | --- |
| M3 | `Analysis/Polylogarithms/docs/manuscript/chapters/03-algebraic.tex` |
| M6 | `Analysis/Polylogarithms/docs/manuscript/chapters/04-cyclotomic-quotients.tex` |
| M8 | `Analysis/Polylogarithms/docs/manuscript/chapters/04-S8-candidate.tex` |
| MS | `Analysis/Polylogarithms/docs/manuscript/chapters/05-signed-kernels.tex` |
| MF | `Analysis/Polylogarithms/docs/manuscript/chapters/05-subcritical-stieltjes.tex` |
| MU | `Analysis/Polylogarithms/docs/manuscript/chapters/05-universal-euler.tex` |
| U | `docs/incoming/ProveIt_Polylogarithms_Research_2026-10-10.zip`; members `polylogarithms_uniform_bounds_20261010/sections/euler.tex` and `polylogarithms_uniform_bounds_20261010/sections/research.tex` |
| C | `docs/incoming/proveit_polylogarithms_research_2026-10-10 (1).zip`; member `polylogarithms_uniform_continuation/article.tex` |

## Results that can be promoted or extended

### Rational tetralogarithm and its cross-base form

**Baseline:** M3, `golden:eq:tetra`, gives the proposed six-argument rational
tetralogarithm relation. Its equivalent cross-base expression is
`golden:eq:kummer`; the surrounding text says a complete proof is still needed.

**New status: proved.** The article's `rattetra:thm:main` proves the exact
identity at arguments $(1/2,1/3,2/3,1/4,3/4,1/9)$. The existing duplication
formulas then prove `golden:eq:kummer` as well. Replace the local assertions
that these two equivalent identities remain proposed with references to this
proof. The proof does not rely on the original numerical search: it uses the
exact cancellation in `rattetra:lem:certificate`, its descent argument, and
the one-parameter identity `rattetra:thm:functional`. The prime $2$ factor
is retained throughout the rational certificate.

Integration text: [sections/02_tetralogarithm.tex](../sections/02_tetralogarithm.tex).
This closes the identified local proof gap; it makes no claim that the
identity is new in the wider literature.

### Sharp late Euler constant and extremizers

**Baseline:** U, `sections/research.tex`, `conj:euler-rate`, asks for

$$
C_N-1\sim cN^{-p},\qquad
p=\frac{\log2}{\log(3/2)},\quad
q=\frac{\log3}{\log2},\quad c=(1-q^{-1})q^{-p}.
$$

The accompanying `sections/euler.tex` already proves $C_N\to1$ in
`thm:euler-asymptotic-budget` and the matching lower bound in
`prop:euler-axis-lower`. Those are prior results, not new contributions here.

**New status: the conjecture is proved.** `lateaxis:thm:sharpasymptotic`
establishes the matching global upper bound, the displayed equivalent, a
second asymptotic term, and the first correction to the maximizing axis
order. `lateaxis:thm:reduction` proves the exact identity

$$
C_N=\max_{b>0}R_N(0,b)\qquad
\bigl(N\ge N_0:=\lceil e^{24}\rceil=26\,489\,122\,130\bigr).
$$

Here $C_N$ is the supremum over positive outer and inner orders. The axis
$a=0$ is a boundary extension: no positive outer order attains that
supremum for these $N$. `lateaxis:thm:unique` gives a unique nondegenerate
axis maximum for every $N\ge2$. `lateaxis:cor:monotone` proves that the
axis maximum decreases and its maximizing order increases with $N$;
hence $C_N$ is eventually strictly decreasing.
`lateaxis:cor:concentration` describes near maximizers at accuracy
$o(N^{-p})$, the scale specifically requested in the incoming discussion.

Integration text: [sections/04_extremal.tex](../sections/04_extremal.tex).
The universal constant in MU, `univeuler:thm:sharp`, was already proved and
should retain its existing attribution and status.

### Fractional all-orders errors and the fixed-total reversal

**Baseline:** MS, `signed:thm:error-polynomial`, proves the complete
logarithmic error polynomial for positive integral orders. U,
`sections/research.tex`, unlabelled paragraph “Fractional-order late Euler
errors”, explicitly asks for the positive nonintegral extension and its
uniform endpoint structure. MF, `subpick:thm:fixed-total`, already proves
strict fixed-total Gaussian monotonicity, which is the first-truncation
comparison used here.

**New status: the requested fixed-order fractional extension is proved.**
`frac:thm:kernel` supplies the compensated representation for all $a,b>0$,
including $a+b\le1$. `frac:thm:density` and `frac:thm:allorders` give the
two sequences of logarithmic powers with remainders uniform on compact
subsets of positive parameter space. The leading coefficient depends only
on $a+b$. `frac:prop:divergence` specifies termination at integral outer
orders and factorial divergence at nonintegral outer orders when the inner
order is a positive integer. An all-orders asymptotic expansion is not a
claim that the corresponding infinite series converges.

**New status: the complete fixed-total comparison is proved.** For
$a\ge1$, `phasefrac:thm:above` proves
$R_N(a,b)<R_N(0,a+b)$ for every integer $N\ge1$.
For $0<a<1$, `phasefrac:thm:unique` proves a unique real truncation
parameter $\nu(a,b)>1$: the difference
$R_s(a,b)-R_s(0,a+b)$ is negative before $\nu$, zero there, and positive
afterwards. Thus the integer comparison reverses once, allowing equality at
one integer. `phasefrac:cor:derivatives` gives the ordered unique zeros of
the successive derivatives of this interpolated difference. The previous
Gaussian monotonicity theorem remains valid; extending its direction to
every truncation would be incorrect for $0<a<1$.

Integration text: [sections/03_fractional.tex](../sections/03_fractional.tex)
and [sections/03b_phase.tex](../sections/03b_phase.tex). The compensation
does not assert the existence of a finite signed measure in parameter
regions where the baseline proves that such a measure fails to exist.

### Polynomial uniform Lerch saturation threshold

**Baseline:** C, `efflerch:thm:explicit` and `efflerch:eq:Kn`, gives the
effective sufficient threshold $576n^2(3n)^{2n-4}$.
`efflerch:prop:mesh` supplies its underlying separation bound, and
`efflerch:cor:growing` gives a logarithmic range of growing indices.

**New status: a polynomial sufficient threshold is proved.**
`polylerch:thm:mesh` gives the Appell mesh bound
$4/[n(n-1)(n-2)]$ for $n\ge3$.
`polylerch:thm:saturation`, with `polylerch:eq:threshold`, proves that

$$
\mathcal K_n=
\left\lceil\bigl(16+6n(n-1)(n-2)H_{n-1}\bigr)^2\right\rceil
=36n^6\log^2 n\,(1+o(1))
$$

suffices, uniformly for $0\le\rho\le1$, for exactly $n$ positive simple
zeros. Their logarithmic location errors are less than $8/\sqrt{k}$.
`polylerch:cor:growing` extends the simultaneous range to
$3\le n\le c k^{1/6}/(\log k)^{1/3}$, for each fixed $0<c<1$ and all
sufficiently large $k$. Integrate this as an improvement of a sufficient
bound, preserving the stronger existing exact results at small indices.

Integration text: [sections/05_lerch.tex](../sections/05_lerch.tex).

## Claims that must remain unresolved

| Target | Exact baseline location | Status after this continuation |
| --- | --- | --- |
| $S_6$ identity | M6, `cycloquot:conj:S6` | Conjectural; no equality certificate is supplied here. |
| $S_8$ identity | M8, `s8new:conj:S8` and `s8new:eq:formula` | Conjectural; proximity certification does not prove equality. |
| Retained $S_{10}$ identity | C, `conj:S10`; proximity theorem `prop:S10-proximity` | Conjectural identity with an already proved proximity enclosure. |
| Retained $S_{12}$ identity | C, unlabelled subsection “A further candidate at weight thirteen”, vector $\mathbf c_{12}$ | Conjectural identity. Keep it distinct from the earlier rejected vector, which the incoming report rigorously disproves. |
| Higher golden identities | M3, `golden:eq:Li6`, `golden:eq:Li7`, `golden:eq:Li8`, `golden:eq:Li9` | Not settled by the rational weight-four proof. Preserve the existing numerical/proposed status. |
| Global axis reduction for every truncation | U, discussion following `conj:euler-rate` | Open for $2\le N<N_0$ in this continuation. The unique axis maximum for these $N$ does not itself prove global axis reduction. The $N=1$ universal problem was already settled. |
| Optimal uniform Lerch threshold | C, discussion following the effective saturation theorem | Open. The polynomial threshold is sufficient; whether the least uniform simplicity threshold equals the endpoint lower bound $n-1$ remains a research question. |

## Wording correction and integration safeguards

Apply `manuscript_wording.patch` against the pinned baseline to soften M3's
claim “imaginary part is no longer elementary at all”. The replacement says
that the displayed transformations do not reduce that part to elementary
constants. The formula `vertical:eq:Im3` is unchanged. The available
transformation does not establish an elementary-value impossibility theorem.

Keep exact algebraic certificates separate from floating-point illustrations.
The late Euler diagnostics support reproducibility but are not the proof of
the infinite asymptotic statements. The article's all-orders statements are
for fixed parameters, locally uniform on compact positive sets; they are not
uniform through $a=0$ or through parameters growing with $N$. Neither the
present threshold $N_0$ nor the Lerch threshold is claimed optimal. No
proof-assistant formalization or global literature-priority claim is made.
