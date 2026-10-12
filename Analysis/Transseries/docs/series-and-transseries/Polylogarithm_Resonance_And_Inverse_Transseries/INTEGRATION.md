# Proposed ProveIt integration

**Report:** *Resonant Order Jets and Convergent Inverse Transseries for
Polylogarithms and Logarithmically Weighted Tails* (12 October 2026).

**Inspected repository revision:**
[`9ec0f0406afe7a5475b03ff65ed91f7e283979b8`](https://github.com/VladimirReshetnikov/ProveIt/tree/9ec0f0406afe7a5475b03ff65ed91f7e283979b8).
The paths and existing-result comparisons below refer to this revision.
These are proposed integration changes; the repository has not been edited.

## 1. Canonical location

Place this package in one directory:

```text
Analysis/Transseries/docs/series-and-transseries/Polylogarithm_Resonance_And_Inverse_Transseries/
```

Keep `polylogarithm_resonance_and_inverse_transseries.tex` and its PDF
together there, retaining the relative `data/`, `figures/`, and
`verification/` paths. Include the package README, build script, source
provenance, and this integration note. Generated TeX caches and Python
bytecode are unnecessary repository artifacts. The package README supplies
the build and diagnostic instructions.

The Transseries collection is the proposed home because the principal
results concern convergent inverse charts, logarithmic support, uniform
changes of inverse scale, and coefficient asymptotics. Link to this same
report from the Polylogarithms manuscript. Maintaining one canonical copy
keeps the proofs and subsequent corrections synchronized.

## 2. Result map for the repository index

The identifiers below are the current LaTeX labels. Use these when checking
the source; numbered theorem references can change after integration.

| Result | Current source labels | Content and scope |
| --- | --- | --- |
| Resonant order derivatives | `thm:jets`, `eq:alljets` | An exact, normally convergent formula at every positive integer order and every nonnegative derivative order, with the logarithmic polynomial expressed through complete Bell polynomials. This systematically extends calculations already present in the Polylogarithms manuscript. |
| Higher integer weighted inverses | `thm:weighted-inverse`, `eq:corner` | For fixed integers $m\ge2$, $k\ge0$, the deficit with weights $(\log\nu)^k/\nu^{m+1}$ has a convergent inverse logarithmic series. Its degree bound is sharp, and its extreme coefficients have a Fuss–Catalan formula. |
| Uniform weighted order-two transition | `thm:critical`, `cor:firstcritical`, `eq:critical-support`, `eq:first-exp` | A jointly holomorphic inverse chart for every fixed integer logarithmic weight, uniform for the scaled order parameter on any compact real interval. It includes explicit corrections, a recursion, and the first possible exponential block. |
| Global analytic control | `lem:univalence`, `lem:cutgap`, `prop:delta` | Univalence on the principal slit plane for real order $s>1$, a strict cut-modulus bound for integer $s\ge2$, and the resulting inverse continuation needed for coefficient transfer. |
| Higher integer inverse coefficients | `thm:coeff-higher`, `eq:QNcorner`, `eq:higher-leading` | An all-orders coefficient expansion, a sharp bound on logarithmic degree, explicit extreme coefficients, and the corrected leading normalization. |
| Dilogarithmic inverse coefficients | `thm:coeff-dilog`, `eq:cj`, `eq:dilog-first-log` | An all-orders expansion in an exact Lambert variable, a reciprocal-Gamma coefficient formula, a controlled remainder, and conversion to ordinary logarithms. This outer coefficient expansion is asymptotic. |

For the third row, the precise bare inverse is

$$
D_{\epsilon,k}(t)
=\sum_{\nu\ge1}\frac{(\log\nu)^k(1-e^{-\nu t})}{\nu^{2+\epsilon}}
=y,
\qquad T=\log(1/y),\qquad \tau=\epsilon T.
$$

For fixed $k\ge0$ and bounded real $\tau$, the theorem gives the exact
convergent specialization

$$
t=\frac{y}{T^{k+1}}
V_k\!\left(\tau;\frac1T,\frac{\log T}{T},\frac{y}{T^{k+1}}\right),
\qquad
V_k(\tau;0,0,0)
=\left(\int_0^1u^ke^{-\tau u}\,du\right)^{-1}.
$$

This formula makes the parameter window and the fixed-weight assumption
explicit in any repository announcement.

## 3. Proposed index entry and cross-links

### Transseries index

Add a report entry to
`Analysis/Transseries/docs/series-and-transseries/README.md` near the
critical endpoint and slowly varying tail reports. The following is a
ready-to-adapt Markdown entry, with a link relative to that index:

```markdown
### Polylogarithm resonance and inverse transseries

[`Polylogarithm_Resonance_And_Inverse_Transseries/`](Polylogarithm_Resonance_And_Inverse_Transseries/)
contains exact formulas for resonant order derivatives, convergent inverses
of logarithmically weighted polylogarithmic deficits, sharp logarithmic
support and Fuss–Catalan extreme coefficients, and a uniform chart through
order two for each fixed integer weight. It also proves all-order ordinary
inverse coefficient expansions and documents corrections to the inspected
10 February 2025 Krattenthaler–Rivoal note. The fixed-weight bare-inverse
transition provides local analytic progress related to the slowly varying
tail report's Research Question 5; its feedback and joint coefficient
questions remain open.
```

### Polylogarithms literature chapter

Target:
`Analysis/Polylogarithms/docs/manuscript/chapters/11-literature.tex`.

The chapter explicitly records a **historical June 2026 survey**. Preserve
that framing and the historical category of the existing
[MO 160646](https://mathoverflow.net/questions/160646/inverse-of-polylogarithm)
row. Add a dated companion paragraph after the first literature table, or
an equivalent nearby literature note:

> **October 2026 companion result.** The report *Resonant Order Jets and
> Convergent Inverse Transseries for Polylogarithms and Logarithmically
> Weighted Tails* develops convergent local inverse charts at integer
> orders and a uniform transition through order two. It also establishes
> all-order Taylor-coefficient asymptotics for the ordinary inverse and
> identifies normalization and remainder corrections in the inspected
> 10 February 2025 Krattenthaler–Rivoal note. These results provide a
> developed analytic direction related to the inverse-polylogarithm
> literature entry; they do not supply a general elementary expression for
> the inverse function or update the historical answer status of the
> linked discussion.

Link the report title to the canonical directory above and add its
bibliographic entry using the manuscript's existing convention. The
relevant report labels are `thm:critical`, `thm:coeff-higher`,
`thm:coeff-dilog`, and `sec:audit`. Ordinary `\ref` cannot resolve labels
in a separately compiled report; use a report citation unless external
references are deliberately configured.

### Slowly varying tails, Research Question 5

Target:
`Analysis/Transseries/docs/series-and-transseries/Slowly_Varying_Action_Tails_Critical_Transseries/article.tex`,
paragraph **“5. Joint endpoint and slow-variation limits.”**

Its current question asks for $\alpha\uparrow2$ or $\alpha\downarrow1$
jointly with logarithmic tails and coefficient index $n$, including the
interaction with the weight divided by $\log b_n$. Retain the question.
Add a dated companion note after it:

> **Related local analytic progress (October 2026).** The companion
> polylogarithm inverse report proves, for each fixed nonnegative integer
> logarithmic weight, a convergent chart for the bare deficit inverse at
> the lower endpoint $\alpha=1$, uniformly when
> $(\alpha-1)\log(1/y)$ belongs to a compact real interval
> (`thm:critical`). This supplies an analytic component for the joint
> endpoint problem. The feedback equation, its joint coefficient limits,
> growing weights, cutoff laws, and the upper endpoint remain to be
> treated.

The new report uses $k$ for the logarithmic weight and
$\epsilon=\alpha-1$. This notation correspondence avoids confusing the
weight with the integer polylogarithm order. Do not mark Research
Question 5 solved or change the associated probabilistic conclusions.

## 4. Boundary between existing material and proposed additions

All Transseries paths in this table are relative to
`Analysis/Transseries/docs/series-and-transseries/` at the pinned revision.

| Existing material | What this report adds or specializes |
| --- | --- |
| The Polylogarithms manuscript's `chapters/07-tornheim-evaluation.tex` already derives the $s=1$ first order jet; its periodic-collision and Stieltjes chapters use Gamma–harmonic generators and finite-part resonance. | `thm:jets` organizes every positive integer and every derivative order in one normally convergent Bell-polynomial formula. Gamma–zeta cancellation itself is an established input. |
| `Logarithmic_Critical_Endpoint_Lambert_Charts/article.tex`, `thm:lambert`, proves general convergent Lambert charts. `Confluent_Critical_Transseries_Exponent_Two_Boundary/Confluent_Critical_Transseries.tex`, `prop:normal`, `thm:chart`, and `thm:inverse-window`, already handles exact cancellation and uniform confluence near order three. | The implicit-function mechanism and the idea of an exact Lambert core are reused. The additions are the stated weighted support laws, the fixed-weight order-two bare-inverse chart, and the coefficient refinements. `prop:dilog-chart` is a concrete specialization, not a new general inversion principle. |
| `Slowly_Varying_Action_Tails_Critical_Transseries/article.tex`, Section 8 and `thm:chart`, treats exact logarithmic weights at fixed $1<\alpha<2$. | The new critical theorem includes $\alpha=1$ within a uniform bounded scaled-parameter window. It does not establish the full joint coefficient or probabilistic endpoint limit. |
| `Lower_Critical_Endpoint_Cauchy_Cutoff_Condensation/lower_critical_endpoint.tex`, `thm:chart`, and `Lower_Critical_Endpoint_Landau_Transseries/article.tex`, `thm:normal` and `thm:inverse`, study critically normalized feedback problems. | The bare deficit inverse has a different normalization and does not inherit a feedback, moving-fold, or cutoff theorem from the local chart. |
| `Nonlinear_Stokes_Transport_Logarithmic_Inversion/article.tex`, `thm:transport`, supplies analytic inverse transport; `Resonance_Block_Summation_Transseries/article.tex` treats cancellation among Borel singularities. | Ordinary Lagrange inversion and analytic transport are established tools. The new order resonance concerns cancellation of Gamma and zeta poles. No new Stokes, Borel summation, or resurgence theorem is claimed. |

These are additions relative to the inspected material. Worldwide priority
has not been established. The report contains conventional mathematical
proofs and reproducible symbolic and numerical diagnostics; it is not a
Lean formalization, and its numerical checks are not interval certificates.

## 5. Version-specific source-correction notice

The correction concerns C. Krattenthaler and T. Rivoal,
[*On the compositional inverse of polylogarithms*](https://rivoal.perso.math.cnrs.fr/articles/inversepolylog.pdf),
the author-hosted six-page PDF dated **10 February 2025**, with SHA-256

```text
783ed56b45aa2e90cbc26ca92106ccea0ab7ee577e156ad04308448dc65ddd62
```

Let $\ell_s$ be the inverse germ defined by
$\operatorname{Li}_s(\ell_s(w))=w$, let
$a_n^{(s)}=[w^n]\ell_s(w)$, and put $\rho=\zeta(s)$.
The corrected leading equivalents are

$$
a_n^{(2)}\sim-\frac{\zeta(2)^{1-n}}{n^2(\log n)^2},
\qquad
a_n^{(s)}\sim
-\frac{\zeta(s)^{s-1-n}}{\zeta(s-1)^s n^s}
\quad(s=3,4,\ldots).
$$

| Issue in the identified source | Location and correction | Independent support in the report |
| --- | --- | --- |
| Dilogarithm leading constant | Page 4, final dilogarithm simplification: restore the factor $\rho$, changing $\rho^{-n}$ to $\rho^{1-n}$. | `thm:coeff-dilog`; `sec:audit`. |
| Higher integer leading constant | Page 5, the display immediately after $z=1+\rho t/[n\zeta(s-1)]$ retains the Jacobian factor $1/\zeta(s-1)$; the next display drops it. Restore it, so the denominator contains $\zeta(s-1)^s$. | `thm:coeff-higher`; `eq:higher-leading`; `sec:audit`. |
| Dilogarithm relative remainder | Page 4, last dilogarithm display before the higher-order case: the printed $o(\log\log n/\log n)$ is false even after correcting the leading constant. Replace it by $O(\log\log n/\log n)$, or retain the explicit correction below. | `eq:dilog-first-log`; subsection “The dilogarithmic remainder and the contour gap.” |
| Fixed contour-gap justification | In the return-contour argument, endpoints approach $z=1$, where the modulus tends to $\rho$. A fixed positive gap cannot hold on those entire moving arcs. Separate the controlled local tails from remote contour pieces with a fixed gap. | `lem:cutgap`, `prop:delta`, and the fixed-keyhole proof of `thm:coeff-dilog`. |

For the remainder issue, with $\rho=\zeta(2)$, the report proves

$$
a_n^{(2)}=-\frac{\rho^{1-n}}{n^2(\log n)^2}
\left[
1+\frac{-2\log\log n+1+2\log\rho-2\gamma}{\log n}
+O\!\left(\frac{(\log\log n)^2}{(\log n)^2}\right)
\right].
$$

Thus the ratio of the relative correction to
$\log\log n/\log n$ tends to $-2$, which rules out the printed
little-$o$ claim. The contour observation identifies a gap in the stated
uniform argument; the report supplies a proof of the intended negligible
remote contribution. The corrected constants and expansions are proved
independently. This notice makes no assertion about an uninspected later
revision of the external note.

## 6. Continuing the programme

The report's `sec:questions` gives twelve further research directions.
For connections to the existing collection, the most direct next steps are
uniform inverse-coefficient asymptotics as the order crosses two, the
weighted upper-endpoint transition, and extension of the bare-inverse chart
to the feedback and cutoff setting. Large-order growth and possible
summability of the outer reciprocal-logarithm expansion remain separate
questions: convergence of the analytic inverse charts does not settle
them.
