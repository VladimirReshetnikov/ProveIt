# Proposed integration into the ProveIt polylogarithm manuscript

## 1. Baseline, provenance, and limits of this update

This guidance is against commit **`3447bc59b78d138a7f0d536b66ac6e5cc5d5e49f`**, inspected on 10 October 2026. Unless otherwise specified, manuscript paths below are relative to `Analysis/Polylogarithms/docs/manuscript/`; package paths are relative to this report's root. The baseline was not modified when preparing this package. Reconcile these suggestions with intervening repository changes before applying them.

The continuation did **not establish any additional displayed baseline formula to be false**. The proposed corrections are updates of proof status and scope. They do not constitute an audit of every formula in the full manuscript. In particular, the baseline's already established rejection of one older frozen `S_8` vector remains valid; the different, later `S_8` candidate remains conjectural.

The earlier warning that the Gaussian maximum alone does not furnish a universal Euler remainder bound is mathematically correct. Preserve that warning as a historical proof dependency. The new positive remainder kernel and its uniform bound supply the missing step. Do not describe the old warning as a mathematical error, or omit the new kernel argument on the ground that the Gaussian maximum was already known.

### Status ledger

| Topic | Status at the pinned baseline or identified predecessor | Status supplied by this package | Scope that remains open |
|---|---|---|---|
| Universal real-order Euler error | Bounds on restricted parameter regions; Gaussian axis maximum known | Optimal constant for every `a,b>0`, every integer `N>=1`; universal `9/8` bound for `N>=2` | Sharp constants for individual later steps; complete parameter-uniform tail asymptotics |
| Displayed golden ladders II and III | Numerical evidence in the canonical chapter | Exact rational-function certificates, weight-five evaluations, and descent through weights 1–4 | Displayed weight-6 through weight-9 candidates; completeness of a numerical period basis |
| Golden ladder I | Analytic proof already available in earlier research | Exact replay and consistency certificate, used in canonical index-24 recombination | No new priority claim for its evaluation |
| Quartic transition | Existence of some transition; diagnostic decimal location | One certified transition in a specified rational rectangle, negative sextic coefficient, local two-turning-point region, fold and radius scaling laws | Global uniqueness of the quartic transition; global count of turning points in the disk |
| Full Cayley relation ideal | Abstract full-ideal quotient structure in the earlier fractional-Cayley report; smaller presentations in the canonical chapter | Explicit all-weight projector with kernel equal to the full specified Cayley shuffle ideal; exact `S_6` target nonmembership | Numerical `S_6` identity; numerical `S_8` identity; relations outside that ideal |

## 2. File placement and label namespaces

Retain the complete original package together, for example as

```
Analysis/Polylogarithms/docs/reports/universal-euler-golden-cayley-continuation/
```

The name is a proposal, not a required repository convention. Keeping `code/`, `data/`, `sections/`, `figures/`, and `verification/` in their relative locations preserves executable artifact paths. Adapt chapter copies for the book, while keeping the report source and records as a provenance snapshot.

| Package source | Suggested manuscript copy | Suggested label mapping |
|---|---|---|
| `sections/02_euler.tex` | `chapters/05-universal-euler.tex` | `eul:*` → `eulglobal:*`; `sec:euler` → `eulglobal:sec:main` |
| `sections/03_golden.tex` | `chapters/03-golden-weight-five-certificates.tex` | `gold:*` → `goldcert:*` |
| `sections/04_turning.tex` | `chapters/05-double-turning.tex` | `turn:*` → `rwfold:*` |
| `sections/05_cayley.tex` | `chapters/04-cayley-normal-form.tex` | `cay:*` labels → `cayproj:*` labels |
| `sections/06_audit_research.tex` | Selective updates in `chapters/10-discovery.tex` | Preserve existing discovery labels; add topic-specific labels only as needed |

Apply a mapping consistently to `\label`, `\ref`, `\eqref`, and any `\cref` arguments in the copied chapter and its cross-references. **Do not blindly replace bibliography keys, original report paths, or the provenance strings inside JSON artifacts.** In particular, `cay:Radford` and `cay:Patras` are citations, not theorem labels. Prefixing `turn:` is prudent because predecessor report sources already use that namespace even though the canonical turning chapter has `rwloc:turn:` labels.

### Concrete input locations

In `chapters/05-certified-computation.tex`, add:

```tex
\input{chapters/05-real-turning}
\input{chapters/05-double-turning}
```

and, later:

```tex
\input{chapters/05-real-euler}
\input{chapters/05-universal-euler}
```

Keep the other inputs in their current order. In particular, `05-subcritical-stieltjes` already precedes both additions, so the inherited Gaussian axis theorem is available before the universal Euler proof.

In `chapters/03-algebraic.tex`, insert

```tex
\input{chapters/03-golden-weight-five-certificates}
```

after the section **“Canonical index-12/20/24 ladders and a $\zeta$-elimination chain”**, immediately before **“The minimal Pisot ladder base”**. This puts the canonical ladder definitions before the new section's final recombination discussion. Earlier displays may forward-reference the new theorem.

In `chapters/04-cyclotomic-quotients.tex`, insert

```tex
\input{chapters/04-cayley-normal-form}
\input{chapters/04-S8-candidate}
```

in place of the current final single `04-S8-candidate` input. This keeps the frozen `S_6` conjecture and its normalization immediately before the new full-ideal calculation.

## 3. Universal Euler theorem

### 3.1 Existing results to retain

In `chapters/05-real-euler.tex`, retain:

- Section `rw:sec:euler`, including the distinction between the signed-kernel region and unrestricted positive orders.
- Theorem `rw:thm:euler`, its exact signed-measure remainder `rw:eq:exacteuler`, and the parameter-dependent constants `rw:eq:Mchoices`. These statements remain valid, and some constants are smaller than the new universal constant on their domains. Do not extend the signed-measure representation into the subcritical region merely because a different positive representation is now available.
- Proposition `rw:prop:weights` and formula `rw:eq:weights`. The finite Euler weights in the new section are the same already established combinatorial identity; a book integration may cite this proposition rather than repeat its proof.
- Theorem `rw:thm:counterexample` and its interval certificates. The unrestricted constant one still fails.
- Proposition `rw:prop:fixedconstant`. Its monotonicity of the *scaled* errors and its fixed-pair optimum are restricted statements. The new theorem proves that the unscaled `E_N` decreases for all positive orders; it does not prove universal monotonicity of `2^N(E_N-g_{a,b})`.

In `chapters/05-subcritical-stieltjes.tex`, retain Theorem `subpick:thm:euler`, formula `subpick:eq:euler-tail`, Corollary `subpick:cor:axis`, Theorem `subpick:thm:fixed-total`, and Theorem `subpick:thm:axis-maximum`. The last theorem already proves uniqueness of the Gaussian axis maximum. Its reproduction as `eul:prop:axis` is inherited material, not a new discovery.

Retain Corollary `subpick:cor:sharp-critical`: the sharp constant `pi/4 + log(2)/2` for positive orders with `a+b<=1` is a separate, stronger restricted-domain statement. The sentence explaining that **this same constant** does not extend to arbitrary supercritical orders remains correct.

### 3.2 Main statement and proof dependencies

The imported theorem `eulglobal:thm:main` gives, for all `a,b>0`,

```tex
0<E_N-g_{a,b}<\frac98\,2^{-N}\qquad(N\ge2),
```

and the optimal all-step bound

```tex
0<E_N-g_{a,b}<C_*2^{-N}\qquad(N\ge1),\qquad
C_* = \max_{b>0}\{\beta(b)+2^{-b}\eta(b)\}.
```

The maximum has the inherited unique maximizer `b_* in (1,2)`. Its approximate value `1.13656110333950956095` is diagnostic. Sharpness follows from `N=1` and `a` decreasing to zero at `b=b_*`. Equality belongs only to the stated boundary extension, not the open positive-order domain.

Do not separate the theorem from these new proof components:

| Package label | Imported label | Role |
|---|---|---|
| `eul:lem:positive` | `eulglobal:lem:positive` | Probability representation valid without a signed-measure threshold |
| `eul:lem:tail`, `eul:eq:tail` | `eulglobal:lem:tail`, `eulglobal:eq:tail` | Exact positive remainder kernel |
| `eul:lem:kernel-gap` | `eulglobal:lem:kernel-gap` | Strict `9/8` bound for every later kernel |
| `eul:eq:mixture`, `eul:eq:mixture-measure` | Corresponding `eulglobal:` labels | Truncated fourth-power mixture for all `N>=4` |
| `eul:eq:P2`, `eul:eq:P3`, `eul:eq:Q4` | Corresponding `eulglobal:` labels | Finite polynomial inequalities supporting the bound |
| `eul:eq:certified-interval` | `eulglobal:eq:certified-interval` | Direct interval budget for evaluations |

The mixture begins at `N=4`, not `N=3`. The proof separately treats `N=2,3`. The measure density is `(-log x)^(a-1)/Gamma(a) dx`; inserting an extra `1/x` would change its moments and invalidate the probability argument.

### 3.3 Suggested replacement for the magnitude-bound warning

Immediately after Theorem `subpick:thm:Gaussian-order`, replace the sentence beginning **“This is a magnitude bound; it is not an Euler remainder constant…”** by:

```tex
This theorem is a magnitude bound. By itself it does not control the
rescaled Euler remainder in parameter regions where the right-endpoint
Stieltjes factorization does not apply. The missing implication is now
provided by the positive remainder kernel of
Lemma~\ref{eulglobal:lem:tail} and its uniform bound in
Lemma~\ref{eulglobal:lem:kernel-gap}. Together with
Theorem~\ref{subpick:thm:axis-maximum}, these prove the unrestricted
optimal constant in Theorem~\ref{eulglobal:thm:main}.
```

This preserves the correct dependency warning while updating what has since been proved.

In the caption of figure `subpick:fig:Gaussian-axis`, replace the final sentence beginning **“The larger global Gaussian maximum does not supply…”** by:

```tex
The larger global Gaussian maximum alone bounds the first Euler error.
The positive-tail kernel bound of
Theorem~\ref{eulglobal:thm:main} supplies the additional control of every
later error and proves that this maximum is the optimal universal
Euler constant.
```

The caption's distinction between diagnostic decimal coordinates and proved bounds should remain.

## 4. Golden formulas II and III, with lower companions

### 4.1 Exact location and status update

In `chapters/03-algebraic.tex`, the section **“Reshetnikov's formulas and their numerical evidence”** contains three weight-five displays just before **“Reconstructing Tito's weight-6 and weight-7 formulas”**. They currently have `\notag` rather than individual equation labels. Identify the second and third by their coefficient vectors:

```
II:  (45000, -16875, -144, 9), at indices (2,4,10,20)
III: (15660, -19440, 7680, 2430, -15), at indices (2,4,6,8,24)
```

Preserve the formulas themselves. Replace the introductory paragraph beginning **“For the three $\Li_5$ golden formulas below…”** by:

```tex
The source reports residuals of approximately $10^{-257}$ for the
three golden weight-five formulas below. Their connection with the
Abouzahra--Lewin ladders is discussed later. The first formula has an
analytic proof in the preceding continuation; the second and third
now have the exact rational-function certificates of
Theorem~\ref{goldcert:thm:main}. Those certificates also prove all their
lower-weight companions through weight one. The earlier residuals
record discovery evidence, whereas the functional identities supply
the proof. No claim of historical priority for the evaluations is made.
```

Retain the existing Abouzahra--Lewin citation. If convenient, add stable labels to the three existing displays and cross-reference them from the imported theorem, but do not reuse a label already assigned to the duplicate theorem display.

### 4.2 Canonical normalization

The section **“Canonical index-12/20/24 ladders and a $\zeta$-elimination chain”** defines `L_12`, `L_20`, `L_24` and the logarithmic completion `tw(n)`. Those definitions and their rational triples remain unchanged. Its displayed values now have functional proofs:

```tex
L_{12}(5)=\frac{67}{6912}\zeta(5),\qquad
L_{20}(5)=\frac{201}{10000}\zeta(5),\qquad
L_{24}(5)=-\frac{1541}{110592}\zeta(5).
```

The exact descent also gives `L_j(n)=0` for `j in {12,20,24}` and integers `1<=n<=4`, using the existing negative-factorial omission convention.

After the explanation that index 24 is obtained by adding `64/3` times the first weight-five formula to the third and dividing by `-15*24^4`, replace **“This supplies the missing notation; it does not provide a new proof…”** and its following low-order sentence by:

```tex
The recombination supplies the canonical notation and is not itself
a proof of the evaluations. The functional certificates in
Section~\ref{goldcert:sec}, together with the earlier proof of the first
ladder, now prove these three weight-five values and the vanishing
$L_j(n)=0$ for $j\in\{12,20,24\}$ and $1\le n\le4$.
The factorial convention above is retained. These downward identities
do not establish the subsequent extrapolations to weights six
through nine.
```

The displayed third formula is **not** the monic index-24 ladder before this recombination. Retain that distinction in tables and status ledgers.

### 4.3 Lower identities and proof artifacts

The imported theorem `goldcert:thm:main` is the most compact complete statement. Its formula `goldcert:eq:all-weights` proves weights one through five simultaneously. The six useful dilogarithm, trilogarithm, and tetralogarithm companions are individually labeled:

```
goldcert:eq:II-two       goldcert:eq:III-two
goldcert:eq:II-three     goldcert:eq:III-three
goldcert:eq:II-four      goldcert:eq:III-four
```

Keep the rational-function proof and endpoint constants with these formulas. It does not differentiate an identity at the isolated point `rho`; it differentiates identities on an open interval before specialization. The weight-five tensor is contracted only to lower weights. The prime-content coordinate of a rational constant such as `2` must remain in the multiplicative vector space; discarding all constant factors would lose logarithmic information.

The exact certificates have 58 nonzero rows for II and 60 for III. The small certificate for I is a replay of an already proved evaluation. The two functions in `goldcert:eq:new-functional-identities` are identities on an interval and may be included in a separate functional-identity inventory, not just a special-value list.

Do **not** change the status of `golden:eq:Li6`, `golden:eq:Li7`, `golden:eq:Li8`, `golden:eq:Li9`, or the later `T(9)` extrapolation. Likewise, `golden:eq:tetra` and `golden:eq:kummer` are not settled by this package. If updating the agenda in `chapters/03-ladder-certificates.tex`, narrow a broad reference to “weight-five through weight-nine golden formulas” only for these now proved families; do not imply that every possible weight-five ladder has been classified.

## 5. Certified radial double turning

### 5.1 Baseline anchors

The existing `chapters/05-real-turning.tex` has section label `rwloc:turn:sec:main`. Keep its quartic formula `rwloc:turn:eq:quartic`, expansion `rwloc:turn:eq:etaexp`, maximum theorem `rwloc:turn:thm:maximum`, minimum theorem `rwloc:turn:thm:minimum`, and existence corollary `rwloc:turn:cor:quarticzero`. These are correct predecessors.

The final paragraph, beginning **“The finite-coefficient diagnostic…”**, reports the approximate pair

```
b = 0.9974937898734204210746055931...
a = 1.0014301809614951381293517294...
```

It then explicitly says these are not certified enclosures and leaves higher radial behavior open. The old decimals remain diagnostic observations, but the new rational interval calculation certifies the nearby transition. Suggested replacement for the final paragraph:

```tex
The finite-coefficient diagnostic located a possible transition near
$b=0.9974937898734204210746055931$ and
$a=1.0014301809614951381293517294$. These original decimal observations
are now supplemented by the rational rectangle in
Theorem~\ref{rwfold:thm:transition}: there is exactly one simultaneous
zero of $K$ and $Q$ in that rectangle. Its sextic coefficient is
strictly negative, and the parameter map $(a,b)\mapsto(K,Q)$ is
nonsingular. Theorem~\ref{rwfold:thm:fold} consequently gives a local
region with two small-radius turning points and the intervening fold.
This is a local uniqueness and local radial classification theorem.
The number of quartic transition points on the entire threshold curve,
and the total number of radial turning points in the full disk,
remain open.
```

### 5.2 New theorem mapping

| Package label | Imported label | Content |
|---|---|---|
| `turn:prop:recurrence` | `rwfold:prop:recurrence` | Convergent implicit expansion and all-order finite recurrence |
| `turn:prop:sextic`, `turn:eq:KQR` | `rwfold:prop:sextic`, `rwfold:eq:KQR` | Explicit coefficients through the sextic term |
| `turn:thm:transition`, `turn:eq:box` | `rwfold:thm:transition`, `rwfold:eq:box` | Certified isolated simultaneous zero of `K,Q` |
| `turn:eq:certified-main`, `turn:eq:qprime` | Corresponding `rwfold:` labels | Rational sign bounds and nondegeneracy |
| `turn:thm:fold` | `rwfold:thm:fold` | Complete classification of sufficiently small positive radii near the certified parameter pair |
| `turn:cor:sextic` | `rwfold:cor:sextic` | Initial decrease at the degenerate pair |
| `turn:cor:splitting` | `rwfold:cor:splitting` | Two-radius square-root scaling on specified parameter paths |
| `turn:cor:fourth-root` | `rwfold:cor:fourth-root` | Fourth-root law on the `Q=0` slice |

The rectangle and sign bounds in the article are certified rational intervals. The proof does not provide a numerical lower bound for the radius of the entire normal-form neighborhood. Do not turn its existential “sufficiently small” quantifier into a plotted finite interval. The radial figure is an illustration of the local model, not an interval certificate for the full zero curve. In particular, the theorem does not prove global uniqueness of `b_dagger` or exclude additional turning points at larger radii.

## 6. Full Cayley projection and the frozen S6 target

### 6.1 Prior work and exact target normalization

In `chapters/04-cyclotomic-quotients.tex`, preserve the basket transformation `s6change:prop:coordinates` / `s6change:eq:identity`, Conjecture `cycloquot:conj:S6`, formula `cycloquot:eq:S6`, and its primitive relation vector:

```
(485683200, -665395200, -36864000, 401080320,
 -258247, 11750400, 109347840, 971366400).
```

The ordered basket is `(S6,g61,g43,g25,pi^7,G*zeta(5),beta(4)*zeta(3),beta(6)*log(2))`. The package's `cay:eq:target` has been checked against this normalization and the two-color `S_6` representation in `harmonic:eq:gaussianMPL` in `chapters/04-depth.tex`.

The existing functional `cycloquot:eq:separating` concerns a restricted presentation and has value `485683200` on that vector. The new coordinate has value `-166348800` on the corresponding explicitly defined formal target. These are different functionals and must not be substituted for one another without their definitions.

The earlier abstract full-ideal quotient theorem is in the associated report

```
Analysis/Polylogarithms/docs/reports/fractional-cayley-scaling/
    sections/cayley_quotients.tex
```

at `cayley:thm:ideal`. Its `integration/S6_SEARCH.md` identifies constructive reconstruction as the next task. The new result supplies that construction; it should acknowledge this predecessor rather than claim the quotient's abstract existence or dimension as new.

### 6.2 Meaning of the new theorem

The all-weight theorem `cayproj:thm:projector` constructs an algebra projector `Pi` on admissible words. Its kernel is exactly

```tex
J=\langle f-Cf:f\in A\rangle_{\shuffle},
```

the full specified Cayley shuffle ideal, not merely the span of finitely many tested rows. The proof uses the Eulerian indecomposable section, its commutation with Cayley and conjugation, and the equivariant endpoint retraction defined by the shifted generators `z+b/2` and `c-b/2`. Killing the unshifted generators `z,c` would not give the required equivariance.

The all-weight argument should remain in the manuscript even if the finite implementation checks are placed in an appendix. Low-weight tests alone do not establish the equality of the kernel with the full ideal. The application `cayproj:prop:separation` has the exact all-weight coordinate lemma `cayproj:lem:coordinate` as a compact proof certificate; the full `S_6` normal form has 3444 nonzero conjugate-paired coordinates.

At the end of the existing `S_6` discussion, after the paragraph beginning **“The weight-seven functional…”**, add:

```tex
The constructive Cayley projector of
Theorem~\ref{cayproj:thm:projector} gives a further obstruction for this
same frozen target. Its kernel is the full ideal generated by the
convergent Cayley relations and all their shuffle multiples.
Proposition~\ref{cayproj:prop:separation} proves that the target is not
in that ideal. This is a formal nonmembership theorem, not a proof
that the numerical period is nonzero. Conjecture~\ref{cycloquot:conj:S6}
therefore remains open; a proof requires relations beyond this
particular ideal. The smaller-presentation functional above remains
valid with its own stated domain.
```

Retain the later candidate `s8new:conj:S8` / `s8new:eq:formula` in `chapters/04-S8-candidate.tex` as a conjecture. Also retain the distinct rejection `research:prop:S8-rejected` in `chapters/10-discovery.tex`; it concerns an older frozen vector. No statement in this continuation proves either `S_6` or the surviving `S_8` candidate.

## 7. Research-program replacements in 10-discovery.tex

### 7.1 “The surviving research programme”

Replace the sentence beginning **“Higher golden ladder certificates and numerical period independence remain open…”** by:

```tex
The second and third displayed golden weight-five evaluations now
have exact functional certificates, including their lower-weight
companions, in Theorem~\ref{goldcert:thm:main}. The displayed
weight-six through weight-nine candidates and numerical period
independence remain open. The $S_6$ candidate remains a concrete
mixed-reduction problem: the constructive projector in
Theorem~\ref{cayproj:thm:projector} now supplies an exact normal form
and a full-Cayley-ideal obstruction for its frozen target.
```

Keep the surrounding proved `S_4` result and the distinction between representations and numerical independence.

### 7.2 “Real-order geometry after the positive-difference theorem”

Retain the paragraph establishing the unrestricted zero-free result and angular uniqueness, and retain the full-radius sign problem for integer `a>=2`. After its sentence about fractional turning points, add:

```tex
The certified double-turning theorem
\ref{rwfold:thm:fold} makes this limitation explicit: near one
nondegenerate zero of the first two radial coefficients there is an
open parameter region with a local minimum followed by a local maximum
at small positive radii.
```

Replace the final passage beginning **“A universal real-order Euler bound above this triangle…”** by:

```tex
Theorem~\ref{eulglobal:thm:main} now proves the optimal universal Euler
bound for all positive orders. The Gaussian maximum alone did not
supply this bound: the positive-tail representation and uniform
later-kernel estimate provide the missing step. Theorem~\ref{rwfold:thm:transition}
also certifies one local quartic transition and its sextic
nondegeneracy, while Theorem~\ref{rwfold:thm:fold} classifies its local
radial unfolding. Global uniqueness of the quartic transition, the
full-radius motion problem, and the Bessel and uniform Lerch
continuations remain further proof problems.
```

The detailed agenda in `sections/06_audit_research.tex` can be selectively incorporated after these updates. It poses further questions rather than treating all listed numerical or structural expectations as theorems. Keep any explicitly labeled conjectures separate from proved consequences.

## 8. Artifacts, bibliography, and book compatibility

### 8.1 Exact records to retain with the proofs

| Topic | Producer or replay | Exact output / review |
|---|---|---|
| Euler polynomials | `code/certify_euler_bound.py` | `data/euler_polynomial_certificate.json` |
| Independent Euler replay | `code/review_euler_certificate.py` | `data/euler_independent_review.json` |
| Double turning | `code/certify_double_turning.py` | `data/double_turning_certificate.json` |
| Golden certificates | `code/certify_golden_ladders.py` | `data/golden_rational_certificates.json`, `data/golden_certificate_verification.json` |
| Cayley projector | `code/cayley_projection.py`, `code/verify_cayley_projection.py` | `data/cayley_s6_normal_form.json`, `data/cayley_projection_verification.json` |
| Independent Cayley proof review | No numerical period evaluation required | `verification/cayley_independent_review.md` |

The Euler producer and double-turning certificate use exact rational arithmetic; the independent Euler reviewer and golden producer require SymPy. The golden script also uses mpmath for separately identified numerical diagnostics. The Cayley implementation uses rational arithmetic, with no numerical period evaluator or rank solver in its independent-cut replay. See the package README and script headers for current commands and dependencies.

The scripts resolve outputs relative to the package root. Preserve that layout, or deliberately adapt paths and record the adaptation. Keep exact records distinct from floating-point illustrations. If a chapter label is renamed during integration, an original JSON provenance string naming `cay:eq:target` still refers correctly to the archived report source; it should not be silently rewritten as though the original artifact used the imported label.

### 8.2 Bibliography reconciliation

The book uses `references.tex`, not a BibTeX `.bib` file. Merge individual entries from this package's `references.tex`; do not copy a second `thebibliography` environment into an included chapter.

| Report citation key | Book integration |
|---|---|
| `Gangl` | Reuse existing `golden:Gangl2013` |
| `AbouzahraLewin` | Reuse existing `golden:AbouzahraLewin1985` where needed |
| `cay:Radford` | Reuse existing `gaussian:Radford` |
| `cay:Patras` | Add a scoped key such as `cayproj:Patras`, using the package's complete Patras 1993 entry |
| `DLMFeuler` | Add a scoped `eulglobal:DLMFEuler` entry for DLMF §3.9(ii) |
| `Williamson`, `McNeilNeslehova` | Add scoped entries if the corresponding historical discussion is imported |
| `Repo` | Replace self-citations by the relevant internal references; retain a pinned provenance reference for the archived continuation where appropriate |

Do not credit the present report with the classical Euler transformation, Radford's polynomial structure, or the Eulerian Hopf-algebra machinery. Keep historical citations and distinguish the constructive specialization and new applications from those foundations.

### 8.3 Macros, notation, and figures

- Do not import the standalone article preamble. The book already defines the theorem environments and macros `\Li`, `\Real`, `\Imag`, `\iu`, `\shuffle`, `\Q`, `\Z`, `\C`, `\R`, `\N`, `\E`, `\dd`, and `\src`.
- The book does not currently load `cleveref`. The simplest adaptation is to replace the few imported `\cref` calls by an explicit `Theorem~\ref`, `Lemma~\ref`, etc. The research-agenda source uses more `\cref` calls; adapt those if importing its prose. Adding `cleveref` is an alternative only after checking the book's existing reference formatting.
- The book's `\lp` means `log(phi)>0`. In the canonical ladder section `ell=log(rho)<0`, while the new proof uses `lambda=log(rho)` and temporarily writes `ell=log(phi)` in its displayed weight-five conclusion. Normalize these locally and explicitly; never substitute `\lp` for a negative logarithm. Keeping `lambda=log(rho)` for the proof and `\lp` for the final weight-five displays avoids ambiguity.
- Do not redefine a global `\R` for the real Rogers function or a global `\C` for the Cayley involution. The literal symbols `\mathcal R_n`, `C`, and `R` in these sections are local notation. If a combined notation table requires distinction, use `\mathcal R_n^{\mathrm{gold}}`, `C_{\mathrm{Cay}}`, and `R_{\mathrm{rad}}`, with a corresponding local explanatory sentence.
- The golden constant `rho` and the radial variable `rho` occur in separate sections; restate their meanings on entry. The radial sextic coefficient `R` and the Euler scaled remainder `R_N` are likewise separate objects.
- Adjust `\includegraphics` paths when copying chapters. The new Euler figure is `figures/euler_axis.pdf`; the local radial model is `figures/radial_local_model.pdf`. Either copy them under distinctive manuscript filenames or point to the preserved report directory. Retain the captions' distinction between illustrations and exact certificates.
- Adapt `\src{code/...}` and `\src{data/...}` citations in copied chapters to the actual archived report paths, or state the report-root convention once. Paths in the untouched archived source remain relative to its own root.

### 8.4 Focused checks after future integration

Run the package's exact verifiers in the preserved report layout, compile the book enough times to resolve labels, and check for undefined or multiply defined references. Reconcile the result inventory and research-status summaries in the manuscript README and any repository ledger that indexes these chapters. Preserve the earlier receipts as predecessor records rather than overwriting them with later theorem claims.

The necessary mathematical status checks are specific: the universal Euler question is resolved; golden II/III and their downward companions are proved; the radial uniqueness assertion is local; the Cayley result is full-ideal formal nonmembership; `S_6`, the surviving `S_8`, displayed golden weights 6–9, and global quartic-transition uniqueness remain open.
