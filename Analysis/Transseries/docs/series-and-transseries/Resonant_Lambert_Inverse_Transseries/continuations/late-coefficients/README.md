# Sharp Late Coefficients and Borel Continuation of Resonant Lambert Inverses

Research contribution prepared for Vladimir Reshetnikov and the ProveIt project, 12 October 2026.

**Main result:** a proof of the hyperbolic late-coefficient conjecture in Section 11.1 of *Double Resonance and Nested Stokes Geometry in Polylogarithmic Lambert Inversion*, with a uniform first correction and an application of nonlinear resurgence that settles the continuation part of Section 11.2.

## Read the article

- [article.pdf](article.pdf) — complete article with proofs, figures, source audit, and eight further research directions.
- [article.tex](article.tex), [sections/](sections/), and [references.tex](references.tex) — complete editable LaTeX sources.
- [PROOF_STATUS.md](PROOF_STATUS.md) — precise claim scopes, dependencies, attribution, and open questions.
- [THEOREMS.json](THEOREMS.json) — machine-readable claim and dependency inventory, keyed to the article's stable labels.
- [INTEGRATION.md](INTEGRATION.md) — proposed destination paths, cross-references, and reviewable replacement prose for the predecessor.
- [integration/predecessor-status-update.patch](integration/predecessor-status-update.patch) — validated amendment to the predecessor, with its build comparison in [integration/validation.json](integration/validation.json).
- [verification/README.md](verification/README.md) — reproducibility and numerical evidence.
- [provenance.json](provenance.json) — pinned repository sources and hashes.
- [BUILD_VALIDATION.json](BUILD_VALIDATION.json) — compilation, PDF inspection, and bundle validation record.
- [SHA256SUMS](SHA256SUMS) — checksums of the packaged files except this checksum list itself.

## Mathematical contribution

Put \(A=4\pi^2\), \(b_n=\Gamma(n)/n\), and
\[
R(t)=-\frac t4+
\sum_{j\ge1}\frac{4\Gamma(2j)\zeta(2j)^2}{2j A^{2j}}t^{2j}.
\]
The formal inverse equation is
\[
V+\frac u2V^2+uR(qe^{-V})=0,
\qquad V(q,u)=\sum_{n\ge1}C_n(u)q^n.
\]

For every fixed \(U>0\), uniformly for complex \(|u|\le U\),
\[
\frac{(-1)^{n+1}A^nC_n(u)}{4ub_n}
=H_{n\bmod2}(\pi^2u)+\frac{K_{n\bmod2}(u)}n+O_U(n^{-2}),
\]
where \(H_0=\cosh\), \(H_1=\sinh\), \(z=\pi^2u\), \(d=A^2/288\), and
\[
K_\epsilon(u)=
\left(du+\frac{1+u}{2}z^2\right)H_\epsilon(z)
+(2+u)zH_\epsilon'(z).
\]
The quotient at zero is removable. For odd \(n\), its normalized remainder improves to \(O_U(|u|n^{-2})\). This gives relative asymptotics uniformly over **all** \(0<u\le U\), including arbitrary positive sequences tending to zero.

The article also proves:

1. A reusable finite-phase transformation law for factorially divergent forward tails. The linear forward coefficient controls the leading action amplitudes; the quadratic coefficient first appears in the next correction.
2. Explicit logarithmic and logarithmic–dilogarithmic Borel boundary models with continuous and continuously differentiable remainders.
3. Genuine singularities at **both** \(\pm4\pi^2\) for every fixed complex \(u\ne0\), including values where a parity amplitude vanishes.
4. Analytic continuation along paths avoiding \(4\pi^2\mathbb Z\), by a checked application of Sauzin's nonlinear closure theorem.
5. Directional 1-summability away from the real directions and an exact sectorial inverse equation.
6. A uniform derivation of the leading inverse Stokes multiplier from the predecessor's exact forward jump.

The proofs of the coefficient results are elementary factorial-convolution and Lagrange-inversion arguments. They do not assume analytic continuation. The analytic continuation and summability statements explicitly use established theorems, cited in the article.

## Relation to the source material

The repository snapshot is:

```text
VladimirReshetnikov/ProveIt
8f5afd4d7565df808359f6a0c22f87f79a119bb9
```

The principal predecessor is the archive
`docs/incoming/Resonant_Lambert_Inverse_Transseries_2026-10-12.zip`.
The two other incoming reports and relevant integrated chapters were reviewed for overlap and context. The scoped audit did not establish a false theorem. The present work strengthens an explicitly stated conjecture and a valid but coarser bound.

This is an unrefereed mathematical contribution prepared with ChatGPT assistance. It contains conventional proofs and executed computational checks. Worldwide priority for each model-specific formula and proof-assistant formalization are not claimed. Full local alien calculus, exact activity of every arithmetic lattice point, and all inverse-index orders remain open.

The exact remainder used here includes the linear term:
\[
R(t)=-t/4+\mathcal R_0(t)
\]
in the predecessor's notation. Retaining that term is essential for the factor \(e^{-Au/4}\).

## Build

A standard TeX Live installation with pdfLaTeX and latexmk is sufficient. From this directory:

```bash
make pdf
```

Or:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

All figure inputs are already included. No bibliography processor, external font download, network access, or shell escape is required.

## Reproduce the computations

The recorded environment is Python 3.12 with the versions pinned in `verification/requirements.txt`. Install those dependencies in your chosen environment, then run:

```bash
python3 -m pip install -r verification/requirements.txt
python3 verification/verify.py
```

The full run evaluates all finite Lagrange summands through index 1,025 in 70 parameter/index cases and performs 5,890 exact finite assertions. Independent 80-digit calculations check selected indices. The main fast calculation requires an extended-range NumPy `longdouble`; it explicitly stops if the platform supplies only ordinary binary64 under that name. See the verification README for portable interpretation of the supplied results and all precision qualifications.

The numerical errors are normalized by the leading hyperbolic amplitude. The secondary truncated precision comparison includes an exact omitted-term bound; the primary coefficient table does not truncate the finite sum. Floating-point diagnostics are not interval certificates.

## Integrate

The proposed standalone destination is:

```text
Analysis/Transseries/docs/series-and-transseries/Resonant_Lambert_Inverse_Late_Coefficients/
```

Copy the package contents together, then add the cross-references and source-status updates described in `INTEGRATION.md`. The report can also be retained as an incoming archive before integration. This deliverable contains no changes to an external repository.
