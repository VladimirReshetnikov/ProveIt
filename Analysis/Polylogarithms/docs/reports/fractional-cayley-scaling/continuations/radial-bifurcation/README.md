# A unique quartic transition and radial bifurcations

**Research continuation for Vladimir Reshetnikov's ProveIt project — 10 October 2026.**

The 18-page article is `article/radial_bifurcation.pdf`. Its modular source is
`article/radial_bifurcation.tex`; `article/radial_bifurcation_standalone.tex`
contains the complete source in one file.

## Results

For `F_{a,b}(z) = sum_{n>m>=1} z^n/(n^a m^b)`, write the local upper angular
zero as `cos(theta) = rho eta(rho)` and
`eta = mu + K rho^2 + Q rho^4 + R rho^6 + ...`.

The audited manuscript already proves the quadratic threshold `a=A(b)`.
This continuation proves that `Q(A(b),b)` changes sign **exactly once** on
`0<b<1`. Exact arithmetic localizes that transition and proves `R<0` and a
nonzero coefficient-map Jacobian there. The consequences are a complete
local two-parameter turning-point classification, an open region with a
minimum followed by a maximum, a fourth-root onset law, and rigidity of
constant normalized-radius curves for `a>=1, b>0`: only `(a,b)=(1,1)` works.
An explicit rational order pair is separately certified to have at least
two radial extrema. Universal coefficient and Möbius-transport identities
are proved analytically, not inferred from finite tests.

The global quartic theorem uses a complete 2,304-cell cover and 4,609
certified root boxes. Every decisive sign is checked with integer outward
interval arithmetic. The floating-point proposal generator is not trusted
by the verifier. The analytic arguments and arithmetic tail bounds are
written out in the article. This is a computer-assisted proof, not a
proof-assistant formalization. Independent review remains important.

## Replay

Python 3.10 or newer is expected; the recorded replay used Python 3.13.5.
From this directory:

```sh
python code/test_exact.py
python code/verify_global.py
python code/verify_local.py
python code/verify_witness.py
```

These four programs require **only the Python standard library**. They
write fresh receipts in `certificates/`. Do not use `python -O`: the programs
explicitly reject optimized execution because assertions carry proof
obligations. A failed assertion is a failed proof check, not a warning.

Optional exact symbolic regressions require SymPy:

```sh
python code/verify_symbolic.py
```

`code/make_mesh.py` requires mpmath and regenerates rational proposals.
It is **not necessary** for verification and is **not part of the proof**.
The universal identities are established by the article's proofs, not by
extrapolating from the optional finite symbolic regressions.

## Build

With a TeX installation providing the packages named in the preamble:

```sh
cd article
pdflatex -interaction=nonstopmode -halt-on-error radial_bifurcation.tex
pdflatex -interaction=nonstopmode -halt-on-error radial_bifurcation.tex
pdflatex -interaction=nonstopmode -halt-on-error radial_bifurcation.tex
```

The standalone file builds in the same way, using its own filename.
The delivered PDF was built with pdfTeX and reviewed in rendered pages.
A new PDF may differ in metadata even when its mathematical content is
unchanged. See `provenance/validation.json` for the delivered review.

## Integration and scope

`integration/INTEGRATION.md` supplies a placement plan, a namespaced chapter
excerpt, a bibliography item, and a guarded proposed status replacement. No remote
repository files were modified. All source references are pinned to commit
`0707425e155707e53d2892e30c72e54d06c00e5f`.

Global quartic uniqueness is global **in the inner-order parameter along
the quadratic threshold**. The complete turning-point count is **local in
radius and parameters**. The explicit rational example proves **at least
two** extrema in its stated interval, not a global count on the disk.
No claim is made to settle the full-radius integer-outer-order conjecture,
S6/S8 period identities, or constant-curve rigidity below outer order one.
The article proposes seven further research directions.

`SHA256SUMS` pins the delivered contents. Replaying checks rewrites receipts;
modified or regenerated files require their own review and new hashes.
