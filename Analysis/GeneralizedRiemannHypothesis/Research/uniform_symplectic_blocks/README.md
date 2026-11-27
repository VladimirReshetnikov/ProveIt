# Uniform rank blindness in rectangular symplectic blocks

Research continuation prepared for Vladimir Reshetnikov, 27 November 2026.

## Main result

Fix a finite field F_q. Let a >= b >= 2 be even and project a uniformly
random symplectic b-frame in a nondegenerate (a+b)-space onto a nondegenerate
a-dimensional summand. Write A for this a-by-b block and U for an iid
uniform matrix of the same size. With d=a-b and
gamma_r = product_{i=1}^r (1-q^(-i)), the theorem proves

    TV(rank A, rank U)
      = gamma_infinity / ((q-1) gamma_d) * q^(-a)
        + O_q(q^(-a-b)).

The constants depend only on q, even when d grows arbitrarily with b.
The full matrix distance satisfies

    TV(A,U) = Delta_q + c_q (q^(-a)+q^(-b))
              + O_q((q^(-a)+q^(-b))^2),

where eta_infinity = product_{i>=1}(1-q^(-2i)),
theta_infinity = product_{i>=1}(1-q^(-(2i-1))),

    Delta_q = theta_infinity (1-eta_infinity) > 0,
    c_q = theta_infinity [q-(q+1)eta_infinity]/(q^2-1) < 0.

The paper gives the stronger signed-law expansions, an exact finite-product
centering, and a uniform theorem for the quadratic defect
J_b-U^T J_a U. The event that this residual is singular is exactly optimal
for distinguishing the full matrix laws. That finite optimality fact was
already in the source and is reproved here as a foundation.

## What is new relative to the inspected source

The source is ProveIt at commit
497c1844e71393df41914f5b783d5dc9a618eb61, especially
Analysis/GeneralizedRiemannHypothesis/Article/sections/spn.tex.
The source's spn:q:symplectic explicitly leaves the fixed positive gap a-b
unresolved. This note resolves it and proves uniformity across all aspect
ratios. The old tall-block bound O_q(q^(b-a)) becomes a sharp leading term
of order q^(-a). The square case, classical iid nullity laws, embedding
counts, and exact residual determinant test are credited as antecedents.

The theorem is unconditional finite algebra. It extends the frame-statistics
method of the GRH project and does not use RH or GRH as a hypothesis.
Worldwide publication priority is not certified by the targeted literature
comparison. The new result is not Lean-formalized.

## Files

- paper.tex and paper.pdf: complete proof, comparisons, examples, and references.
- code/verify.py: exact rational finite-law calculator and 146 parameter checks.
- code/exhaustive_check.py: independent exhaustive enumeration in eight cases;
  includes the genuine field GF(4), implemented as GF(2)[x]/(x^2+x+1).
- code/make_figure.py: reproducible graph of the exact distances.
- results/: exact counts, rational distances, and numerical remainder checks.
- figures/: the scientific figure in PDF and PNG formats.
- SOURCE_AUDIT.md: source scope, pinned revisions, verification evidence,
  and the exact source labels used.
- FORMALIZATION.md: a Lean roadmap with the remaining proof obligations;
  no unchecked Lean code is presented as a completed formalization.
- sources/: source snapshots and original Git blob metadata.
- BUILD_VERIFICATION.txt: manuscript compilation and validation summary.
- SHA256SUMS: checksums of the delivered files.

## Reproduce

With Python 3 and a normal LaTeX installation:

```sh
python3 code/verify.py
python3 code/exhaustive_check.py
python3 code/make_figure.py
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
```

The two verification scripts require only the Python standard library.
The optional figure rebuild requires matplotlib. The figure is included, so
compiling the paper does not require matplotlib. A quick rational check uses
`python3 code/verify.py --quick`; this replaces the results table with a smaller
set, so run without `--quick` to regenerate the full delivered table.

Checksums can be checked on systems with GNU coreutils:

```sh
sha256sum -c SHA256SUMS
```

The exact computations verify finite identities and implementation consistency.
The asymptotic estimates are proved in the paper, not inferred from numerical
fits. No repository was modified or published as part of this delivery.
