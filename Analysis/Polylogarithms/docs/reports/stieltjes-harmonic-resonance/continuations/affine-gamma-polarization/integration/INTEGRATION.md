# Additive integration instructions

Suggested location:
`Analysis/Polylogarithms/docs/reports/stieltjes-harmonic-resonance/continuations/affine-gamma-polarization/`.

Keep the modular article as the editing authority and regenerate standalone.tex
and the PDF after changes. The standalone file is a convenience, not an
independent source to edit in parallel.

## Canonical manuscript additions

1. After the canonical integration-by-parts/Gamma parity section, add the
   all-derivative-square theorem and its affine-symbol proof. Preserve the
   Appell primitive lemma: merely introducing the weighted symbol without
   justifying the primitive's coefficient class leaves a proof gap.
2. In the analytic kernels/parameter-primitives material, add the normalized
   beta–Hurwitz transform and Stieltjes endpoint theorem with the exact c_r,
   Pochhammer denominators, joint removable-pole instruction, and anchors.
3. Add the Bernoulli selector identity and functional classification near the
   Hurwitz/Bernoulli material. Preserve the elementary remainder field
   C(s) + 2^(-s) C(s); allowing arbitrary meromorphic coefficients would make
   the classification vacuous.

`manuscript-fragment.tex` is an additive synopsis using `agint:` labels to avoid
conflicting with the full article's `ag:` labels. It states the main additions
and points to their proofs. It does not pretend that a theorem synopsis replaces
the proofs in the article. Bibliography keys should be mapped to local keys when
integrating into the canonical source.

## Required status updates

- Mark the no-additional-u2 square family of the next-Gamma-projection question
  proved, and record the all-r extension.
- Do not mark the full mixed u2,u3 projection proved.
- Preserve attribution of the normal-form decomposition, f0, pure squares,
  and r=2 family to the existing inputs.
- Do not change the unequal-tail optimal-prefix, S6, or revised S8 status on
  the basis of this report.
- Distinguish functional independence over C(s) from numerical independence.

No automatic patch against a changing main branch is provided. A maintainer
should review the source manifest and claim scopes before incorporating text.
