# Integrated second-order report review

Review date: 2 October 2026. This review was carried out independently of the article's producer, after the separate source-proof audits. It covers the wrapper and all five included proof files, not merely the wrapper. Frozen dependencies were not modified.

## Verdict

The integrated article faithfully establishes the matching second-logarithmic expansion

D_n = C_* F + (7C_*/3) F loglog(n)/log(n) + O(F/log(n)),

its stated monotone inverse consequence, and the explicit finite-height radius expansion with c_*=0.866796245805539952988634807649337371.... No unresolved mathematical gap was found in the integrated proved results. The final conditional next-scale calculation is correctly excluded from the theorem and inverse conclusions.

This is a mathematical research audit, not formal proof-assistant certification or journal peer review. The detailed mathematical justifications remain in the separate lower-construction, upper-calibration, and finite-height-constant audits included alongside this review.

## Complete source coverage

I read all six TeX files listed in the hash block below. The wrapper's exact constants, positive-kernel conventions, terminal factor, and first-hit input agree with the frozen foundation. The input graph includes the finite-height proof through the corollaries file, and the outlook is separately included after the explicit theorem-scope discussion.

The lower-coefficient section retains every substantive part of its audited source: the symmetric good-bridge event, unconditional Bernstein estimates followed by conditioning, independence only between the two complete balanced vectors, global q-window legality, exact total degree, Jensen cancellation, sine-sum estimates, and O(M) error budget. Its rounded-M identities use the corrected O(log n) errors.

The upper-coefficient section preserves the exact finite-n potential, quantitative Legendre bound, explicit logarithmic endpoint cutoffs, polylogarithmic derivative bounds, both complementary-step Chernoff estimates, a uniform row contraction, and exact terminal control. Changing the local tilt-scale notation to a=F/n and b=F/H avoids confusion with the coefficient a_n and does not change any formula.

The finite-height section preserves the independently checked exact transfer amplitude, endpoint Laplace factor 2, full defective critical mass, high-strip subkernel, exponential moments, exact sine-centering tilt, boundary-safe sine extension, and the spectral comparison. The positive finite-matrix radius identification used when passing from a Perron root above/below one to rho_H is the already-proved finite-height input from the frozen dependency, and also follows from the exact positive finite resolvent stated there.

## Independent check of the inverse corollary

Let lambda=log(mu), S=log Y, G(S)=S^(1/3)(log S)^(2/3), and E(S)=G(S)/log S. For n=S/lambda+O(G(S)), the leading deficit scale is

n^(1/3)(log n)^(2/3)=lambda^(-1/3)G(S)+O(E(S)).

The constant shift -log(lambda) in log n has precisely O(E(S)) effect. The effect of the O(G(S)) change in n is smaller: differentiation gives O(S^(-1/3)(log S)^(4/3))=o(E(S)). The next relative factor loglog(n)/log(n) differs from loglog(S)/log(S) by O(1/log S), sufficient at the claimed precision.

Therefore the article's two-sided uniform deficit estimate is valid throughout both proposed integer bracket points. Taking a sufficiently large fixed K makes lambda n-D_n-S negative at the lower point and positive at the upper point. Monotonicity of a_n, proved in the dependency by appending the last letter, brackets N(Y). Integer rounding contributes O(1)=o(E(S)); E(S) tends to infinity. The coefficient is correctly C_*lambda^(-4/3), independently evaluated as

0.893568257650894909124642189453413239213533519....

The corollary is an asymptotic with a diverging error, not an exact integer rounding rule, and the article says so explicitly.

## Conditional outlook and theorem boundary

The proposed third global constant is labelled conjectural in its section title, opening paragraph, displayed equality, and closing explanation. It is not included in the abstract's claimed theorem, main theorem, inverse corollary, or proved finite-height consequence.

The conditional algebra is correct. With Y0=(2v alpha/(3pi^2))^(1/3), the Kepler profile gives ds/y=2du/(pi Y0), integral(1/y)ds=2/Y0, and the weighted average of log y is log Y0-2log 2. Since C_*=alpha/Y0, the proposed first perturbation reduces to

kappa_*=log Y0-2log 3+2c_*
        =-1.94014818313627039209328207137117391494337961....

The missing hypothesis is explicitly stated: the exact local threshold would have to transfer to the global action with o(F/log n) error and no additional contribution at that scale. The article explains that the current lower construction loses O(M), and therefore does not prove this hypothesis. This audit confirms only the conditional algebra and clear separation of scope; it does not certify the conjectured third term.

## Integration corrections and verification

Three transcription/notation issues were found in the initial integrated draft and corrected by the producer before this signoff:

1. The cube-root exponent in M was moved inside the rounding operation, restoring an integer M=round((6A0 n/L)^(1/3))
2. The inverse bracket's literal TeX control-space followed by “pm” was changed to the actual plus-minus command
3. The alias z_*=z was explicitly defined alongside t_*=t

I checked all three corrections in the final sources. I also inspected the corrected rendered pages containing the M definition and inverse bracket, and the rendered conjectural section; those displays are legible and the theorem/conjecture distinction is visible. Separate all-page layout and archive checks are recorded in the release verification materials. The current PDF hash is recorded below to bind this mathematical signoff to the rebuilt article.

## Hash-bound reviewed payload

Any change to these TeX inputs requires reconciliation and a new integrated hash signoff. The values below were computed from the files after all three corrections.

- `a202061-second-order.tex`: `9d0b80ff3555a247425a0f4c76f283b0f951f661fcec85281ffa91bc6365a51d`
- `proofs/lower-section.tex`: `2f7203927382f65b199e8e2f36ceab570e5c67676329c7c62d794c00518f335b`
- `proofs/upper-section.tex`: `18fc5c865df82f7b5833feb202f6fce17e4f772e9c76ba1e53fb074105dc0c52`
- `proofs/corollaries-section.tex`: `ec9d6258e0c72d296d21df3b7b17641db36aac7be7b110ed22ecb8ec9109a792`
- `proofs/finite-height-section.tex`: `fb51eab039ca61d87fcd81ce7c87ce0547426a0012e44ec3a9359d969e85e9c8`
- `proofs/conjectural-outlook.tex`: `c5e9bb8788f97bb0b0fda4402d7f0aca983ec887bfe5450a46ec0224d56e171b`

Reviewed rebuilt PDF `a202061-second-order.pdf`: `71e21cd457c4bb60d5c8a87f76e9c3807458df04c51b0f14f288074179a8426e`
