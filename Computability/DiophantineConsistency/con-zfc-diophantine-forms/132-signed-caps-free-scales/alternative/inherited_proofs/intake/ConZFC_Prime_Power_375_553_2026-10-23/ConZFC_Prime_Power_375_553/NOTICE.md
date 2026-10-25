# Provenance, attribution, and scope

Prepared for Vladimir Reshetnikov's ProveIt project through AI-assisted mathematical research, with ordinary mathematical proofs and independently implemented finite algebra checks.

**Contribution date:** 23 October 2026, Pacific time. Dates embedded in inherited archive names and source records retain their original conventions.

## Immediate parent

The immediate parent is the ProveIt incoming contribution:

```text
ConZFC_407_888_Quartics_2026-10-24.zip
```

It was inspected at repository commit
`ec80841c07e91be8956ce6ed4af9a9c0b782d3d9`.
Its SHA-256 is:

```text
59f847872298260ee35e9d8e4cd0b52d2d78658ac523981fe060e81f40ca4a59
```

The parent is retained under `inherited/parent407/`. Its own notices and the notices of its ancestors remain applicable to their files. Its metadata describes historical snapshots; it is not rewritten to imply that those earlier artifacts originated in this contribution.

## Inherited mathematical and software ingredients

The numerical calculus C222, its calibration to finite ZF and ZFC refutations, the proof-flow interpretation, the eight-column direct certificate, beta coding, arithmetic graph identities, shared Pell construction, and exact coordinate-elimination infrastructure come from ProveIt and its incoming research contributions.

The logical source pin is
`08200eb10fde2db408c69dffd840d6920a569b1f`.
The article identifies the calibration interfaces
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`.
The signed comparison-coordinate Pell argument is credited to the earlier incoming `ConZFC_Shared_Pell_1873.zip` contribution. The present argument further permits signed main abscissas and recovers their orientation from the power congruence.

Classical Pell arithmetic, binomial divisibility, the Chinese remainder theorem, and Legendre's three-square theorem are explicit mathematical dependencies. References and the exact roles of inherited results appear in the article and supplementary proofs.

The new builders reuse the retained parent's arithmetic graph and elimination modules. The independently implemented checkers verify the specific finite transformations and literal coefficient data; the term "independent" does not mean that every inherited logical theorem has been reproved from axioms.

## Changes supplied here

The article and proofs develop the prime-power bounded-row representation, its separate index lift, the linear precision budget, and the signed square-budget compilation. The package materializes the resulting quartics in 375 nonnegative and 553 unrestricted integer variables, with complete residual lists, collected coefficients, inverse certificates, and reconstruction code.

These are defined constructions and measured changes relative to the identified parent. No claim of global simplicity, worldwide priority, or novelty of every general identity is made.

## Licensing and proof status

New code and accompanying documentation are provided under the MIT No Attribution terms in the root `LICENSE`. Retained third-party and inherited notices and licenses continue to apply to their respective files; this notice does not supersede them.

The mathematical proof is ordinary mathematics formalizable in ZFC and uses the explicitly named inherited calibration. This package supplies no new end-to-end Lean/Rocq proof term and no emitted object-language ZFC proof of the final coefficient lists. It neither assumes nor proves Con(ZFC). Its claim is the provable equivalence between consistency and absence of solutions.
