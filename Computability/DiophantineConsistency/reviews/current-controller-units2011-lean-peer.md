# Independent review: actual current rank-step units

Verdict: **PASS**, with no mathematical or interface finding. I independently
read the complete 201-line main and 85-line checks and freshly replayed both
in an isolated overlay. The packet proves unit properties of the actual
rank-step coefficient. It does not prove power-orbit coverage, LTE, safe
mutation, or the remaining equation converse.

The reviewed packet was authored by `controller_certificate`. I authored the
imported `NativeRankVariation` algebra and the separate dummy-mutation packet;
I did not author this unit proof. This review verifies the new arithmetic
composition and its actual coefficient binding, while disclosing that prior
authorship.

## Frozen source and reused dependencies

Paths are relative to `Computability/DiophantineConsistency/`.

| File | SHA-256 |
| --- | --- |
| `Lean/DiophantineConsistency/CurrentControllerUnits2011.lean` | `1c3bdb8af6c4113589b92b76aa895fbee3ecad4ca4d32f8e6290b382bf2f004f` |
| `Lean/DiophantineConsistency/CurrentControllerUnits2011Checks.lean` | `40af856fb4a962ff6650b3a3f74758625377470935e9b7652476c9991a9e0bdf` |

The main directly imports `CurrentKernelResidues2011`, `NativeRankVariation`,
and pinned Mathlib `FieldTheory.Finite.Basic`. I read the complete
`CurrentControllerData2011`, the structural kernel-reindex and final residue
interfaces, the existing full kernel-residue peer review, and the exact
Mathlib `pow_eq_pow_of_modEq` and `ZMod.pow_card_pow` theorems. The complete
843-line finite kernel evaluator was **not** freshly replayed in this review;
its accepted objects and published full-source/finite reconstruction review
were reused. No claim of a fresh literal-table or kernel reconstruction is made.

| Reused module | Source SHA-256 | Reused `.olean` SHA-256 |
| --- | --- | --- |
| `CurrentKernelResidues2011` | `6e6812f7181a4b7fa5c558aef5f369c3068c21870710d522a979c39c877c8f4f` | `91a5c3514338ebe9f0ddbd3069e3928ff61595c332017ba773232b8c2a33063e` |
| `CurrentControllerData2011` | `a86aa5cc6b523bd659df8681012a1a39307ea340c27a7785629d30699ca151ae` | `d3e59650f41406c44c43bd0d702a16b9256f21c1242c6faeb4bbf0439951a7b8` |
| `NativeRankVariation` | `46c226eba0018eb15eaec66bb31b2ea8af7682fbef76d0245ee45c6aa236ef73` | `4d73da3692ddee9ed725396f830bf859743bcbfaaf5c90b6341007bd2f8c9232` |

The reused `reviews/current-kernel-residues2011-peer.md` has SHA-256
`79e352fcfb07254843c67660b1d2f5c22653f9a892e82fa479002f2f194d43b3`.
That prerequisite discharges the earlier controller-data module's explicit
kernel residue premises using the actual unchanged kernel. The new unit
endpoints do not leave any kernel-residue hypothesis to their callers.

## Mathematical and premise audit

The actual constants are `d=47*2011=94517`, `B=2^94517`, and auxiliary prime
`lambda=120199`. For arbitrary independent natural exponents `rw,n`, the
module defines `N=lambda^n`, `q=B^N`, `A=K+B^(lambda^rw)`, and

```
Gamma = radix^977 * (q^2-1) * (1+q*A).
```

`lambda` is 1 modulo both 23 and 402. Those are the checked orders of `B` at
47 and 2011, respectively; the second order is correctly 402, not 2010.
The fixed-prime power reductions follow for every exponent from these
congruences. At the auxiliary prime, an instance of the checked primality
fact permits `ZMod.pow_card_pow`; this is Frobenius, with no LTE or
primitive-root premise. Exponent zero gives dimension one, not zero.

The resulting exact residues are:

| Prime | q | q²−1 | 1+qA |
| ---: | ---: | ---: | ---: |
| 47 | 37 | 5 | 29 |
| 2011 | 1283 | 1090 | 674 |
| 120199 | 37435 | 99282 | 36379 |

The coupling identity retains the original `K` and reduces both independent
power dimensions to `B` before applying the unconditional literal-kernel
residue theorem. It never replaces `K` with a residue-defined port. Natural
subtraction in `q²−1` is justified before casting by `q>1` and hence `1≤q²`.
All three quadratic and coupling residues are nonzero. The remaining factor
`radix^977` is coprime to each odd prime. Multiplication and prime-power
coprimality give exactly
`Nat.Coprime (Gamma rw n) (d*lambda^n)`, then the actual `ZMod` unit statement.
No condition `rw≤n`, divisibility of width into count, or geometric relation
between the two exponents is hidden in these algebraic endpoints.

`Gamma_cast_rankGamma` agrees with the actual signed perturbation factor from
`NativeRankVariation`, including the natural-subtraction side condition.
`Gamma_pos` proves positivity separately. This does not assert that the
ordinary increment stays in a prescribed interval: in particular, independent
exponents can describe a very large width for which a mutation's nonwrapping
bound needs further work.

Focused checks include zero exponents, `rw=17,n=0`, all three residue triples,
the exact signed rank identity, arbitrary-width failure of the special
coupling residue, and `q=1` as a zero-Gamma nonunit control. As supporting
arithmetic only, I independently evaluated all 16 pairs from
`rw,n∈{0,1,2,17}` with Python modular exponentiation using the proved kernel
residues. Gamma reduced to 14, 232, and 93846 at the three primes, each with
gcd 1. This spot check neither imports project code nor replaces the universal
Lean proof or repeats the upstream literal-kernel reconstruction.

## Fresh isolated replay

All reviewed source was read before execution and matched the announced
hashes. The overlay `/tmp/current-controller-units-peer-g987bwf_` excluded the
two reviewed stems and symlinked unchanged prerequisite objects. Main and
checks compiled sequentially with source `Elab.async false` and:

```sh
lean -M6000 -j1 -o /tmp/current-controller-units-peer-g987bwf_/DiophantineConsistency/CurrentControllerUnits2011.olean /home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentControllerUnits2011.lean
lean -M6000 -j1 -o /tmp/current-controller-units-peer-g987bwf_/DiophantineConsistency/CurrentControllerUnits2011Checks.olean /home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentControllerUnits2011Checks.lean
```

Both passed. Main took 4.09 seconds, peak RSS 3,268,556 KiB; checks took 3.02
seconds, peak RSS 3,241,564 KiB. Main emitted the benign existing threshold
warning that exponent 977 exceeds 256 and was not numerically evaluated;
the symbolic proof still compiled. Checks had no warning. All 14 axiom reports
are limited to `propext`, `Classical.choice`, and `Quot.sound`. Neither reviewed
file adds an axiom, `sorry`, or `native_decide`.

Both sources remained unchanged, and both fresh objects were byte-identical
to the shared frozen originals. No shared object, source, documentation, or
git state was modified by replay.

| Artifact | SHA-256 |
| --- | --- |
| Main fresh `.olean` | `2b6f6f8e5766a198e7d66bda90b948f25e72c3f1d574ca9c5df48d2bfb1bcdde` |
| Checks fresh `.olean` | `82a1fecea83f4d12fffa69ff386c7fb7d997780e2fae1f2dc385b38760b471c3` |
| Main replay log | `9b9b8df7692a86b13a383bf5eb63e1f2d5fce6b0e48928b8c6bb3c1d555192fb` |
| Checks replay log | `494f4a082b073203da2c0c5fbff9418130f0f9aa19d04a202c75b3d46653a9a2` |
| `/tmp/current-controller-units-peer-g987bwf_/REPLAY.json` | `b907ce24e6ea6218993d0fe0aa312bdddef3e1b507bde838d270fe8aa5af7382` |
