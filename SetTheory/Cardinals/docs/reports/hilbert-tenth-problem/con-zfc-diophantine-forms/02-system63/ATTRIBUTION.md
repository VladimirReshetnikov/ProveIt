# Attribution and pinned source provenance

This contribution was prepared with ChatGPT for Vladimir Reshetnikov's
ProveIt repository. Its new work is the fixed blank-input specialization,
the explicit finite coefficient recipe, the reduced ordinary-strong systems,
the sign-adjusted quadratic lift, and the accompanying exposition and checks.
The underlying K215 machine, proof-search construction, Pell encodings,
universal Diophantine compiler, and earlier proof developments are inherited
work and are not claimed as new here.

All ProveIt source references in this appendix use the immutable commit
[`cdd582bec13f908df3711fa9e05d1ddac368a5db`](https://github.com/VladimirReshetnikov/ProveIt/tree/cdd582bec13f908df3711fa9e05d1ddac368a5db).
The machine-readable [PROVENANCE.json](PROVENANCE.json) gives exact repository
paths, pinned URLs, UTF-8 byte counts, and SHA-256 digests for each inspected
source and each preserved notice. The names in its `copy_filename` fields
identify the inspected copies; the pinned repository paths identify the
authoritative upstream sources.

## K215 and its inherited attribution

The exact table is the upstream
[`candidate-k215/k215.tm`](https://github.com/VladimirReshetnikov/ProveIt/blob/cdd582bec13f908df3711fa9e05d1ddac368a5db/Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm),
with SHA-256
`fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090`.
Its accepted ordinary mathematical consistency comparison is inherited;
the new Diophantine specialization does not constitute a new proof-assistant
build of that comparison.

The original [candidate NOTICE](upstream_licenses/candidate-k215/NOTICE.md)
and [candidate provenance](upstream_licenses/candidate-k215/provenance.json)
are preserved verbatim. They identify the partial-selector and
permuted-commands K216 submissions and distinguish their authorship from
the K215 composition, review, and packaging roles. The corresponding
attribution files and inherited notices are preserved under
`upstream_licenses/candidate-k215/provenance/`.

Within their stated scopes, these notices credit Mira and ProveIt,
Elliot Glazer's compact theory K/K230 development, Jeff Ketchersid and
collaborators' busy-beaver/Rocq development, Andrew James Wade's compiler
ancestry, BusyCoq, and the Coq Library of Undecidability. The preserved
original notices specify the precise relationships; this paragraph does
not replace them or assert ownership of their work.

## Diophantine and compiler sources

The principal inherited sources, relative to
`Computability/HilbertTenthProblem/`, are:

| Role | Pinned repository path |
|---|---|
| Reference finite-window compiler | `Papers/verification/explore_fixed_raw_universal_76.py` |
| Modified half-binomial compiler and proof | `Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.py` and `.md` |
| Raw 75-gate proof | `Papers/1980/FIXED_RAW_UNIVERSAL_75_PROOF.md` |
| F84 circuit and scaled-strong proof | `Papers/research-wip/native-stream-queue/complete84_scaled_strong_output.json` and `.md` |
| Asymmetric scale | `Papers/research-wip/native-stream-queue/complete75_asymmetric_scale_tradeoffs.md` |
| Generic strong Pell-rank result | `Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` |
| Signed auxiliary stepdown | `Papers/research-wip/native-stream-queue/complete75_reversed_auxiliary89.md` |
| Normalized strong and coupled index | `Papers/research-wip/native-stream-queue/complete75_normalized_strong87.md` and `complete75_coupled_index_linear88.md` |
| Existing nine-witness theorem | `Lean/Diophantine/Paper1982/NineMain.lean` |

The standalone compiler was compared with the two listed reference
compiler functions. Several earlier reference copies contain one additional
terminal line-feed byte. This changes their file hashes but no executable
or mathematical content. The manifest records both the exact upstream
hash and the inspected copy hash, and identifies every such difference.
The K215 table, raw-75 proof, F84 JSON, asymmetric-scale proof, and generic
strong proof are byte-identical to their pinned upstream sources.

## Terms and preserved notices

The root [ProveIt license](upstream_licenses/LICENSE.ProveIt) is **MIT No
Attribution**, copyright 2026 ProveIt Contributors. Newly prepared material
is intended for incorporation under those repository terms. Inherited
third-party components retain their own terms; this contribution does not
relicense them.

The candidate's complete license directory is preserved under
`upstream_licenses/candidate-k215/licenses/`, including
`LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`,
`NOTICE-original245.txt`, and `SOURCE_PINS.json`. The Wade license is MIT No
Attribution, copyright 2025 Andrew James Wade. All preserved license and
attribution files are byte-identical to the pinned upstream files, and
the four inherited source hashes also match `SOURCE_PINS.json`.

**Relative links inside inherited notices refer to their original source
archive locations.** Those notices are retained without rewriting. To
follow a link whose target is not reproduced in this package, use the
notice's exact pinned upstream path in `PROVENANCE.json` as its base.
Some older predecessor archives are referenced rather than redistributed.
This preserves the original attribution without suggesting that every
historical relative path is a local package path.

No assertion of global minimality, discovery priority, absolute ZFC
consistency, fully materialized astronomical coefficients, or a newly
compiled complete Lean/Rocq endpoint accompanies this provenance appendix.
