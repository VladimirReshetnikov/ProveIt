# Sources, exact pins, and attribution

All repository sources below belong to
[VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt).
Paths identify historical inputs; the new Q214 files in this package are
newly generated artifacts and are not asserted to exist at those commits.

## 1. Comparison snapshot and immediate polynomial parent

The comparison snapshot is commit
`02a78a08603cbae248c19c23a75907c6c6bd6443`.

The immediate parent is the source 173 principal equation:

`Computability/DiophantineConsistency/con-zfc-diophantine-forms/173-crt-index-anchor-215/equations/principal/equation.json`

[Pinned parent equation](https://github.com/VladimirReshetnikov/ProveIt/blob/02a78a08603cbae248c19c23a75907c6c6bd6443/Computability/DiophantineConsistency/con-zfc-diophantine-forms/173-crt-index-anchor-215/equations/principal/equation.json).

The exact original 27,732 bytes are retained as
`direct/principal/equation.json`; SHA-256:

```text
8d919a1e5d6a802765b6d010c0140fb1d83c3d36d211b209b7a8d2fb3f3fb6f6
```

Both the producer and independent verifier require this identity. The
changed-row ledger refers to this parent's final integral coordinates.
It does not assume an earlier, unoptimized coordinate convention.

The source 173 comparison figures and its P214/P213 companions are
documented in the
[pinned package README](https://github.com/VladimirReshetnikov/ProveIt/blob/02a78a08603cbae248c19c23a75907c6c6bd6443/Computability/DiophantineConsistency/con-zfc-diophantine-forms/173-crt-index-anchor-215/README.md),
also preserved as `inherited/parent173/README.md`.

## 2. Credit for the inherited source design

The self-power device is already present in source 170:

`Computability/DiophantineConsistency/con-zfc-diophantine-forms/170-quotient-carriers/direct/diagonal_pool/inputs/DIAGONAL_SOURCE_PROOF.md`

[Pinned source 170 proof](https://github.com/VladimirReshetnikov/ProveIt/blob/02a78a08603cbae248c19c23a75907c6c6bd6443/Computability/DiophantineConsistency/con-zfc-diophantine-forms/170-quotient-carriers/direct/diagonal_pool/inputs/DIAGONAL_SOURCE_PROOF.md).
Its bundled copy is `inherited/PRIOR_DIAGONAL_SOURCE_PROOF.md`. This
earlier proof uses F=t^t and explains the shared roles of a large
evaluation value and a binomial shift. The present report credits this
prior design and does not describe self-power as a newly discovered idea.

The range-free C-anchor and the source-polynomial growth interface are
inherited from source 173. The following paths are relative to
`Computability/DiophantineConsistency/con-zfc-diophantine-forms/173-crt-index-anchor-215/`
at the comparison commit:

| Upstream path | Bundled copy | Role |
|---|---|---|
| `proofs/LABEL_SEPARATION_WITHOUT_DERIVED_RANGE.md` | `inherited/parent173/LABEL_SEPARATION_WITHOUT_DERIVED_RANGE.md` | Product separation without a derived-label range, local-size bounds, and the every-prime CRT interface |
| `proofs/C_ANCHOR_THEOREM.md` | `inherited/parent173/C_ANCHOR_THEOREM.md` | Signed anchor classification, orientation, cofinal choice of C, and private Pell witnesses |
| `proofs/RANGE_FREE_ANCHOR_AUDIT.md` | `inherited/parent173/RANGE_FREE_ANCHOR_AUDIT.md` | Review of the inherited range-free anchor construction |
| `proofs/ORDINARY_PROOF_DEPENDENCY_BOUNDARY.md` | `inherited/parent173/ORDINARY_PROOF_DEPENDENCY_BOUNDARY.md` | Precise arithmetic and logical calibration boundary |
| `proofs/PROJECTION_PROOF.md` | `inherited/parent173/PROJECTION_PROOF.md` | Integral projection and reconstruction background for the parent chart |
| `inherited/syntax/SYNTAX_RECODING.md` | `inherited/parent173/SYNTAX_RECODING.md` | Constructor-preserving square-shell recoding, fixing truth 0 and falsity 1 |

These inherited notes retain their historical constants and proposed
variants. The selected new values and the updated proof are specified
by `direct/DIAGONAL_PROOF.md`, `majorant/PROOF.md`, and the report. The
new work changes the growth certificate and its frame binding; it does
not claim the inherited removal of the label range or anchor relocation
as a new contribution.

## 3. Exact square-shell arithmetic source

The constructor source is pinned separately at commit
`953fb4d82d4229f4efc5f9db4cc2bf38ae329bb4`:

`Computability/DiophantineConsistency/con-zfc-diophantine-forms/112-powered-saturation-round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/code/shell_source.py`

[Pinned square-shell source](https://github.com/VladimirReshetnikov/ProveIt/blob/953fb4d82d4229f4efc5f9db4cc2bf38ae329bb4/Computability/DiophantineConsistency/con-zfc-diophantine-forms/112-powered-saturation-round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/code/shell_source.py).

The exact original 2,955 bytes are retained as `majorant/shell_source.py`;
SHA-256:

```text
59c68a354fe5cdbc04bde33720080db2436cb51ae25e3485ac5ae45ff4230199
```

The majorant checker authenticates this file before executing its
`codes_only` path through an independent symbolic builder. It checks the
actual nine axiom expressions and the five additional label-bound
expressions. The resulting 312-node positive arithmetic DAG has diagonal
polynomial degree 524,288. The new certificate is a bound for this exact
source, rather than an estimate inferred from constructor names.

## 4. Logical calibration

The same commit `953fb4d82d4229f4efc5f9db4cc2bf38ae329bb4` pins the
logical endpoint files:

- [KEndpoint.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/953fb4d82d4229f4efc5f9db4cc2bf38ae329bb4/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean), at `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean`.
- [ConstructibleChoice.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/953fb4d82d4229f4efc5f9db4cc2bf38ae329bb4/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean), at `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean`.

The exact named interfaces are

```text
SetTheory.BusyBeaver.ZFC.KEndpoint.c222_iff_zf_refutation
SetTheory.BusyBeaver.ZFC.ConstructibleChoice.zf_refutation_iff_zfc_refutation
```

The logical chain is square-shell C222 refutability, original C222
refutability, refutability of the sealed ZF presentation, and refutability
of the sealed ZFC presentation. The recoding step is a constructor-
preserving effective translation, not equality of the two numeric codes.
The consistency predicate uses the repository's finite proof relation
`BProv`, axiom predicate `ZFCax_s`, and falsity formula `Form.fBot`.

The selected endpoint files are retained in `inherited/logical/`; its
`SOURCES.json` records their identities. They are unbuilt source excerpts
from the larger development. This archive is not a complete Lean import
closure and does not claim a fresh kernel build or a new checked
object-language derivation of the final equivalence. In particular, the
full unbounded C222/ZF calibration remains an explicitly credited
dependency; it is not certified by the polynomial coefficient checker.

| Exact bundled endpoint | Bytes | SHA-256 |
|---|---:|---|
| `inherited/logical/KEndpoint.lean` | 4,004 | `04965b2e82b0f22cdbb11910c17ddf82efafe26123040d6b1b01a88707ec8175` |
| `inherited/logical/ConstructibleChoice.lean` | 2,356 | `3728efadefd93d944836c0f70d18aabbad37274b8c474594b8f01b89dd0eb84c` |

## 5. Inherited arithmetic theorem references

The dependency note identifies the following arithmetic sources at
commit `953fb4d82d4229f4efc5f9db4cc2bf38ae329bb4`:

- `Computability/DiophantineConsistency/con-zfc-diophantine-forms/151-factorial-free-binomial-crt/report/main.tex`: factorial-free binomial-CRT selection, including both directions of prime-power coverage.
- `Computability/DiophantineConsistency/con-zfc-diophantine-forms/135-cofinal-anchors-round17/direct/PROOF_315.md`: the retained signed Pell representation framework.
- `Computability/DiophantineConsistency/con-zfc-diophantine-forms/135-cofinal-anchors-round17/direct/ORIENTATION_FIRST_PROOF.md`: canonical orientation before semantic sign recovery.
- `Computability/DiophantineConsistency/con-zfc-diophantine-forms/135-cofinal-anchors-round17/direct/STRICT_BUDGET_PROOF.md`: strict arithmetic error budgets.
- `Computability/DiophantineConsistency/con-zfc-diophantine-forms/158-pooled-powers/proofs/POOLED_POWERS.md`: pooled power certificates.

These references state the deeper inherited theorem dependencies. Their
entire source trees are not duplicated or rebuilt in this archive. The
new proof specifies exactly where the old interfaces are used and proves
the changed label, growth, radius, parity, and frame conditions.

## 6. Bundled-copy identities

The following SHA-256 values identify the bundled prose copies. Several
copies have an additional final newline relative to their upstream file;
these are **bundled-copy hashes**, not claims of upstream byte identity.
The two exact byte pins for the parent equation and square-shell source
are given separately above.

| Bundled path | SHA-256 |
|---|---|
| `inherited/PRIOR_DIAGONAL_SOURCE_PROOF.md` | `e2b109eb3566f993f49262fd356e419e4aa58530755ffceb2e77f80462c87168` |
| `inherited/parent173/README.md` | `3a6224b0fd4f4f4a314f396b3d932ab8b9279c3a1d06ed2cfe06b0f1bc68bee4` |
| `inherited/parent173/C_ANCHOR_THEOREM.md` | `9bcb27fbfdb7f5f63e850fe32da1db448c1b53e4b70cd1f97acbb4ef256c9ee3` |
| `inherited/parent173/LABEL_SEPARATION_WITHOUT_DERIVED_RANGE.md` | `eef3d2bc4091cdd327ec5b7e9f4410acd335b723c1e4536467d39f03ab38ff70` |
| `inherited/parent173/RANGE_FREE_ANCHOR_AUDIT.md` | `6c24fb48afc00d7782ba114aa68552d021fec07bd855f29d85e41fa7d0157e52` |
| `inherited/parent173/ORDINARY_PROOF_DEPENDENCY_BOUNDARY.md` | `8cf33a75f78a8e092d512054191f6efe9193de294d34318783f6689f75bc80bb` |
| `inherited/parent173/PROJECTION_PROOF.md` | `21d3c957886929787f0169d08e3d8657454434993b75b8b8039a1209dc823eb4` |
| `inherited/parent173/SYNTAX_RECODING.md` | `9d36f423618df90089be613c95cf866e10891476446afd1aaca7893c6bcce496` |

## 7. New artifact identities and attribution

The new equation is `direct/diagonal214/equation.json`, SHA-256:

```text
7ffda8ff6f609918dc3d1824a28ff7188ec8c3ea2be83abb1e4bc5d465fd7894
```

The complete collected expansion is
`direct/diagonal214/expanded_polynomial.json`, SHA-256:

```text
171c6c26f97c0c0846f2aa4c6a8e134db6d4d2d459874b1e3b224bce67a8bcc4
```

The new mathematical contribution and its implementation were prepared
for Vladimir Reshetnikov with ChatGPT assistance. Existing mathematical
constructions, formal developments, and source artifacts remain credited
to their ProveIt contributors and cited antecedents. The package includes
the ProveIt MIT No Attribution license. The separate derivations and
reviews included here are internal AI-assisted work, not external human
endorsements or a claim of worldwide novelty.
