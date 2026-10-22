# Projected-cross coefficient reduction

## Result

The blank K215 local predicate in package 06 reads only the five-cell cross,
and reads the previous-time symbol only through its `H`-boundary bit. Replacing
full 3-by-3 windows by projected crosses reduces the local alphabet from
1,420,903,358,357,108,792,377 to **87,923,161**. A corresponding explicit native
packing layout gives **b = 5^13, L = 5^15, d = 5^28**, rather than the old
`b = 5^33, L = 5^34, d = 5^67`. The exact binary length of `B - 1` decreases
by **5^39**, and every one of the four coefficient ports has at most `2d` bits.
The coefficients remain very large and are specified by exact finite recipes.

The complete mathematical proof and all coefficient formulas are in
`sections/projected_cross_section.tex`; it is a TeX-ready section requiring amsmath,
amsthm and booktabs, with citations `src06` and `masks`.

## The projection and reconstruction theorem

A projected cross is `(p,left,center,right,following)`, where `p` is the
indicator that the previous-time symbol is `H`. The literal predicate
`blank_helical.local_valid` has no other dependence on that predecessor and
has no dependence on any diagonal corner.

For projected crosses `U,U',U''` at a cell, its right neighbor and its
following-time neighbor, require:

1. `U.center = U'.left`;
2. `U.right = U'.center`;
3. `is_H(U.center) = U''.p`;
4. `U.following = U''.center`.

At cyclic index `i`, with neighbor offsets `-1,-h`, these identities give
`left_i = center_(i+1)`, `right_i = center_(i-1)`,
`following_i = center_(i-h)` and `p_i = is_H(center_(i+h))`.
They reconstruct precisely the data read by the old predicate. Therefore the
projected system and the old periodic cell system have the same existence
condition, for every cyclic length and stride, even when offsets coincide.

Start is `(1,434,435,436,1)`. Its center is the unique initialized head in a
canonical halting rectangle. The first K215 transition writes `1`, moves
right and enters state `93`; the following-time center is therefore headless
`1`. The forbidden selector is `(1,0,437,438,437)`. It is locally valid, but
in any globally consistent word its predecessor would be `H` with following
center `V`, contradicting vertical-bit propagation. It is thus harmless to
reserve and forbid selector 1 as before.

## Why six payload slots suffice

The selector determines six one-hot payloads: predecessor H-bit, left,
center, right, following, and center H-bit. Their alphabet sizes are
`(2,a,a,a,a,2)`, with `a=439`. The last payload is a deterministic projection
of the selected center symbol, rather than an additional independent choice.
The slot exponent offsets are `k+(10,5,4,3,1,7)*a`. Translation by `3a` gives
the two vertical comparisons; translation by `a` gives the two horizontal
comparisons. All other incidences are excluded by the separated support.

The clean clause-band proof is unchanged: a selector total in `[0,k]` with
`2^ell > k+1` is forced to zero or one by the low-digit mask, after which each
payload and anchor bit is forced by parity. Heterogeneous slot sizes do not
affect this argument. Horizontal comparisons propagate occupancy from Start.

The overlap masks contain `3a+2` one-bit targets and the two anchor targets.
Thus the mask population parameter is

`m = 2*popcount(mu) + 3a + 4 = 2ell + 11a + 18 + 2padding`.

The ordinary no-carry bound and four-valued dummy treatment still apply.
All nonanchor support is below the first anchor; only anchors `9M,27M` have
difference `18M`. The two far clause bands cannot both intersect an arbitrary
rotated support. Hence the inherited native proof still forces radix and
whole-cell alignment before interpreting the overlap tests.

The arithmetic ports are `beta=B-1`, `K=DC+B*DR`, `MC`, and the **shifted**
mask `MF=MF_native+B-1`. They must be generated together. The same band
spacing gives `2DC-DR = 3 (mod 5)`, so the inherited dummy-bit tuning of the
actual Pell index still supplies completeness. The canonical low-field mask
check survives because all added payload slots have positive exponents.

## Exact census and checks

The old five-cross census was rerun from the exact K215 table. It checks all
left/right pairs for each of 13 center classes and confirms
38,256,607,897 crosses. Projection divides the noninitial-interior counts by
438, leaves initialization counts unchanged, and multiplies boundary counts
by `2/439`. The exact total is 87,923,161; its class table is in the TeX and
`coefficients/projected_cross_constants.json`.

`code/projected_cross_compiler.py` provides:

- exact finite definitions and scalar geometry, without expanding giant
  coefficients or enumerating the projected alphabet;
- sparse convolution basis checks on four small toy alphabets;
- an **actual-dimension interval-support certificate** covering every
  selector and payload, not a sample of the 87-million-selector interval;
- exact band-separation, anchor-pair and modulus-5 checks;
- cyclic reconstruction checks including coincident strides;
- optional checks of the projected local predicate against the exact raw
  K215 table, with 32 accepting control presentations, 1,144 projected local
  windows and overlaps, and rejection of a 20-step nonhalting truncation.

The archive contains the original package 06 Python helpers in
`evidence/legacy-code/` and the pinned table in `machine/k215.tm`.
Full reproduction from the archive root:

```sh
python evidence/legacy-code/count_blank_alphabet.py --tm machine/k215.tm --output verification/cross_count_full.json
python code/projected_cross_compiler.py --inherited-count verification/cross_count_full.json --legacy-code evidence/legacy-code --tm machine/k215.tm --output verification/projected_cross.json
```

The projected compiler resolves its relative file arguments from the archive
root, so it can also be invoked by absolute script path from any working
directory. The central verifier runs the exact census only in its optional
`--full` mode; its default mode reuses the delivered checked census.

The source table must have SHA-256
`fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090`.
It is 5,542 bytes with exactly its original terminal newline. The GitHub
text materialization initially added an extra terminal newline; this was
detected by the inherited hash check and corrected before any census or
machine check was accepted.

These checks complement the universal proof. They do not produce an
accepting K215 computation, materialize a Pell witness, enumerate all tiles,
or add a Lean/Rocq theorem.

## Calibration and source audit

All source references are pinned to ProveIt commit
`3b201cdea32d2c816f5f3d20734051f25fd3ef14`.

The inspected file
`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` states exactly

```text
blank_halts_iff_zfc_refutation :
  BlankHalts machine215 ↔ BProv ZFCax_s [] Form.fBot
nonhalting_iff_zfc_consistency :
  (¬ BlankHalts machine215) ↔ ¬ BProv ZFCax_s [] Form.fBot
```

It specializes the common endpoint by the dense-table correspondence,
register box lemmas, bootstrap, decoder coverage and source-enumerator
equivalence. The common `KEndpoint.lean` composes blank halting with C222
derivability, C222 derivability with ZF refutation, and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. The files are present
at the pin; this work does not rerun their full dependency builds.

The claimed ZFC-provability is through the ordinary K215 calibration and
arithmetic proofs formalizable in ZFC, not an inference from the metatheoretic
soundness of Lean. The new compiler transformation is a finite local
reconstruction argument plus elementary integer identities. It neither
proves consistency nor requires a consistency assumption. It does not by
itself establish that the equation's solvability is also unprovable under
mere consistency; that stronger independence claim is not made.

The intermediate unprojected five-cross construction gives
`k=38,256,607,897` and `d=5^36`; the archive packages the stronger projected
recipe as its primary result.

## Provenance

The scripts adapt `06-blank67/code/compiler_constants.py`,
`06-blank67/code/blank_helical.py` and its exact census at the pinned commit;
the native carry and alignment argument comes from
`complete75_half_binomial_compiler.md` and the underlying native compiler.
The original repository's MIT-0 license and required notices should travel
with the vendored helpers and table. The new ordinary proof has been supplied
for incorporation in ProveIt. No global optimality claim is made.
