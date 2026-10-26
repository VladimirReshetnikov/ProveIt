# Independent audit

**Retain the 45-line proof-only core; treat the stronger word-tail API and `Fin.pred` representation cleanup as separate options.** Source-level checks and exact patch replay pass. No new Lean code was compiled or kernel-checked.

## Findings

- **Physical order:** `strictMono_fin_eq_self` is a strictly increasing endomap of the *same* finite ordinal, including the empty ordinal. `Equiv.ofBijective` supplies the order isomorphism; `hf.le_iff_le` supplies its order law. The pinned, already imported `Fin.coe_orderIso_apply` supplies value equality and `Fin.ext` lifts it. No positivity assumption, extra helper, or import is introduced. The full production file shrinks from 180 to 156 lines.
- **Coprime cardinality:** the existing `NeZero C0` is precisely what `ZMod.natCast_val` needs. The rewritten negated divisibility statement becomes the existing nonzero projection `hr`; `castHom` and `cast` are definitionally compatible here. No prime, positivity, nonzero-modulus, or Boolean-choice premise is removed. The full file shrinks from 50 to 44 lines.
- **Hs wrappers:** the three directed arithmetic rewrites remove the symbolic `B` and `K` before `decide` sees a goal. The local irreducibility barrier and every `hK` hypothesis remain intact. This does not establish actual kernel residues. Deleting the private helper is included in the full-file 184-to-169-line accounting.
- **Optional predecessor:** `nonStartIndex` changes its definition body to `Fin.pred`; this is not classified as proof-only. The pinned core definition is `subNat 1`, whose value is the original subtraction. A separate original-constructor `rfl` regression is supplied but **uncompiled**. Combining this option with the core saves 52 production lines.
- **Optional marker tail:** the new formula requires `1991 ≤ h < 2011`, retains arbitrary numeric controls, and includes the bare-offset collision at **h = 2008**. The reflected source is `h - 1005 + position e`; in this band only marker1004 can survive. At h1990 the Start tile's west bit at985 is1, so broadening the lower boundary is false: with N1 and zero dummy/marker, the actual convolution is69,752,854,530, not0. The endpoint clients become shorter, but three added helpers cost more: full file259→278 (+19 physical lines; +16 nonblank lines including comments). This is a stronger API, **not** a net source reduction.
- **Withdrawn overlap:** `exists_coordinate`'s cast-projection cleanup duplicates packet p's `SupportDifference.residue_val` technique. It is absent from delivered patches and proposed files; its five lines are not credited.

## Exact compositions

| Production selection | Before | After | Net saving |
|---|---:|---:|---:|
| Proof-only core, 3 files |414|369|45|
| Core plus predecessor, 3 files |414|362|52|
| Core plus word API, 4 files |673|647|26|
| All options, 4 files |673|640|33|

These are complete affected production files, including helper additions/deletions, comments, and blank lines. Prepared regression source and audit tooling are separate artifacts, not hidden production helpers. Do not add the independent physical variants to the combined variant: they are alternatives.

## Replay

From any directory after extracting the packet:

```sh
python3 -B /path/to/packet/audit/check_integrated.py
python3 -B -O /path/to/packet/audit/check_integrated.py
```

The default baseline is `packet/baseline`, with repository-relative paths. In a working checkout only, `--baseline-tree /path/to/upstream` may be passed explicitly. JSON goes to stdout. `--output /explicit/path.json` is the only optional write. No compiler, Git, network, bundled-script import, or incoming executable is used. Substantive checks use explicit exceptions, not Python assertions.

The audit verifies pinned-source SHA256 values, all existing declaration headers, unchanged imports/context commands/definition bodies (except the explicitly named predecessor option), exact patch-to-candidate reconstruction, exact option composition, private-helper deletion, added-helper accounting, and absence of prohibited trust markers. Its comment-aware lexical checks are deliberately not represented as a Lean parser or elaborator.

Finite sanity checks cover19,720 reflected-position cases,60 bare residues,257,140 cyclic cases including N1 and last cells,2,100 cardinality choices, all three small Hs calculations, and50,070 finite endomaps for n0 through6. The word checker separately exercises full weighted models. These are regression evidence, not proofs of universal statements.

## Remaining boundary

Compilation, prepared `rfl` regression elaboration, and `#print axioms` are **NOT RUN**. No Lean elaboration, kernel, axiom, or performance checks were performed in this review. All-old-proposals compatibility is a bounded documentary/source assessment from `catalog`, not a claim that every historical proposal was applied and built together. Current patches preserve the shared API and compose exactly with one another; any historical patch that reworks the same proof must be rebased rather than blindly applied.
