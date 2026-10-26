# Retained arithmetic proposal: certify the remaining selector residue by Horner evaluation

## Scope and novelty

Review base: ProveIt `7ba7d102822df1eff376cbca913727d9d588ab4e`.
Latest refresh: `3b51c69d42ff99bc420698532af3fe1d1f9bd356`. The common-modulus change is now merged; the current target file was fetched through GitHub and found byte-identical to the comparison base below. Current blob: `bbd8f1d565c646121cf009f985a9cc7eaa1ab231`; current file SHA-256: `f16f792f4449e423bfa6165f81a6b6e3d8c872531b4e428aaf0bebafd178a659`. Therefore the 243-line reduction also applies directly to this latest current source.

Original assumed-applied comparison base: `research/lean-proof-simplification/2026-10-26zn/proposed/Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentKernelResidues2011.lean`.

Packet zn already reduces three separate modular evaluations to one evaluation modulo 47 * 2011 * 120199 = 11360848883. That idea is not claimed again. The new delta removes the remaining 59 checked chunk residues, their 58 length facts, and the explicit assembly rewrite list by refining the evaluation algorithm itself.

The current evaluator and zn's replacement both use

    evaluate r (a :: l) = 2 * a.2 * r ^ l.length + evaluate r l.

Although the source comment calls the finite blocks Horner blocks, this is a direct sum of powers. The proposed accumulator is

    run r [] z = z
    run r (a :: l) z = run r l (z*r + 2*a.2).

The proved invariant is `run r l z = z*r^l.length + evaluate r l`. At z=0, the original evaluator equals the accumulator. The definition of `evaluate`, all literal row data, physical-order interpretation, raw-kernel bridge, common modulus, and modular projection results remain available with their original meanings.

The novelty auditor searched all 43 archived packets and all 7 incoming archives after refresh, including code/patch material. No prior accumulator certificate for this evaluator was found. Closest prior work is zn (modulus sharing), plus generic scanner folds (different source objects and proof obligations). The incremental claim is 59 chunk certificates to one row certificate after zn; never 177 to1.

## Mathematical justification

Induct on l, keeping z arbitrary. The empty case is z=z*1+0. For a::l, apply the induction hypothesis to z*r+2*a.2 and distribute multiplication by r^length(l). The two resulting terms are z*r^(length(l)+1) and the defining head contribution 2*a.2*r^length(l), followed by evaluate r l. Ring normalization proves this identity in the checked helper over a commutative semiring. No property of the numerical rows or modulus enters the invariant.

A single `decide +kernel` then checks the entire 941-element ordered row list at r=10653241607 in ZMod11360848883. The resulting residue is 10463387658, exactly zn's rows_common result. This removes exponentiation and list-length traversal from the computational inner loop. No wall-clock performance improvement is claimed; only successful whole-list kernel replay and source reduction were measured.

## Exact source accounting

- Baseline zn module: 426 physical lines, 18,230 UTF-8 bytes.
- Proposed incremental module: 183 physical lines, 7,465 UTF-8 bytes.
- Net reduction including new helper: 243 physical lines, 10,765 bytes.
- Removed numerical chunk theorems: 59.
- Removed chunk length theorems: 58.
- Replaced rows_common proof:explicit 117-name assembly rewrite becomes `rw [evaluate_eq_run]; decide +kernel`.
- Public evaluate_append retained for compatibility even though this file's numerical assembly no longer uses it.

This is source accounting for one specific post-zn module. It is not an aggregate claim about applying the mutually overlapping entire corpus of proposals.

## Verification and practical limits

The standalone `lean/HornerResiduePilot.lean` compiled successfully with Lean 4.32.0 and mathlib 81a5d257c8e410db227a6665ed08f64fea08e997. It contains the actual 941 pairs copied in exact order from the assumed-applied zn fixture. A separate Python audit compared every ordered pair and chunk concatenation with the CURRENT WangTiles942PhysicalData source. Hash of the canonical compact JSON pair list is 362de053598c3bfa3facee341a6b2fc46a66eda74ecf98904a33c7dd3c9209a8.

Lean printed `run_eq` axioms [propext] and `rows_common` axioms [propext, Quot.sound]. No sorry, axiom declaration, native_decide, or external evaluator establishes the theorem. The numerical Python calculation is only an independent data sanity check.

The full production module and its dependency graph were not rebuilt. The proposed module includes the already-proposed zn edits as its baseline. The patch applies to the latest reviewed current module, which now contains zn's merged common-modulus change; for older snapshots, apply zn first or rebase equivalent code. Run `lake env lean` on the changed module and the project's current-kernel residue checks before adoption. The standalone replay validates the new equality and whole literal numerical certificate; it does not reprove that the literal ordered data correspond to the physical tile table. That semantic bridge remains unchanged and is present in production.

## Rejected candidates

1. One-unsaturated-digit strict Mersenne bound: current CurrentCarryConstruction2011.Facts.word_lt already implements it. Do not include as fresh.
2. Single-nonzero-digit positivity: existing word_pos_of_digit and packet zj already cover this mechanism.
3. Shared modulus for K residues: exact duplicate of zn.
4. Difference-set geometry for Split/Gap exclusion: projected support-difference mechanism already appears in p; additional clients alone are not a novel proposal.

## Artifacts

`lean/HornerResiduePilot.lean`: kernel-checked generic invariant and actual941-row residue.
`evidence/horner/validation.txt`: observed command/version/exit/axiom information.
`patches/current-kernel-horner.patch`: incremental patch against zn's proposed module.
`proposed/DiophantineConsistency/CurrentKernelResidues2011.lean`: complete reviewable module after the incremental change.
`evidence/horner/metrics.json`: exact accounting and ordered-data hash.
`scripts/verify_horner_data.py`: reproducible comparison of fixture rows with the repository.

## Refreshed near-prior disclosure

The newly arrived shape-windows-growth archive records a rejected idea called “affine-monoid Horner chunk assembly.” That item only repackages the old block assembly interface. This retained proposal does not claim such a monoid interface: it changes the executable arithmetic inner loop and successfully replaces all remaining chunk-residue certificates with one kernel check of the unchanged full ordered list. The novelty auditor screened the full fresh archives and retained this narrower distinction.
