# M1 — a small residual bit-test proof deletion

## Result

`CurrentWordPadding2011.bit3_clear_of_residue` can use its already-imported bit-test APIs directly, deleting **3 physical/code lines and 34 lexical tokens**, with **zero new helpers, imports, statements, assumptions, or witness changes**. This is a routine new-client cleanup, not a new bit-transport interface or a larger mask/carry simplification.

The proposed full module is `candidates/CurrentWordPadding2011.lean`; its sole edit is `patches/bit3_clear_of_residue.patch`. Source pin: `9f35798db4a63c25e435fca14d75931144657d7e`. Source path:

`Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentWordPadding2011.lean:127–134`.

```lean
theorem bit3_clear_of_residue {x : ℕ} (hx : x%2048 ≤ 5) : x &&& 8 = 0 := by
  simpa only [PaddingStaircase.bit3_mask_iff, Nat.testBit_mod_two_pow,
    show (3 < 11) = True from propext (by decide), decide_true, Bool.true_and] using
    (Nat.testBit_lt_two_pow (show x%2^11 < 2^3 by omega))
```

**Uncompiled Lean candidate:** static and finite checks pass, but no Lean invocation, elaboration, kernel validation, axiom check, or performance measurement was performed. All upstream files were left unchanged.

## Why this preserves the exact proof obligation

The supplied inequality bounds the remainder, **not** the full natural number. Put `r = x % 2048`. Since `r ≤ 5 < 8`, `Nat.testBit_lt_two_pow` gives bit three of `r` equal to false. The existing `Nat.testBit_mod_two_pow` identifies that bit with bit three of `x`, because `3 < 11`. Finally, the existing `PaddingStaircase.bit3_mask_iff` translates the bit equality into the literal mask test `x &&& 8 = 0`.

The old proof performed these same steps by introducing a separate equality, changing its modulus syntax, simplifying it, and rewriting the small-remainder conclusion. The candidate simplifies the input proof and the target in one `simpa only`. It uses the same literal numerical comparison and no global simplifier rule.

No restriction `x < 2048` or `x ≤ 5` is introduced: for example `x = 2048` satisfies the theorem, as do arbitrarily large multiples of 2048. The public bound remains **5**, even though 6 and 7 would also clear bit three; the proposal neither strengthens the API nor claims that 5 is sharp. Admitting residue 8 would fail, and changing the modulus to 4 would fail at `x = 8`.

The entire module outside this proof body is byte-identical. In particular, actual source/marker/dummy values, `[NeZero (N*2011)]` and `[NeZero N]` section scopes, at-most-one physical-selector hypotheses, carry normalization, the exact padding interval `1 ≤ h ∧ h ≤ 916`, and all mask conclusions remain untouched. The target theorem itself has only the displayed natural-number argument and residue hypothesis.

## Full helper-inclusive accounting

| Scope | Baseline physical | Candidate physical | Baseline code | Candidate code | Baseline lexical | Candidate lexical |
|---|---:|---:|---:|---:|---:|---:|
| Changed proof body | 6 | 3 | 6 | 3 | 86 | 52 |
| Complete module | 224 | 221 | 175 | 172 | 2587 | 2553 |
| All added helpers/imports | 0 | 0 | 0 | 0 | 0 | 0 |

The tokenizer is the explicitly recorded Python regular expression in `manifest.json` and `verify_masks.py`, after removing comments; it is **not Lean's parser token count**. Comments and blank lines count toward physical lines. All 15 module declaration names are retained. Documentation and checking scripts are research artifacts, not omitted production helper costs.

## Novelty boundary and rejected routes

The baseline reviewer searched both exclusion collections, including complete proposal text and prototype matches. It found no earlier proposal for this exact fresh client. The nearest source precedent is **already present** in `PaddingStaircase.bit3_eq_of_mod16`, lines 28–33: it uses the same `simpa only [Nat.testBit_mod_two_pow, …]` recipe and was also included as baseline source in a previous delivered packet. Therefore the gain is only this specific three-line deletion; bitwise transport is not a new idea.

The final bounded comparison also read late packets **ze and zf** in full at `91dce223cda86c0755b8a9b2504f84be04443fce`, including proposal-bearing notes, all nine Lean prototypes, optional extensions and tentative audit-only directions. No overlap with this bit-test client was found. Exact read evidence and the comparison with the other fifth-iteration candidate families are in `evidence/late91/LATE_REVIEW.md`, `late_review.json`, and `read_manifest.json`. This assigned two-packet review supplements the central corpus ledger; it does not replace its final census.

The following explored routes receive **no delivered candidate or savings**:

- `CurrentWordScalarWitness2011.q_prefix`: replace its predecessor-exponent calculation using `pow_succ` and `Nat.sub_add_cancel`. This exactly repeats E41 in packet f, `report/sections/02_local.tex:145–164`; changing multiplication orientation or using this new client does not supply residual novelty. Its experimental candidate and patch were removed.
- `CurrentWordOrigin2011` and `CurrentWordHighMask2011`: source-zero, aligned-residue, origin-exclusion, and mask-block interfaces are already assumed under E17/E20; no repackaged helper is offered.
- `normalized_padding_residue`: using exact zero incoming/outgoing carries instead of projecting the carry equation modulo 2048 repeats the already-assumed E16 carry/reset interface.
- Generic coherent normalization/witness extraction and scalar quotient/remainder packaging are already assumed under E15/E34 and the late signed-prefix-borrow packet.
- The exact marker-only band 1991–2010 and its exceptional bare term at 2008 were delivered in round four and remain excluded.

## Reproducible evidence

`verify_masks.py` is a newly written, **read-only** Python checker. It imports only the standard library, reads local files, and prints JSON. It never writes a file, invokes Lean, imports or executes repository/incoming scripts, installs packages, or accesses the network.

```sh
python masks/verify_masks.py --baseline-tree baseline
python -O masks/verify_masks.py --baseline-tree baseline
```

From the research workspace, use `--baseline-tree lean_simplification_round5/upstream`. With no argument it searches the sibling `baseline/` and then `upstream/`; there are no hard-coded workspace paths. The final release should supply the five dependency/source files named in `manifest.json` as well as the target source. `--candidate-dir` supports independent read-only mutation checks against a copied candidate directory.

The checker verifies exact source and candidate SHA-256 values, an exact single-body replacement, the unchanged theorem signature and section scopes, unchanged imports and declaration names, all helper-inclusive metrics, five source/dependency hash bindings, the exact unified patch, and absence of the withdrawn scalar candidate. The normal and optimized (`python -O`) runs produce identical results; no correctness check depends on Python `assert`.

Finite tests cover all 2,048 possible low residues across ten high multiples, including one of bit length 257: **20,480** bit/mask/modulus cases, of which **60** satisfy the theorem's exact guard. Additional explicit cases show the danger of admitting residue 8 or a too-small modulus, and the necessity of keeping the full digit unbounded. These finite checks do not prove universal quantifiers or Lean elaboration; they support the exact arithmetic translation being proposed.

Artifacts: `manifest.json`, `validation.json`, `validation_optimized.json`, `verify_masks.py`, the complete candidate, and the unified patch. The retained change has no dependency on the withdrawn scalar proof experiment.
