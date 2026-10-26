# Independent fifth-iteration audit

**Recommended source reduction: 24 physical / 23 nonblank lines.** Optional
`Gamma_pos` dependency reuse adds 3 / 3, for 27 / 26 across all four files.
These are small new-client proof cleanups, not new mathematical abstractions.
No helpers are added; one private four-code-line transport theorem and its
surrounding documentation/spacing are removed. All counts use complete
affected production files, not hand-picked replacement snippets.

## Results and limits

- `integrated_results.json`: exact pinned-source binding, candidate reconstruction,
  proof-header and complete non-proof-scaffolding preservation, helper-inclusive
  counts, and bounded independent arithmetic checks.
- `integrated_results_optimized.json`: byte-identical result with Python `-O`.
- `portability_results.json`: isolated default-baseline run from an unrelated cwd,
  zero writes by the auditor, and six tampered controls rejected normally and
  with `-O` even when their patches reconstruct their tampered candidates.
- All four patches compose in every one of the 24 possible orders; the recommended
  three compose in all six orders. This is exact textual composition, not Lean
  import/elaboration compatibility.
- **All new Lean remains UNCOMPILED.** No installation, Lean elaboration, kernel
  check, axiom comparison, or performance measurement was attempted. User
  permission is still needed for installation. Python results do not certify Lean.
- The old fourth-iteration checker was reusable infrastructure, not a new
  simplification result. This checker is a locally authored extension of that
  approach; no incoming script was executed in this independent review.

## Run the read-only auditor

```sh
python3 -B audit/check_integrated.py
python3 -O -B audit/check_integrated.py
```

Python 3.9+ standard library only. Default baseline is the sibling `baseline/`
directory with repository-relative paths. To use a checkout elsewhere:

```sh
python3 -B audit/check_integrated.py --baseline-tree /path/to/repository
```

JSON is stdout-only. The auditor writes nothing and invokes no subprocess,
network, compiler, git, or bundled script. Checks do not use Python `assert`.
It is a bounded parser for the delivered source layout, **not a general Lean
parser**. Exact normalized source scaffolding includes imports, attributes,
options, definitions, structures, section commands, and multiline omitted
typeclass scopes outside theorem bodies. Existing proof headers are compared
separately, and only explicitly listed proof bodies may change.

Optional checker self-test:

```sh
python3 -B audit/selftest_auditor.py
```

This separate harness writes an isolated temporary copy and invokes only the
copied locally authored auditor, then removes the temporary directory. It does
not modify the package or source tree.

## Mathematical and dependency review

1. **Guarded power cast.** `1 ≤ g` is unchanged, so the `Nat.cast_sub` side
   condition follows from `one_le_pow₀ hg`. No `[NeZero m]` is added: `m=0`
   means integer casts and remains valid; `m=1`, `g=1`, and `k=0` are included.
   Dropping the guard is false at `g=0,k=1,m=2`: truncated natural subtraction
   is divisible by two, but zero is not one in `ZMod 2`.
2. **Exact-order clients.** CRT order preservation uses the same actual
   equivalence and existing product-order identity, including coprime zero/one
   factors. The auxiliary cast is the `k=0` generator-order theorem; the full
   base-modulus cast is the `k=0` full-order theorem. Neither creates a cycle.
   The dependent modulus rewrite uses the already proved factorization and
   retains `B` as locally irreducible. Constructed coordinate equivalences and
   base-power witness theorem bodies are unchanged.
3. **Bit3.** The exact premise `x % 2048 ≤ 5` and arbitrary natural `x` are
   retained; there is no whole-number smallness assumption. The replacement
   merely simplifies the existing small-remainder test-bit fact to the target.
   Existing generic-section `omit [NeZero (N*2011)] in` scope is unchanged.
4. **Optional Gamma positivity.** `Nat.Coprime (Gamma rw n) 47` excludes zero,
   so natural-number positivity follows. Both exponents still range over all
   naturals, including zero, and the four executable definitions are unchanged.
   The earlier coprimality theorem does not depend on `Gamma_pos`; no cycle is
   introduced. However, elementary factor positivity now reaches the full
   literal-`K` residue certificate chain. The three-line saving is therefore
   optional, not a default recommendation or a claim of faster checking.

## Novelty boundary

The baseline reviewer checked all inherited proposal collections plus the
delivered fourth iteration. See `catalog/novelty_decisions.json` and its evidence.
The final documentary refresh through `91dce223cda86c0755b8a9b2504f84be04443fce`
has 36 placed manuscripts: the preceding 28, the fourth packet now placed as
`zh`, and seven additional manuscripts. All retained candidates survived that
bounded rereview. All four targets and 15 relevant dependencies are recorded
byte-identical to the unchanged implementation pin `9f35798...`; this auditor
checks those 19 baseline hashes against the old/late comparison receipts.
It does not itself fetch or resolve remote Git objects. The late `zd` packet
already includes a finite prime-factor order certificate mechanism, so there
is no global claim that prior work lacked exact-order machinery.
`q_prefix` was rejected as an exact E41 predecessor-exponent rewrite repeat;
neither its candidate, patch, nor savings are delivered. The accepted cast,
CRT, bit-test, and positivity changes are described only as fresh applications
at these exact clients. Familiar simplification techniques are not claimed new.

## Independent finite controls

The JSON records 2,907 guarded cast cases, 5,580 CRT cases (120 with a zero
factor), five actual full prime-power order instances (`k=0..4`), the exact
nonzero lift digit 60,739, 14,336 bit-residue representatives with large
multiples, and 502 coprime-to-47 positive naturals. Invalid no-guard alternatives
have explicit controls. These finite tests supplement source review only.
