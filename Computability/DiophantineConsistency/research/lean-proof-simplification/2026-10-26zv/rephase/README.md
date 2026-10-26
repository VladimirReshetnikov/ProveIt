# Exact rephase field transport: one local residual deletion

**Retain as a routine, proof-only cleanup.** The complete
`CurrentWordRephase2011.lean` changes from **122 to 116 physical lines**
(6023 to 5925 UTF-8 bytes). There is no helper, new import, new dependency,
changed public statement, new definition, or changed choice of witness.
Only the proof fragment of `normalization_of_rotation_eq` at original
lines 28–38 changes. The eight theorem statements and every other byte
are preserved. This is not a new rephasing or normalization abstraction.

Source pin: `9d9d1123b39927d30363f1dcd53c23f0575c30ee`.
Source prefix: `Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.

## Mathematical reason

The existing definition is

```
raw c W i = convolution folded c i + binaryRotation 47 W c i.
```

The theorem assumes an actual equality of functions
`hr : binaryRotation 47 W' c = binaryRotation 47 W c`.
After unfolding `raw`, `hr` rewrites each new rotation to the old one.
The new recurrence and decomposition are therefore exactly the old fields:

```lean
  refine ⟨hf.carry_bound,hf.digit_bound,?_,?_,hf.word_bound,?_⟩
  · intro i
    simpa only [CurrentCarryConstruction2011.raw,hr] using hf.recurrence i
  · intro i
    simpa only [CurrentCarryConstruction2011.raw,hr] using hf.decomposition i
```

The source creates a four-line intermediate function equality `hraw`, then
uses two three-line `intro`/`rw`/`exact` branches. The proposal replaces that
ten-line portion by two two-line `intro`/`simpa only` branches; the common
`refine` remains. The two `simpa only` calls have an explicitly limited
rewrite set. They do not search for a different carry or normalized word.

The subsequent scalar-congruence proof (original lines 39–47) is retained
byte-for-byte. It transports through the proved `word_binaryRotation`
congruences, adds the literal-kernel contribution, and composes with
`hf.transport`. It does **not** turn congruence into equality of ordinary
multipliers.

## Semantic guards retained

- `c`, `carry`, and `digits` remain exactly the same functions.
- The generic normalization theorem retains arbitrary natural-valued `c`,
  with no new Booleanity or tiling premise. Its existing `[NeZero n]` is
  unchanged. Positivity is not silently discarded.
- Physical shift and source equality, whole-cell rotation, marked-word
  transfer, and all packing clients are byte-identical.
- `marked_packing_rephase` still uses the exact transferred normalization
  and the original `carry`/`digits`; matching and Boolean dummy hypotheses
  remain where needed for scalar/mask construction.
- The new positive quotient remains `quotientWitness` of the product with
  the **new** ordinary multiplier. The source, alpha and normalized F are
  not resampled. Ordinary temporal multipliers can differ, and so can z.
- `N=1`, zero stride, multiple periods and cyclic predecessor wrap remain
  in scope exactly as before. No actual one-cell marked tiling is asserted.

A deliberately tiny guard model makes the distinction visible: radix 4,
length 1, kernel 1 and source digit 1 have carry 0 and normalized digit 2
for both shifts W=0 and W'=2. The multipliers are 1 and 4, respectively;
the positive quotients are 1 and 2. Both transport factors are one.
This is a generic reduced-radix illustration, not a claimed instance of
an actual marked 942-tile word.

## Novelty after all earlier proposals are assumed available

The inherited E15/E16 coherent carry and word views, E17 modular source
projection, normalization uniqueness/cyclic carry results, generic
witness transport, and fresh incoming ResetLocality are all treated as
available. The delivered round-five exact-order/modulus/bit-test changes,
including excluded `q_prefix`, receive no credit here. The baseline reviewer
searched all a–w materialized reports/notes/Lean/patches, inherited x–zj
texts and all five new incoming ZIPs (including baseline/library snapshots)
and found no proposal for this exact intermediate `hraw` deletion.

The fresh incoming nearest contract `lean-proof-simplifications-2026-10-26`
C characterizes raw-cell carry/digit finite prefixes after proved terminal
reset. Its normalization/locality architecture is not claimed anew. The
residual recommendation is strictly the concrete removal of a now-unneeded
intermediate equality in two freshly introduced client proof fields.

### Screened alternatives not promoted

1. A general source/carry record view, same-normalization constructor, or
   quotient/remainder transport interface would repeat the assumed baseline.
   Merely moving the seven packing fields into a helper is not a saving
   without counting that helper and every adapter, so no such patch is supplied.
2. The current `rotation_eq` can be reasoned about directly from the actual
   quotient/remainder rotation definition. Generalizing it to non-Boolean
   sources would change the public API or require a retained wrapper, whose
   full cost is not justified by these existing clients. No broader theorem,
   removed guard, or speculative saving is credited.
3. Factoring `(K+2^W)*C` through shorter modular chaining would be a cosmetic
   rewrite of a useful explicit arithmetic boundary. The literal transport
   chain is deliberately left untouched.
4. Identifying the ordinary multipliers, retaining the old quotient, or
   replacing the old carries/F by a fresh existential normalization is invalid
   for the exact requested witness-preserving endpoint.

## Artifacts and checks

- `source/CurrentWordRephase2011.lean`: complete pinned source.
- `candidate/CurrentWordRephase2011.lean`: complete candidate module.
- `patches/rephase-exact-field-rewrite.patch`: exact unified diff.
- `evidence/*.lean`: five unchanged complete source dependencies/checks,
  included only as evidence, not new helper implementation.
- `source_manifest.json`: exact SHA-256 bindings.
- `verify.py`: newly authored portable, read-only, Python-standard-library
  checker. It writes no files, imports no repository code, invokes no
  subprocess/network and has no `assert` checks disabled by optimization.
- `validation.json`, `validation_optimized.json`: matching observed results.

Run from any directory:

```sh
python3 /path/to/rephase/verify.py
python3 -O /path/to/rephase/verify.py
# Optional: compare all source evidence to the supplied read-only checkout.
python3 /path/to/rephase/verify.py --source-root /path/to/pinned/upstream
```

The checker verifies the exact permitted replacement, all eight public
names, complete unchanged prefix/suffix, full module metrics, hashes and
patch reconstruction. It additionally tests 32,832 reduced-radix cases,
242,568 recurrence/decomposition instances, 31,708 strict quotient cases,
and 30,916 genuinely changed positive quotients. All source maps into
`{0,1,2}` are tested for lengths 1–4 and radices `2^v`, v=1–3, with kernels
0/1/5, partial phases and one/two complete periods. Its negative guards
reject nonperiod rotation equality, ordinary-multiplier equality and
reuse of the old positive quotient.

**All Lean is UNCOMPILED.** These static and finite checks do not establish
Lean elaboration, kernel acceptance, axiom footprint, fixed enormous-kernel
exhaustion or performance. No Lean/Lake/Elan, incoming code, package
installation, branch fetch or upstream edit was executed. The candidate
should be tested by rebuilding the main module, then its existing checks
against that rebuilt object, in an authorized Lean environment.
