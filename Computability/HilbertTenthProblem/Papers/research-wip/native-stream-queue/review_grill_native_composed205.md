# Independent review of the composed native Grill205 compiler

**PASS; no requested source or documentation change.** The complete composed polynomial equals the weak208 polynomial on the same supplied coordinates. The separate identity with strong206 uses `Z_strong=Z_weak−2x`; it does not identify positive witness fibers. The default fixed program `011` costs **205=92M+113A**, with 31 positive witnesses and degree upper bound 1187. Its raw mode costs 229=98M+131A, with 37 witnesses and upper bound 484. Neither bound is asserted to be the exact degree or a universal Diophantine operation record.

This review read the complete composed source and companion note, the frozen phase-residual transformation and proof, and the relevant weak-width transformation inherited from the prior review. It independently checks the eight complete emitted forms against both frozen parent receipts. It does not repeat the native classification proof, encoded-universality investigations, all historical author suites, or all ancestor source-loader regressions.

## Pinned evidence

| Artifact | SHA-256 |
|---|---|
| [Composed source](grill_tag_native_composed205.py) | `4084a58d5cf30694a8717c26d0abdf2aecc2fa6a7099d9815f35521005afab94` |
| [Composed proof/API note](grill_tag_native_composed205.md) | `47416c75df576e3f13fd2ebd2a13ac8b7d1fa9d1049e79de5243833ed5751592` |
| Weak208 source | `8f636a7954fce4335c2977baf849da0107b29d146aaa008fbb9732acedcf60b9` |
| Weak208 complete saved receipt | `855a973645e93f64d9e61998880bf270d0f048b8a13a4823ea756bf57092695a` |
| Strong206 source | `b9eaa5edf08f355607adf496d9477b806960c3438a81099f64cf08d0b7471af1` |
| Strong206 complete saved receipt | `bc58e688fd9f47e2a6ad2414084d68cc4f4118c0234a7f72f949b2524e995908` |

The [independent checker](review_grill_native_composed205.py) authenticates the candidate bytes and both direct source files before importing the candidate. It authenticates both parent receipts before reading their complete schedules. Candidate execution compiles authenticated source bytes directly; its public calls recheck both direct parents and the inherited source contexts. No reviewed source or saved parent receipt was modified; warm guard tests use private copies.

## Independent algebra and complete source accounting

Put `S_p=Shat_(2p)+Shat_(2p+1)−2`, `J=ΣS_p`, and `T=Σ_(p=1)^(m−1)(m−p)S_p`. Expanding the actual parent definitions, rather than treating `J` as independent, gives

\[
Q=(m+1)J-mS_0-T,\qquad \operatorname{Next}=mJ-T,
\qquad P=(B-1)J+1.
\]

Hence the complete phase residual is identically

\[
B\operatorname{Next}+q_0-Q-mP
=m(\widehat S_0+\widehat S_1)-(B-1)T+q_0-(J+3m).
\]

For one phase it is `q0−1`. This holds without sign, zero-set, Boolean-selector, or native-typing hypotheses. The checker recursively expands both actual phase residuals into polynomials in `B`, every original selector hat, and `q0`; it also independently expands the actual `J` and `P` registers. It then proves `B` unchanged and compares the two entire expression DAGs using only the proved phase residual as a cut. A shared exact expression table, not a digest heuristic, proves all other comparison operands, common active interfaces, all native factors, and the complete output identical. The change therefore preserves the full polynomial and all supplied positive zeros relative to weak208.

The opposite order is independently reconstructed from the saved strong206 source. Its only private width multiplier is `three_x__0=3*x`, consumed solely by `P0=Z0+three_x__0`; `Z0` also has no other consumer. Removing that gate and replacing the width row with `P0=Z0+x` yields the composed certificate and full polynomial schedules literally, including all comparisons and active interfaces. Thus no uncharged replacement or hidden deletion accompanies the composition.

The separate affine identity `3x+(Z−2x)=x+Z` proves the width cut for strong206. A second exact whole-DAG comparison then proves every residual and the full output under that substitution. This integer coordinate map is invertible, but the inverse sends the positive tuple `x=Z=1` to slack −1. The forward map from strong positive tuples, `Z_weak=Z_strong+2x`, is positive and preserves the complete output. The inherited padding theorem establishes equality of existential input languages; it is not replaced by an unsupported positive inverse map.

Every emitted binary gate, including constant multiplication, is charged. All 1,594 gates across the eight schedules are live in their respective full outputs. Independent degree propagation reproduces the declared upper bounds. Each form saves exactly 1M+2A from weak208 and 1M from strong206. The candidate keeps `exact_degree=None`, the original supplied coordinate lists, raw/unit native factors, and complete finalizers. The prior native theorem applies through the exact weak-parent polynomial identity; no fresh materialized Pell solution is claimed by these algebra tests.

## Scope, metadata, and public APIs

The current `polynomial_identity_parent` explicitly names weak208. `phase_residual_rewrite` names that actual parent and pins strong206 separately as the arithmetic rewrite source. The earlier width-rewrite relation is archived under `historical_weak_cone_rewrite`; strong-only ancestor information remains historical. Removed phase outputs have proof-only formulas, with no stale live-register references in active metadata. The current input cone remains `P0=x+Z0` and explicitly denies a positive-fiber bijection to the strong ancestor. The complete proof note accurately preserves fixed finite programs, existential packed duration, post-halt closure semantics, and the absence of a universal program/input decoder.

Canonical parent accessors reproduce both complete pinned saved descriptors. Public whole-packet validation rejects altered source rows, metadata, numeric type aliases and foreign string keys. Assignment APIs require exactly the coordinate keys and positive exact integers, with an explicit exact Boolean `signed=True` for integer algebra. The integer pullback advertises possibly nonpositive output. Nested mutations to all four public copy-returning surfaces do not poison subsequent calls. Both direct source files are reauthenticated even after private warm-cache population. Optimized execution is explicitly rejected.

## Bounded independent receipt and replay

The [saved receipt](review_grill_native_composed205.json) records:

- Eight full weak-parent DAG identities and eight signed strong-parent DAG identities, covering 248 complete residual identities.
- Forty-eight expanded phase/`J`/`P` identities and 16 independently reconstructed literal certificate/full-polynomial schedules for the opposite rewrite order.
- Eight full ledger, liveness, upper-degree and current/historical-metadata audits; 16 pinned whole-parent descriptor checks.
- Eighty complete integer diamonds, including 40 signed tuples, and 2,480 numeric residual equalities;16 rational diamonds and 40 positive forward maps.
- Eight explicit identical-coordinate strong/weak output separations, 224 malformed rejections, 32 nested copy-isolation checks, two private warm direct-source pin rejections, and explicit `-O` rejection.

The complete checker run and a fresh exact `--expect` replay passed. No result depends on a hardcoded temporary or workspace location. Supply the source, root and parent receipts explicitly; the optional note argument authenticates the proof note as well. The research virtual environment supplies SymPy:

```sh
/tmp/diophantine-research-venv/bin/python review_grill_native_composed205.py \
  --source grill_tag_native_composed205.py \
  --root /path/to/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue \
  --weak-receipt grill_tag_native_weak_cone.json \
  --strong-receipt grill_tag_native_phase_residual206.json \
  --note grill_tag_native_composed205.md \
  --expect review_grill_native_composed205.json
```

Omit `--expect` and pass `--output PATH` to write a new receipt. Saved JSON comparisons are recursively type-sensitive.

## Root integration check

The root agent read the complete author source and proof, both inherited
transformation proofs, and this independent checker and review. Fresh root
replays of the author and independent checkers reproduce both frozen receipts
byte for byte. The integration keeps equality to weak208 and signed substitution
to strong206 separate, and retains the explicitly unproved universal decoder.
