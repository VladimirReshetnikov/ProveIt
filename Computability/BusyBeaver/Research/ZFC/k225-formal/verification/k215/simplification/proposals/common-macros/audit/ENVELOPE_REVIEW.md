# Independent review of the envelope/comprehension patch

Reviewed artifact: `root_work/envelope-sharing.patch`, against snapshot
`6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95`.

Status: **PASS for source applicability, mathematical reasoning, and explicit
signature comparison**. This review itself does not run Lean; the separate
compiler evidence must establish elaboration and kernel acceptance.

## Reasoning

`raw_aug` constructs an `E` satisfying

```
mem z E <-> z = a or (mem z a and mem t z).
```

The new `raw_envelope` extracts exactly what its three clients need:

- `a` belongs to `E`, so `E = t` would contradict the emptiness of `t`;
- if `t` belonged to `E`, the first disjunct would give `t = a`, contradicting
  `a ≠ t`, while the second gives `mem t t`, contradicting irreflexivity;
- a tagged member of `a` belongs to `E` by the second disjunct.

The premise `a ≠ t` is needed for this particular envelope construction. It is
not a claim that no different envelope could exist when `a = t`. The existing
empty-bound case of `dt_comp` remains separate and unchanged.

`dt_comp_env` moves from `KLowerQHyp` to the earlier `KLowerTag` module without
changing its proof body or namespace. Its conclusion includes the raw-member
bound needed in the power-set construction, so using it to prove ordinary
comprehension loses no information. A tagged test element is neither `E`
(because `E` is untagged) nor `t` (by irreflexivity), so its membership in the
constructed `S` is equivalent to the intended predicate. The envelope
containment assumption is used in the correct direction when constructing
membership in `S`.

`tag_collection` only needs `mem x E` for a tagged `x` belonging to `a`, exactly
the `hEa x.1 x.2 hx` supplied by the helper. Its later exclusion arguments still
have the same `E ≠ t` and `¬ mem t E` hypotheses.

The old tagged-set `envelope` API is the immediate instance of `raw_envelope`,
since `mem t a` and irreflexivity imply `a ≠ t`.

## Source checks

- `git apply --check` succeeds on the pinned source.
- The explicit theorem signatures of `dt_comp_env`, `dt_comp`, `envelope`,
  and `tag_collection` are unchanged after whitespace normalization.
- The moved declaration stays in the namespace
  `SetTheory.BusyBeaver.ZFC.KLower`.
- `KLowerQHyp` imports `KLowerEqv`, which imports `KLowerTag`; former importers
  therefore still obtain the declaration transitively, without a new cycle.
- The section variable declarations, universe, membership parameter and
  `include hs hirr ht` are identical at the old and new declaration sites.

| File | Before bytes | After bytes | Before lines | After lines |
|---|---:|---:|---:|---:|
| KLowerTag.lean | 9,945 | 10,641 | 214 | 226 |
| KLowerQHyp.lean | 12,635 | 11,040 | 263 | 231 |
| Total | 22,580 | 21,681 | 477 | 457 |

The net reduction is **899 bytes and 20 lines**. No new mathematical axiom or
stronger premise is introduced into an existing theorem. Compiled checks are
still needed to establish the exact elaborated types and axiom profiles.

## Elaboration repair

The reviewed final version spells the subtype projection cast as
`by simpa only [e] using a.2` rather than `e ▸ a.2`. This discharges the
same membership rewrite without asking dependent elaboration to substitute
inside the subtype term. The mathematical contract and all four reviewed
public signatures remain unchanged. Root reports that `KLowerTag` compiled;
that compiler execution is separate from this independent source review.
