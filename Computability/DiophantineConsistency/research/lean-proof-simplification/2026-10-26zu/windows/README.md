# Shared monotone windows: one structural proof idea

Repository pin: `VladimirReshetnikov/ProveIt` commit
`9d9d1123b39927d30363f1dcd53c23f0575c30ee`.

**Marginal baseline:** packet y
`syntax/candidates/ObjectPairingInjective.lean`, assuming its shell-cut
proposal has already been applied. This exact baseline is included under
`prior_baseline/`. Generic ordered-semiring division uniqueness and the
successor-order bridges are also treated as prior work.

## Proposal

Use a single index-recovery theorem for two existing uniqueness arguments.
For a monotone boundary map `base`, a successor map satisfying
`a < b -> succ a <= b`, and one value `x`, the four inequalities

```
base a <= x < base (succ a)
base b <= x < base (succ b)
```

force `a = b`. The proof compares the indices. If `a < b`, the first strict
upper bound and monotonicity imply `x < base b`, contradicting the second
lower bound. The reverse strict comparison is symmetric.

The theorem `OrderedWindow.index_unique` requires only a linear order on
indices and a preorder on values. It does not require well-foundedness,
finite intervals, Archimedeanness, external natural indices, strict
monotonicity of `base`, or a total inverse function. The strict upper bound
is essential: closed adjacent windows can share their boundary point.

### Client 1: maximum shell in square pairing

In `ObjectPairingInjective.lean`, take `base k = k*k` and the index
`max a b`. The already proved `max_square_le_pair` and
`pair_lt_next_square` provide both bounds. This removes the private
`square_le_square` and `max_not_lt` scaffolding, and establishes the common
maximum before the existing branch argument. The proposal changes no
pairing formula and introduces no new ring assumption. The original
`succ_le` parameter is retained.

### Prior-work compatibility client: quotient window

In `ObjectDivision.lean`, take `base q = q*d`. A division certificate
`n=q*d+r` with `r<d` puts `n` in that half-open window. Monotonicity uses
`0<=d`, already available for every internal natural. After the shared
index theorem gives equality of quotients, additive cancellation gives
equality of remainders. No separate positive-denominator premise is added;
when `d=0`, the supplied strict remainder bound is itself impossible.

The compatibility-only pinned-source adapter uses the existing internal discreteness lemma to
supply `step_le`. Under the user's assumed-applied baseline, packet zf's
successor-order interface can supply the same callback directly. That
replacement is prior work and is not counted as a contribution here.

## Novelty boundary

This is ONE cross-client interface, not two independent ideas. Earlier
packet y proposes a pairing branch threshold and retains `max_not_lt` and
`square_le_square`; the delivered hunk modifies the preceding maximum-index
argument and remains applicable after that branch simplification. Packet
zf already supplies successor-order bridges and optional instances.

The incoming `proveit-lean-additional-certificates-2026-10-26.zip`, member
`audit/exclusion_taxonomy.txt`, explicitly discusses exploratory generic
ordered-semiring division uniqueness. That suggestion is treated as prior
work even though it is not a supplied implementation. Consequently this
packet does NOT claim ordered-semiring division uniqueness, the quotient
interval argument by itself, or generic Euclidean certificates as new. Its
narrow additional proposal is the non-arithmetic monotone-window interface
and its reuse across the quotient and square-shell arguments.

## Honest marginal accounting

The main patch is rebased onto packet y's complete pairing candidate. It
preserves `pair_lt_shell_cut` and the subsequent two-branch injectivity
proof exactly, changing only how the common maximum is obtained. Generic
ordered-semiring division uniqueness is assumed available and contributes
ZERO new source-line savings.

| File | After prior proposals | After this proposal | Delta |
|---|---:|---:|---:|
| ObjectPairingInjective.lean | 100 | 94 | -6 |
| New OrderedWindow.lean helper | 0 | 22 | +22 |
| Total physical lines | 100 | 116 | **+16** |

The extra import and complete helper are charged. The existing pairing file
shrinks, but the marginal package grows by 16 lines. This is optional
structural simplification, not a net source-size win. Adopt it if a common
boundary-index API improves maintenance or serves further clients. No
compile-time improvement is claimed. The successor callback is left as in
y to avoid claiming prior zf work again; using zf's already available bridge
affects both baselines equally.

`compatibility_current_head/` retains the earlier illustrative current-head
patch and algebra checks. Its two files shrink by 8 lines while its helper
adds 22, for net growth of 14. Those numbers are not marginal savings under
the user's premise and must not be substituted for the table above. The
division change is compatibility evidence only.

## Artifacts and validation status

- `lean/DiophantineConsistency/OrderedWindow.lean` is the minimal new helper.
- `lean/DiophantineConsistency/ObjectPairingInjective.lean` is the complete
  candidate AFTER packet y's prior shell-cut simplification.
- `ordered-windows.patch` adds the helper and changes that post-prior pairing
  candidate. It passes `git apply --check` against the exact y baseline
  included under `prior_baseline/`. It is not intended to apply directly to
  the pinned maintained pairing file before the prior proposal is applied.
- `kernels/PairingKernel.lean` extracts the complete generic
  `DiophantineConsistency.MaxSquarePairing` namespace from the post-prior
  candidate, without altering definitions or declarations. Only imports
  are replaced by precise Mathlib dependencies and the new helper. The
  internal-natural wrapper following that namespace is outside this check.
- The generic helper and post-prior pairing kernel are checked with Lean
  4.32.0. See `validation.json` and the logs for exit status and hashes.
- The complete internal-object modules are NOT claimed to have been
  rebuilt. Model-specific wrapper integration requires the repository
  build. The public signatures and computational definitions are preserved,
  but that is not a substitute for integration.
- `compatibility_current_head/` contains separately labeled complete-module
  candidates, an exact generic production kernel check, and arbitrary
  ordered-semiring checks for the current maintained source. Those files
  support applicability; they do not establish a further new division idea.

After applying the prior y change and then the main patch in a fully
configured checkout, a suggested integration check is:

```
lake build DiophantineConsistency.ObjectPairingInjective
```

Run the corresponding existing checks and compare axiom reports. The new
helper sits below either client, avoiding division-to-pairing or
pairing-to-division imports. Reusing it inside an already-refactored generic
division library is a possible adapter, not another recommendation counted
as new here.
