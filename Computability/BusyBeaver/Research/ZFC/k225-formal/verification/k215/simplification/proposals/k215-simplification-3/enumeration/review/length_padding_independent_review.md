# Independent review: command-length padding

Status: mathematically valid under the hypotheses below. This is a source review and proof sketch, not a Lean-kernel-validated result. No sealed candidate or upstream source was changed.

## 1. Minimal encoding lemma

Assume a command codec satisfies

- `decode (pack c r) = (c,r)`;
- `(decode z).2 <= z` for every natural `z`.

Then `r <= pack c r`, by applying the second assumption to `pack c r` and rewriting with the first. For

- `encL c [] = pack c 0`;
- `encL c (c' :: cs) = pack c (encL c' cs + 1)`,

induction proves `cs.length <= encL c cs`. The empty-tail case is `0 <= pack c 0`; in the successor case,

`(c' :: cs).length = cs.length + 1 <= encL c' cs + 1 <= pack c (encL c' cs + 1)`.

The bound is on the tail length, equivalently the full nonempty word's length minus one. Do not strengthen it to full length: a one-command terminal word can have code zero.

A suitable uncompiled Lean proof sketch for the existing `EnumPerm` namespace is:

```lean
theorem pack_ge_residual (c : Cmd) (r : Nat) : r <= pack c r := by
  have h := decode_le (pack c r)
  simpa only [decode_pack] using h

theorem encL_ge_tail_length (cs : List Cmd) :
    forall c : Cmd, cs.length <= encL c cs := by
  induction cs with
  | nil => intro c; exact Nat.zero_le _
  | cons c' cs ih =>
      intro c
      have h1 := ih c'
      have h2 := pack_ge_residual c (encL c' cs + 1)
      simp only [List.length_cons, encL]
      omega
```

Variable command arity is immaterial: both hypotheses apply after the entire command, including operands, has been decoded. No fresh facts about Cantor pairing are needed.

## 2. Universal halting survives arbitrary finite prefixes

Let `U` be nonempty and assume `cexec U w = none` for every raw work-store `w`. Let `P` be any finite command word. Existing `cexec_append` gives:

- if `cexec P w = none`, then `cexec (P ++ U) w = none`;
- if `cexec P w = some w'`, then `cexec (P ++ U) w = cexec U w' = none`.

Thus `P ++ U` halts from every raw work-store. This argument requires genuine totality into `Option`: a physical infinite execution of a prefix command is not represented by `none` and is not covered. Earlier halting is permitted; the prefix does not have to preserve any invariant or complete normally.

If `P.length = N`, the encoded word has tail length `N + U.length - 1 >= N`. Therefore its candidate code is at least `N`. The universal quantifier must range over every raw store that can be produced by a prefix or earlier candidates; merely proving the suffix for clean stores is insufficient without a reset or an invariant argument.

## 3. Pointer zero and reachability are separate issues

In `lean/latest/EnumPerm.lean`, code zero is not an empty-program sentinel. A zero-valued encoded terminal command is actually fetched and executed. Internal list tails are stored as `encL tail + 1`, so they are positive even when the tail's encoded number is zero. At `pl = 0`, the next candidate is fetched; at positive `pl`, the command code is `pl - 1`.

For positive `pl`, the next list pointer is at most `pl - 1`, by `decode_le`. This is the strict-decrease argument needed by `drain`. Candidate commands terminate abstractly because `cstep` is a total `Option`-valued function. `reach` then proves that the consecutive scheduler reaches every candidate at or above the current cutoff, unless it halts first. None of these facts depends on invariants of the working registers.

For a fixed cutoff `b`, choose padding length `N = b`, or use a fixed universally halting word already known to have code at least `b`. Invoke `reach` with distance `code - b`, then `exec_list`; prepend the reaching run using `run_add`. If starting with `pl > 0`, invoke `drain` first. These are operational completeness facts, independent of soundness.

A fixed candidate code at least 21 is sufficient for cutoff 1, but not for an arbitrary larger initial cutoff. A theorem quantified over every initial cutoff needs cutoff-dependent padding, or a separate cofinal family. Length padding replaces the `START_Y`-parameter family with a simpler syntactic one; it does not eliminate cofinality from arbitrary-cutoff completeness.

## 4. Scheduler limitation

Cofinality of the universally halting candidate set does not imply that a biased or skipping scheduler visits that set. Even two cofinal subsets of the naturals can be disjoint. An exhaustive consecutive scheduler, a proved hitting condition for this particular family, or a stronger scheduler-specific construction is required. This review does not establish any result for arbitrary biased schedulers.

## 5. Inspected source facts and verified common-NIP application

Inspected: `research_proof_simplification/lean/latest/EnumPerm.lean`, especially `pack`, `decode`, `decode_pack`, `decode_le`, `encL`, `cexec_append`, `exec_list`, `drain`, `reach`, `program_none`, `encL_ge`, `complete`, and `halts_iff`.

The source already proves `program_none Y p hp` for every raw `W`, so taking `Y = 0` supplies a fixed universally halting suffix in this model; prefix padding then recovers arbitrary-cutoff completeness without the existing operand-specific `encL_ge` argument.

Also inspected: `research_sub214d/rotate_math/common_nip_repair/PROOF.md`, Sections 1, 4, 8, 10, and 11; and `CREDIT_PROOF.md`, Sections 1 and 2. The common-NIP codec is not the same command-tag codec as `EnumPerm`, but it satisfies the same relevant properties.

Section 8 explicitly defines `STORE_i = D; R^8; M(i)`, so each `STORE0` has ten commands. It proves that two stores map every raw input to the required sentinel state unless they halt first, and hence that `U = STORE0; STORE0; B1; R; R` universally halts. Its exact positive-residual codec preserves terminal zero R commands: `Tail([R]) = 1`, `Tail([R,R]) = 3`, and fresh candidate 2 executes both R commands. Thus `U.length = 22 + B1.length` and `code(U) >= 21 + B1.length >= 21`. The established actual startup has next candidate 1 and residual pointer zero. No padding or `START_Y` family is required for this cutoff.

There is an even smaller source-level replacement: `CREDIT_PROOF.md` Section 2 already proves `W(n).length <= n + 1`. Once the exact codec round-trip identifies `W(code(U)) = U`, this existing fact directly gives the same lower bound. The new generic encoding lemma is useful for reuse, but is not mathematically necessary to simplify this actual-cutoff proof.

This change removes only the command-level cofinal family from the actual-cutoff completeness argument. It neither replaces nor strengthens the separate source, physical runtime, protected-credit, blank-start, and numerical-calculus comparison premises. No physical audit was rerun.
