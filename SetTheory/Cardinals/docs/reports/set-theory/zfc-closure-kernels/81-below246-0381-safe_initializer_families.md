# Safe seeds for shorter initialization

The new dirty-root result leaves six fields unrestricted, but retains an exact
condition on the formula data:

```text
Safe st = C254 st.tw ∧ C254 st.p2 ∧ Enum254.Good st.ws.
```

The fields are `[N,T,W,A,D,H,X,Y,L]`. A valid whole root frame with this
condition is enough for `DirtyProgram254.iter_halts_iff` and its path-program
corollary. It need not have `N=2` or have all nine fields zero. The checked
`Bisim254.prog254_halts_iff` transports every common register vector between
literal `Prog254` and the path DAG at empty instruction pointers. Its full
3,010-entry kernel check has passed; see
[the verification record](results/bisim254-optimized-verification.json). The generic statement supplies no binary frame theorem.

A small family needs no equality derivation. Code 0 is `C254.truth`, and
`C254.gen i` closes any theorem code under `wal i`. In particular,

```text
wal 0 0 = 2,    wal 1 0 = 6.
```

Thus either formula field may be 0, 2 or 6. The formula stack uses **unshifted**
Cantor pairing: `Enum254.good_cons` builds `Good (P x z)` from `C254 x` and
`Good z`. Starting from `Good 0` and taking at most two cons operations with
heads in `{0,2,6}` gives exactly

```text
{0,3,9,18,21,48,252,297,399}.
```

This is a directly provable finite relaxation of a zero-only initialization
screen. The proof-list constructor's extra 1 does not belong to the formula
stack. For example, stack 1 contains the falsity code 1 and is unsafe under
numerical consistency. The small positive instances `Good 3`, `Good 9`,
`Good 18` and `Good 21` follow from the same construction.
The checked `SeedInvariant254.lean` module supplies a larger certificate family,
including numerical equality reflexivity via the actual Tarski-to-numerical
proof adapter (`eq_refl_code`). This smaller family uses only truth
and generalization.

The known runtime-252 physical frame
`[60,4,2,4,0,0,0,0,0]` has logical top and retained formula zero, but stack 60.
The source-35 configuration is an **interior** dispatch position: the
head-to-header distance is 32 cells in total, comprising 28 PC bits and only
four zero padding cells. It does not have 32 zeros after the PC and is not
an empty-PC root frame. Neither the root dirty-state theorem nor the
empty-PC/gap-at-least-40 detector applies directly to that configuration.
Repeated unpairing exposes heads `[5,0,0,1]`. Its buried falsity makes `Good 60`
imply `C254 1`, so six-field freedom alone does not repair that frame. As a
formula, however, 60 is `wim 5 0`, and is derivable by K-weaken from truth.
Likewise 4 is `wim 1 0`. Thus every scalar value in this physical frame is a
theorem code, despite the failure of its stack invariant. Moving the bad stack
scalar into the top/cache field can therefore be sound; the stack itself must
still receive safe stream data.
Allowing merely satisfiable open atomic seeds would not solve the problem:
generalization requires a sound interpretation of their universal closures.

The accompanying bounded experiment permutes the physical roles while retaining
the complete calculus. The stack can exchange its physical slot 0 with a
numeric slot such as nextproof's slot 6. That permutation retargets two
incoming selector edges; the complete
program and every logical rule remain present. All 64 stack swaps and
stack-containing three-cycles passed the 8,391 instruction diagnostics per table, conditional on the four attributed core-box
contracts. The exact protected 55 transition pairs supporting those contracts
are unchanged. The first 36 recipes and remaining 28 are recorded separately
by `breakthrough_register_permutation.py` and the corresponding two result
files. These tests preserve the whole frontend but are not a kernel proof of
the binary program.

The stronger blank-start experiment covers 64 permutations and an identity
control. Zero-read prefixes collapse all 252 blank start states exactly into
seven first-write classes (240 states) and 12 all-zero cycles. All role-map
edits read 1, so this prefix partition is unchanged. There are 455 normalized
literal runs, each bounded by one million steps after its first write: 440
reach that bound and 15 halt. None reaches the tested sufficient empty-PC,
gap-at-least-40 frame. Two earlier fixed-start controls additionally reach ten
million steps without it. These finite observations do not exclude later
initialization or an interior frame with a separately proved continuation.
The detector records all spare blocks; their required values/capacity still
need separate proof for any positive. Moving scalar theorem codes does not
repair a program-counter or padding mismatch.

Exact recipes, charged tables, finite scopes and limitations are recorded in
`results/breakthrough-register-permutation.json`,
`results/breakthrough-register-permutation-remaining28.json` and
`results/breakthrough-blank-starts.json`; the last experiment is reproduced by
`breakthrough_blank_starts.py`. The old frame is not a bootstrap certificate
for an altered table.

The final invariant remains explicit: a genuine root dispatch frame, the exact
instruction pointer and head position, three safe formula fields, and the
binary engine's exterior/spare-block conditions. Logical zero registers beyond
index 8 and physical spare blocks are separate obligations. None of these
planning observations establishes a smaller consistency machine or changes a
frozen candidate table.

