# AQ22–AQ28 and standard AQ26/AQ29: current-source build and promotion

3 November 2026. Author-side build by the Claude session; not a paired replay.

## What was promoted

Before this record, the iPRA endpoints for the
[22-variable degree-ten](../../research/adaptive-square-sums22-degree10/README.md),
[26-](../../research/adaptive-square-sums26-degree8/README.md),
[27-](../../research/adaptive-square-sums27-degree8/README.md) and
[28-variable degree-eight](../../research/adaptive-square-sums28-degree8/README.md)
candidates, and the standard-theory clients for AQ26 and AQ29, existed only as
drafts under `research/adaptive-aq22-proof/draft-src`,
`research/adaptive-aq28-27-proof/draft-src`, `research/ipra-standard-aq26/draft`
and `research/ipra-standard-aq29/draft`. They had compiled only in historical
hybrid providers, and so were kept outside the Lean source tree.

All 35 drafts were copied **byte for byte**, with unchanged module names, into
`Lean/DiophantineConsistency/`. None of them collided with an existing module.

## Build

- **Tree:** the root workspace at `97c0c77cc4`. No file under
  `Computability/DiophantineConsistency/Lean` changed between that commit and
  `62494ae438`.
- **Build discipline:** one target per `lake build +DiophantineConsistency.<M>`
  invocation, in dependency order, with `LAKE_JOBS=1` and
  `LEAN_NUM_THREADS=0`.
- **Outcome:** every one of the 35 targets exited 0 with no `error:` line.
  The peak resident memory per target was 3.6–4.8 GB.
- **Earlier evidence:** the native modules had also compiled on 2 November in
  an untracked replay against the same sources, and that replay had the same
  axiom reports.

## Named axiom reports (Lean metatheory)

Each of the following reports exactly `[propext, Classical.choice, Quot.sound]`:

- **Native endpoints:**
  - `IPRAAQ28Native.literal_equivalence`, `bridge28`, `sameNoZero` and `AdaptiveAQ28.current_no_zero_iff`;
  - the same four for AQ27 and for AQ26;
  - `IPRAAQ22Native.literal_equivalence`, `bridge22`, `sameNoZero`.
- **Standard endpoints:**
  - `IPRAStandardAQ22.literal_equivalence`, `selected_foundation_consistency`, `literal_iff_translated_consistency`;
  - the same three for `IPRAStandardAQ26` and `IPRAStandardAQ29`;
  - `IPRAStandardTheory.provable_iff`.

## Scope

- **What this shows:** the drafts are current-source Lean results of the root
  workspace. Their source-to-object provenance is therefore that of any other
  module in the tree.
- **What it does not show:**
  - It is not an independent paired replay.
  - It adds no Lean degree theorem or PDF-byte binding. The finite substitution,
    degree and display checks of the candidate directories remain the evidence
    for the displayed polynomials.

## Source SHA-256 (first 16 hex digits)

| module | SHA-256 |
|---|---|
| `*AdaptiveAQ22.lean` | `aa297c69f2d6e404` |
| `*AdaptiveAQ22Literal.lean` | `7d417cd67cc0d615` |
| `*AdaptiveAQ22Maps.lean` | `001522388c7ee1ba` |
| `*AdaptiveAQ22Transport.lean` | `5268cdf1dd3ec128` |
| `*AdaptiveAQ22Zeros.lean` | `68f5256462721aac` |
| `*AdaptiveAQ26.lean` | `a860fe6727f99615` |
| `*AdaptiveAQ26Checks.lean` | `ad52094c5899b601` |
| `*AdaptiveAQ26Literal.lean` | `91af1d18ff432362` |
| `*AdaptiveAQ26Maps.lean` | `d7d77a51a01c982f` |
| `*AdaptiveAQ26Transport.lean` | `ac8174e891a7f485` |
| `*AdaptiveAQ26Zeros.lean` | `dd49ed0bf6833835` |
| `*AdaptiveAQ27.lean` | `f2442ba590962f1d` |
| `*AdaptiveAQ27Checks.lean` | `afba09db77ff45da` |
| `*AdaptiveAQ27Literal.lean` | `51e8c9bcc00f8032` |
| `*AdaptiveAQ27Maps.lean` | `45849ddcf9afb737` |
| `*AdaptiveAQ27Transport.lean` | `27fee44ba2bae98f` |
| `*AdaptiveAQ27Zeros.lean` | `efb37851cc6e044c` |
| `*AdaptiveAQ28.lean` | `8dedd9b8c09b60b3` |
| `*AdaptiveAQ28Checks.lean` | `129e4a394e048c74` |
| `*AdaptiveAQ28Literal.lean` | `62dd23f65337c5da` |
| `*AdaptiveAQ28Maps.lean` | `50611f5f1728975a` |
| `*AdaptiveAQ28Transport.lean` | `984ac0e8477ba325` |
| `*AdaptiveAQ28Zeros.lean` | `f6b1da712d189a30` |
| `*IPRAAQ22Native.lean` | `b90a9eb67b6fef94` |
| `*IPRAAQ26Native.lean` | `7be42c91618e357e` |
| `*IPRAAQ26NativeChecks.lean` | `3b7f63153b364c99` |
| `*IPRAAQ27Native.lean` | `dcd3a41ae591cb1a` |
| `*IPRAAQ27NativeChecks.lean` | `4906fce572e86b24` |
| `*IPRAAQ28Native.lean` | `8dcf0da5661d0385` |
| `*IPRAAQ28NativeChecks.lean` | `1283ec4d03d3f7c9` |
| `*IPRAStandardAQ22.lean` | `87e270c7532b7189` |
| `*IPRAStandardAQ26.lean` | `b42e1da34edeb673` |
| `*IPRAStandardAQ26Checks.lean` | `60c7f5ef33b25b38` |
| `*IPRAStandardAQ29.lean` | `3d5dfcf53162bc7f` |
| `*IPRAStandardAQ29Checks.lean` | `d2dc7c8308b9fa2f` |
