# Exact endpoint and inherited proof boundary

## The mathematical claim

Let `P589` be the literal integer polynomial in
`fused68/support8/polynomial.json`. With `Con(ZFC)` meaning absence of a
finite formal ZFC refutation, the proposed ordinary mathematical theorem is

    ZFC proves: (there is no z in Z^589 with P589(z)=0) iff Con(ZFC).

The construction does not prove either side of this equivalence. It gives
a new explicit equation by exact transformations of a previously reviewed
refutation source. Its new equivalence lemmas are elementary integer
arguments formalizable in ZFC. The inherited arithmetic compilation and
logical calibration below remain part of the proof. No new complete Lean
kernel check or emitted object-language ZFC derivation is claimed.

## Pin and equation interface

All repository URLs in this note are pinned to commit
`84e16e43092614bae262ca59651cb9d77e31a255` of
`VladimirReshetnikov/ProveIt`.

The exact input is
[`research/factorial-radius-output-sign-profile/raw/parent.json`](https://github.com/VladimirReshetnikov/ProveIt/blob/84e16e43092614bae262ca59651cb9d77e31a255/Computability/DiophantineConsistency/research/factorial-radius-output-sign-profile/raw/parent.json),
Git blob `b43a389d3606e11ac67f8a400dd4c46b4d174007`, with its
[`raw/domain.json`](https://github.com/VladimirReshetnikov/ProveIt/blob/84e16e43092614bae262ca59651cb9d77e31a255/Computability/DiophantineConsistency/research/factorial-radius-output-sign-profile/raw/domain.json),
Git blob `8c4d3bac16db89652f27b259fb1ccecd21b5cebd`.
These literal source files are included in this directory, and
`SOURCE_PROVENANCE.json` binds their bytes to both Git blob SHA1 and SHA256.
The inherited interface is:

    exists a zero of the full 75-predicate raw integer source
        iff C222 derives the falsehood code
        iff there is a finite formal ZFC refutation.

There are 1,259 original integer body coordinates and 1,177 body equations.
The parent adds 75 nonnegativity predicates, each realized by a private
three-integer witness. Thus its full raw dimension is 1,484 coordinates
and 1,252 quadratic equations. The body contains no unfixed coefficient
ports. The new reduction does not alter its body equations.

The new proof is independent of the internal meaning of every body
coordinate. It first reconstructs all 75 old predicates at the same body
tuple, only then applies the inherited interface. No missing sign is
justified by a computation interpretation that itself needs that sign.
Both new directions preserve the set of body tuples, with fresh private
three-square witnesses when necessary. Exact monic projection then gives
the displayed 589-variable equation and a unique integer restoration of
every deleted coordinate.

## Named logical endpoint

The arithmetic source encodes the numerical `C222` calculus directly. It
does not simulate K215, and it does not use Jones' universal polynomial.
The logical endpoint is the composition of these two named theorems:

1. [`KEndpoint.c222_iff_zf_refutation`](https://github.com/VladimirReshetnikov/ProveIt/blob/84e16e43092614bae262ca59651cb9d77e31a255/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean),
   in `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean`,
   Git blob `bdf3a570fe02e5e0becf6c12f562957cf03fc8d5`:

       KCode222.C222 Code254.F <-> BProv ZFax_s [] Form.fBot.

2. [`ConstructibleChoice.zf_refutation_iff_zfc_refutation`](https://github.com/VladimirReshetnikov/ProveIt/blob/84e16e43092614bae262ca59651cb9d77e31a255/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean),
   in `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean`,
   Git blob `0f14fc8890363d7abb9c4e9aa89cae80553735cc`:

       BProv ZFax_s [] Form.fBot <-> BProv ZFCax_s [] Form.fBot.

The latter is the constructible-model Choice transport. Immediate source
copies of both files are included under `upstream/`. Their presence and
byte authentication are not a rebuild of their transitive Lean imports.
Only the machine-independent first endpoint theorem is used: the
machine-specific halting compositions in the same file are unnecessary.

## Arithmetic compilation and guard proof chain

The reviewed starting arithmetic bridge is
[`PROPOSAL_REVIEW_QUARTICS407888.md`](https://github.com/VladimirReshetnikov/ProveIt/blob/84e16e43092614bae262ca59651cb9d77e31a255/Computability/DiophantineConsistency/PROPOSAL_REVIEW_QUARTICS407888.md),
included under `upstream/`. It accepts the construction at the ordinary
mathematical level and records the same named C222-to-refutation
calibration. The review's immutable archive is
[`docs/incoming/ConZFC_407_888_Quartics_2026-10-24.zip`](https://github.com/VladimirReshetnikov/ProveIt/blob/84e16e43092614bae262ca59651cb9d77e31a255/docs/incoming/ConZFC_407_888_Quartics_2026-10-24.zip),
SHA256 `59f847872298260ee35e9d8e4cd0b52d2d78658ac523981fe060e81f40ca4a59`.
That review's historical checks are reported by its author; this package
does not claim to have independently rerun its entire archive.

The relevant subsequent ordinary proof interfaces, at the same pinned
commit, are:

| Source path under `Computability/DiophantineConsistency/` | Role in the inherited chain |
|---|---|
| [`candidates/projected-factorial-radius/PROOF.md`](https://github.com/VladimirReshetnikov/ProveIt/blob/84e16e43092614bae262ca59651cb9d77e31a255/Computability/DiophantineConsistency/candidates/projected-factorial-radius/PROOF.md) | Factorial radius and low-digit radix variant; the 667-coordinate natural body. |
| [`candidates/projected-radius-integers/PROOF.md`](https://github.com/VladimirReshetnikov/ProveIt/blob/84e16e43092614bae262ca59651cb9d77e31a255/Computability/DiophantineConsistency/candidates/projected-radius-integers/PROOF.md) | The source body over integers with explicit sign recovery and monic projection. |
| [`research/main-root-and-modulus-signs/README.md`](https://github.com/VladimirReshetnikov/ProveIt/blob/84e16e43092614bae262ca59651cb9d77e31a255/Computability/DiophantineConsistency/research/main-root-and-modulus-signs/README.md) | The 21-sign reduction supplying the 79-predicate predecessor. |
| [`candidates/projected-radius-comparison-base/PROOF.md`](https://github.com/VladimirReshetnikov/ProveIt/blob/84e16e43092614bae262ca59651cb9d77e31a255/Computability/DiophantineConsistency/candidates/projected-radius-comparison-base/PROOF.md) | The 78-predicate source; signed comparison-base normalization is an existential lift, not a pointwise positivity inference. |
| [`research/paired-index-guards/LOCAL_FACTORIAL.md`](https://github.com/VladimirReshetnikov/ProveIt/blob/84e16e43092614bae262ca59651cb9d77e31a255/Computability/DiophantineConsistency/research/paired-index-guards/LOCAL_FACTORIAL.md) | The 77-predicate local factorial/index bridge. |
| [`research/factorial-radius-guard/PROOF.md`](https://github.com/VladimirReshetnikov/ProveIt/blob/84e16e43092614bae262ca59651cb9d77e31a255/Computability/DiophantineConsistency/research/factorial-radius-guard/PROOF.md) | The 76-predicate source; factor lower bound restores omitted factorial index signs before semantic use. |
| [`research/factorial-radius-output-sign/PROOF.md`](https://github.com/VladimirReshetnikov/ProveIt/blob/84e16e43092614bae262ca59651cb9d77e31a255/Computability/DiophantineConsistency/research/factorial-radius-output-sign/PROOF.md) | The 75-predicate source: an exact source-row identity restores the factorial output sign before closure. |
| [`research/factorial-radius-output-sign-profile/`](https://github.com/VladimirReshetnikov/ProveIt/tree/84e16e43092614bae262ca59651cb9d77e31a255/Computability/DiophantineConsistency/research/factorial-radius-output-sign-profile) | Literal raw and compact 75-predicate equations and domain ledgers used here. |

The full dependency pins of the last source profile are preserved in
`upstream/SOURCE_PINS75.json`. The two final inherited guard proofs are
included verbatim at this directory's root. The preceding references
identify the larger existing proof; they do not replace it with a new
end-to-end formal certificate.

## What the new independent verification establishes

`check_pair_guards.py` verifies every one of the six exact row-sum
identities, every original and replacement guard, the full copied body,
complete signed monic projection certificates, and all expanded quartic
coefficients for the 69-predicate profiles. `check_fused68.py` additionally
verifies all 22 repeated-square rows, the carrier identity, all 68 guard
rows, all three final projection certificates, and every final quartic
coefficient. Both check the exact copied source bytes.

These are finite exact integer-algebra checks, not tests at sample values.
The unrestricted witness implications are proved in
`PROOF_PAIR_GUARDS.md` and `PROOF_FUSED68.md`, using the classical
three-square theorem for the range of `a^2+b^2+c(c+1)`. The verification
does not decide existence of zeros, search for proofs of contradiction,
rebuild the logical endpoint's full Lean closure, or emit an internal ZFC
proof. The final claimed ZFC-provable equivalence is the ordinary
mathematical composition of the new proved transformations with the
explicit inherited calibration.
