# Concrete internal fresh streams and overlapping-start transport

`ValidatorEnvironmentStreams254` removes the disjoint-stream restriction from
the empty-bound-stack alpha client. For every internal source formula `p` and
any two starts `s,t` whose future labels avoid the stored free labels and
fallback 1, it constructs both literal-validator implications

```text
E(F,[],s,p) → E(F,[],t,p)
E(F,[],t,p) → E(F,[],s,p).
```

The result uses the checked [internal alpha theorem](validator_environment_alpha254.md),
which handles disjoint streams. If `s` and `t` have different residues modulo
2, their `+2` streams are already disjoint. If their residues agree, the proof
chooses a sufficiently large start of the opposite parity and composes the
two alpha implications through that encoding. Every label, remainder, source
formula and proof witness is internal to the arithmetic model.

The represented selector is

```text
alternateStart(bound,seed) =
  if seed % 2 = 0 then 2*(bound+2)+1 else 2*(bound+2).
```

Its fixed Σ0 graph is defined before the ambient model. The selected value
exceeds both `bound` and 1, and has the opposite residue from `seed`.
Foundation's existing `nth_le` bounds every stored vector coordinate by the
numeric code of the vector itself. Consequently the coarse bound `F+B+B'`
supplies avoidance of all free labels, fallback 1 and both bound stacks,
without introducing a maximum-fold computation. The numeric selector and its
resources need IΣ1; formula transport uses the checked IΣ2 alpha theorem.

`encode_formula_relabel` requires only `StreamFree(s,F)` and
`StreamFree(t,F)`, where `StreamFree(s,F)` means that every future `s+2*k`
avoids the free vector and fallback 1. The focused `encode_formula_next`
client compares the overlapping starts `s` and `s+2` from the single premise
`StreamFree(s,F)`. Its audit includes the concrete start pair 2 and 4 with the
empty free vector, uniformly for every internal source formula.

This supplies the change of binder start needed in the source universal rule.
It does not rename arbitrary accepted proofs or reconstruct source derivations.
The remaining compiler can use the [configurable encoder](validator_environment_labels254.md)
directly: its falsum code is already the literal validator's code 1. Comparing
it with a separate fixed encoder is optional. Source-proof compilation, ZF
axiom reconstruction and the reverse consistency endpoint remain open; no new
machine-state count is claimed here.

## Verification

The 138-line source and focused audit passed their first pinned Lean 4.32.0
check with **14 named axiom reports, 18 callers and the standard three axioms
only**. Six linter warnings remain: four in the source and two in the audit.
They concern a redundant simpa/simp step, an unreachable tactic, one unused
simp argument and two unnecessary `<;>` sequences. The exact successful bytes
are retained without a cosmetic recompilation.

The source took 3.644 seconds and the audit 3.080 seconds, using one thread,
4 GiB, default Lean proof limits and a 120-second timeout per command.
The source object hash was persisted before the audit and remained unchanged.
The [exact verification record](results/validator-environment-streams254-verification.json)
is preserved unchanged.

The runner reuses the exact checked alpha parent, 29 project objects, five
direct external boundaries and two toolchain providers. It checks 79 current
input paths and actual first-provider identities. There is no new direct
external boundary or Cantor object variant, and no dependency was built or
downloaded. The supplied external caches remain explicit boundaries, not an
attestation of an entire Foundation namespace.

The [history](results/validator-environment-streams254-history.json) retains
the exact successful source/audit/guard/logs, initial preparation and separate
maintained-default preparation. The portable runner changes only maintained
source/audit defaults. [Author and independent reviews](results/validator-environment-streams254-review.json)
record the successful evidence and the unbuilt default preparation, which
performs no proof compilation or compiler-version query.

## Reproduction

From the repository root, with the existing checked prerequisite objects:

```sh
python -B Logic/Interpretability/ZFCinPA/check_validator_environment_streams254.py \
  --dependency-root /path/to/dependency-checkout \
  --output /fresh/external/environment-streams
```

`--alpha-evidence` accepts a relocated copy of the exact parent record.
`--project-cache` may select a supplied cache containing all 29 prerequisite
project objects, and `--namespace-cache` a cache root containing the Foundation
namespace mirror. `--source` and `--audit` accept relocated copies of the frozen
successful bytes. `--prepare-only` performs no proof compilation or
compiler-version query.
