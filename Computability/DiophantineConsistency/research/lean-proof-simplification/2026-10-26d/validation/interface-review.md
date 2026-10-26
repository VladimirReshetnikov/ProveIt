# Independent review of packaged proof simplifications

Reviewed four complete source files by inspection against the pinned original definitions and theorem statements. This review did not itself recompile the packaged files; the root agent owns final compilation after import/path changes. No reviewed source was edited.

## Findings

No hidden hypothesis strengthening, circular use of the original target theorem, or unsound change of domain was found.

- **ScannerCore:** `scan` uses exactly the existing `Nat.rec` transition scheme. The generic successor, fixed-point, invariant, and reject-or-invariant proofs are direct inductions. `scan_reject_or_invariant` deliberately permits the rejecting state to satisfy `Good`; its disjunction is not exclusive. To infer `Good` from nonrejection, retain the separate nonrejection evidence. Each scanner still needs its concrete step-preservation proof, initialization argument, parser/code correspondence, and primitive-recursive realization. Do not infer termination, fuel sufficiency, or absence of rejection from this generic interface. Preserve the raw `Nat.rec` definitions when shortening existing proof bodies; switching to another iteration representation may disrupt definitional equations used in the executable program proofs.
- **FinitePushforward:** arbitrary `p` retains all collisions. `Semiring R` is sufficient; multiplication order is retained, so no unadvertised commutativity assumption is needed. The natural-number mass/convolution instances are straightforward. In `word_foldStencil`, this identity discharges only the finite-sum interchange and selection step. The separate modular argument using `pow_mod_length` still turns the reduced exponent into the original exponent. It does not prove no-carry, position injectivity, or canonical-word uniqueness. Instantiating with `ZMod n` still needs the original finiteness/nonzero-modulus context.
- **ArithmeticRefactors:** residue identities preserve congruences modulo the field width; they do not turn cyclic subtraction into truncated natural subtraction. `[NeZero (N * L)]` excludes zero cell/radix modulus as needed. The exact scaled quotient/remainder identity requires `0 < s`; dropping it is false, since the right side retains `y / 2` at `s = 0`. The derived bound and parity lemmas need only the predecessor bound `y ≤ 3`, legitimately weakening the local current-digit requirements. Parity additionally retains the even-scale condition.
- **RotationRefactors:** the two signatures retain the original hypotheses, notably the absence of a `NeZero n` assumption. The source uses only `shiftDigits` and the new arithmetic lemmas; it does not invoke the original bound or parity theorem, despite importing the original module for the definition. No temporal alignment or digit Booleanity is assumed. It therefore is an actual alternative derivation, not a corollary of the theorem it purports to simplify.

## Validation architecture

The proposed sequence is appropriate:

1. Compile every shipped Lean module from its final packaged path against the exact original dependency environment, after all import-name changes.
2. Check each complete patched module independently, with the original public namespace and theorem names. It must not import its own old module, directly or transitively. The two relevant baselines are safe by inspection: `Representation` imports only Mathlib, and `NativeCyclicRotation` imports the earlier convolution layer; the generic arithmetic helper imports no project theorem.
3. Run `git apply --check` against the pinned tree and record hashes of the exact checked files.
4. Print axioms for all new proof interfaces and patched targets. This detects admissions or custom axioms, but does not prove that the proof avoids the old theorem; source/dependency inspection establishes that independently.
5. State separately which results are additive generic interfaces, which are complete checked module replacements, and which are architectural proposals. Compilation of the supplied modules does not by itself constitute a full downstream-library rebuild.

The code already uses appropriately narrow rewrite interfaces. In particular, leave `scan_succ`, the finite-sum rearrangement, and large circuit unfolding rules out of the global simp set unless a concrete use justifies adding them.

A minor optional cleanup: `ScannerCore` does not reference the imported `Function.Iterate` API; its current proofs appear to need only core recursion/equality facilities. That is an import-size opportunity, not a correctness issue and not worth additional broad testing.

## Source hashes at review time

| File | SHA-256 |
|---|---|
| `ScannerCore.lean` | `495810099ccad170f29e7ee115f7baecce1f6cbb08254172be7e866c5536ef74` |
| `FinitePushforward.lean` | `48fc9b1b5c41018e67964c4e374faa859bba99026cd2d9707aa8e50ec139c290` |
| `ArithmeticRefactors.lean` | `257426e1e8115c5f932e17175a3e49e703a35467439ca145797061b6512cf48b` |
| `RotationRefactors.lean` | `cc5f952a35118b79aacef0355453251d1f7a8e0de5a755ca0ca158002dc7a415` |
