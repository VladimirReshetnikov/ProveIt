# Exact phase-residual compression of the strong-cone Grill compiler

The complete fixed-arity compiler for program `011` now costs **206 operations = 93 multiplications + 113 additions/subtractions**, with 31 positive witnesses and 11 comparison residuals. This is an exact polynomial rewrite of the strong-cone 209-operation parent. The raw native version drops from 233 to 230 operations. No witness, input condition, or packed-duration condition changes.

The parent is [grill_tag_native_phase_sharing.py](grill_tag_native_phase_sharing.py), pinned to SHA-256 `760ce9a0ea6e6020ecb52737ccc5c4197f7b84a212c73dc351b9ae3e6ef60069`. Its proof and inherited semantics are in [the phase-sharing note](grill_tag_native_phase_sharing.md) and [the native word-closure note](grill_tag_native_word_closure.md). The child retains the **strong cone** `P0 = 3*x + Z0`, with every supplied coordinate a positive integer. It does not incorporate the separate weak-cone compiler.

## 1. A literal residual identity

Fix the number of phases `m >= 1`. These symbols denote actual parent source polynomials:

\[
S_p=\widehat S_{2p}+\widehat S_{2p+1}-2,\qquad
J=\sum_{p=0}^{m-1}S_p,\qquad
P=(B-1)J+1.
\]

Write

\[
R=\sum_{p=1}^{m-1}pS_p,
\qquad T=\sum_{p=1}^{m-1}(m-p)S_p=m(J-S_0)-R.
\]

The old phase forms satisfy the polynomial identities

\[
Q=J+R=(m+1)J-mS_0-T,\qquad
\operatorname{Next}=R+mS_0=mJ-T.
\]

Consequently its phase residual is

\[
\begin{aligned}
r&=B\operatorname{Next}+q_0-Q-mP\\
 &=B(mJ-T)+q_0-[(m+1)J-mS_0-T]-m[(B-1)J+1]\\
 &=mS_0-(B-1)T+q_0-J-m\\
 &=m(\widehat S_0+\widehat S_1)-(B-1)T+q_0-(J+3m).
\end{aligned}
\]

This uses neither a zero of another residual nor a Boolean, natural, or phase-valid selector hypothesis. It is an identity in `B`, **all `2m` original selector hats**, and `q0`. Both `J` and `P` are expanded from their actual source definitions; neither is admitted as an independent proof atom. The code checks the complete sparse expansion of both residuals in precisely those atoms. It also checks that the derived atom `B` is unchanged in the full source.

For `m=1`, `T=0` and `J=Shat0+Shat1-2`, so the same identity reduces exactly to **`r=q0-1`**. Unlike the preceding phase-sharing stage, this child therefore also improves the one-phase programs.

## 2. Paid source transformation and complete polynomial

For `m>1`, the child constructs the complementary weighted sum

\[
T=\sum_{p=1}^{m-1}(m-p)(\widehat S_{2p}+\widehat S_{2p+1})-m(m-1).
\]

It reuses the existing selector pair sums, the existing `J`, and the already-paid register `B-1`. It then replaces only the operands of the existing phase-residual subtraction by

\[
\left(m(\widehat S_0+\widehat S_1)-(B-1)T+q_0,\quad J+3m\right).
\]

For `m=1`, the replacement operands are `(q0,1)`. In both cases their difference is the original residual. All other comparison operands, the native unit factors, the native root coordinate and projection aliases, the finalizer beyond this subtraction, and the complete supplied-coordinate list remain unchanged.

The implementation prunes the **whole output dependency graph**, retaining every finalizer gate. For `011`, eleven old source gates disappear and eight new gates are emitted: one multiplication and two additions/subtractions are saved. The changed phase operands are not asserted to equal the old operands separately. A formal expression-DAG comparison proves the entire output identical after cutting only at the separately proved phase residual. It verifies every other residual and every native unit factor before accepting the packet.

Thus, separately for each finalizer mode,

\[
F_{206}(v)=F_{209}(v)
\]

as polynomials in every supplied coordinate. The raw source has the analogous exact identity `F230=F233`. These are all-value identities over integers, rationals, or any commutative ring; the raw and unit-mode polynomials are **not** asserted to equal one another. The identity map on coordinates is a full zero-set bijection within each mode, in particular on the positive-integer domain to which the imported computation theorem applies.

The old current-interface names `Q`, `Next`, `phase_lhs`, and `phase_rhs` are removed. Their mathematical values remain as explicit **proof-only historical formulas** under `proof_only_phase_formulas`; they are not unpaid live outputs. Current phase outputs are named `phase_residual_left` and `phase_residual_right`. The previous phase-sharing provenance is retained under `historical_phase_sharing`, and the active ledger describes only the emitted child source.

## 3. Complete ledgers and degree limits

All entries include the complete native kernels and the complete final polynomial, with every emitted gate live. Multiplication by a nonunit constant costs one multiplication. Additions and subtractions each cost one operation. Only literal constant folding, neutral-element simplification, structural common-subexpression reuse, and removal of dead source registers are free.

| Program | Mode | Parent operations | Child operations | M | A | Positive witnesses | Residuals | Formal degree upper bound |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| `0` | raw | 192 | 189 | 83 | 106 | 32 | 20 | 304 |
| `0` | unit | 168 | 165 | 77 | 88 | 26 | 11 | 737 |
| `1` | raw | 195 | 192 | 85 | 107 | 32 | 20 | 304 |
| `1` | unit | 171 | 168 | 79 | 89 | 26 | 11 | 737 |
| `011` | raw | 233 | 230 | 99 | 131 | 37 | 20 | 484 |
| `011` | unit | 209 | **206** | **93** | **113** | **31** | **11** | **1187** |
| `201` | raw | 241 | 238 | 105 | 133 | 38 | 20 | 520 |
| `201` | unit | 217 | 214 | 99 | 115 | 32 | 11 | 1277 |

Every listed form saves `1M+2A`. These eight complete sources are stored in the receipt. The public builder accepts any nonempty exact tuple of natural program entries and verifies the symbolic source identity for that instance, selecting the parent unchanged if a candidate is not cheaper. The table is evidence for these eight forms, not an exhaustive enumeration of arbitrary programs. Formal degree propagation is recomputed on the emitted child DAG; it matches the parent's bound. Exact degree remains unclaimed (`exact_degree=None`). Polynomial equality also preserves the true degree, whatever that degree is.

## 4. Input, duration, and theorem scope

The sole ordinary parameter is the positive integer `x`. The retained source computes `P0=3*x+Z0`, keeps the dyadic input-width lane and the strong height cone, and packs arbitrary nonempty duration existentially. It preserves the original selector, range, radix, sentinel, reverse-phase, ordinary-input, and native-unit constraints. There is no externally fixed trace horizon in this compiler, and no input decoding is supplied for free.

Its imported interpretation concerns a fixed finite Grill program and existential admissible dyadic padding. No universal Grill recognizer, universal program compiler, or universal ordinary-input decoder has been proved here. Consequently 206 is a cost for this complete fixed-program relation, not a new universal-Diophantine operation record. No claim about weakening the input cone or combining that separate transformation is made.

## 5. Exact guards, provenance, and replay

Public APIs are `build`, `checked`, `canonical_parent`, `rewrite`, `polynomial_source`, `evaluate`, and `identity`. `rewrite` accepts only the complete canonical 209-parent packet, not an arbitrary similarly shaped source. Full structural comparison distinguishes integers from booleans and floats, lists from tuples, and exact strings from subclasses. Evaluators require the exact coordinate key set and exact positive integers; `signed=True` enables only the explicitly algebraic signed-integer mode. Mutable public results are defensive copies.

The direct parent bytes are rehashed before every public canonical call. Its own guard reauthenticates the native parent and all 72 inherited source pins, including on warm-cache calls. Byte execution uses `compile` on the authenticated bytes rather than cached bytecode. The module explicitly refuses Python `-O`, because inherited historical checks use assertions.

The author receipt records:

- Eight complete formal polynomial identities and 124 comparison-residual identities.
- 160 complete integer evaluations, including 80 signed cases and 2,480 residual comparisons, plus 24 exact rational cases.
- Eight active metadata/liveness/degree audits, 259 rejected malformed inputs, and 24 defensive-copy checks.
- Three private warm-cache rejections after separately modifying the direct phase parent, native parent, and an inherited kernel source; each restored source reproduces the original packet.

Replay uses Python with SymPy through the inherited compiler dependencies. In this workspace the research virtual environment provides them; adjust that executable path for another installation. Put the child beside the pinned phase parent, or pass `--root` pointing to the repository's `native-stream-queue` dependency directory:

```sh
/tmp/diophantine-research-venv/bin/python grill_tag_native_phase_residual206.py \
  --root /path/to/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue \
  --expect grill_tag_native_phase_residual206.json
```

`--output PATH` writes a fresh deterministic receipt, including all eight complete emitted sources. `--expect PATH` checks exact typed equality against the saved JSON without changing it. The isolated guard tests modify only temporary private copies; the pinned parent and repository remain unchanged.
