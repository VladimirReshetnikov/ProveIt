# Composed weak-cone native Grill compiler: 205 complete operations

For fixed program `011`, the complete polynomial now costs **205 operations = 92 multiplications + 113 additions/subtractions**, with 31 positive witnesses and 11 comparison residuals. The raw-native alternative costs **229 = 98M + 131A**, with 37 witnesses and 20 residuals. This composes the frozen weak-input-cone change and the frozen phase-residual compression; it introduces no further arithmetic transformation.

The full polynomial and supplied positive zero set are exactly those of [the weak-cone 208 parent](grill_tag_native_weak_cone.md). The relationship to [the strong-cone 206 compiler](grill_tag_native_phase_residual206.md) uses a signed affine substitution. Its positive witness fibers are not identified. The inherited fixed-program language has an ordinary positive input and existentially packed unbounded duration; no universal Grill program or input decoder is established.

## 1. Frozen sources and the two composition orders

The [compiler](grill_tag_native_composed205.py) authenticates these sources before execution and again on warm public calls:

| Role | Source | SHA-256 |
|---|---|---|
| Canonical weak parent | `grill_tag_native_weak_cone.py` | `8f636a7954fce4335c2977baf849da0107b29d146aaa008fbb9732acedcf60b9` |
| Phase-residual rewrite and canonical strong reference | `grill_tag_native_phase_residual206.py` | `b9eaa5edf08f355607adf496d9477b806960c3438a81099f64cf08d0b7471af1` |

Both sources pin the same phase-sharing ancestor, SHA-256 `760ce9a0ea6e6020ecb52737ccc5c4197f7b84a212c73dc351b9ae3e6ef60069`, and propagate authentication through the native parent and its 72 inherited source dependencies.

The new builder first obtains the complete canonical weak208 packet, applies the frozen phase-residual transformation, and corrects the resulting parent-specific provenance to describe that actual weak source. Separately, it obtains the complete canonical strong206 packet and applies the frozen weak-width transformation. It requires exact typed equality of twenty normative fields from the two resulting packets: the entire certificate and polynomial schedules, every comparison and active interface, all supplied coordinates, tile maps and groups, native factors and root/projection interfaces, region data, and the full ledger.

The independently checked equality of these complete schedules establishes that the arithmetic rewrites commute on the actual compiler. It does not rely on comparing only the outer wrapper or only the displayed cost totals.

## 2. Same-coordinate polynomial identity with weak208

Let `F208` denote either finalizer mode of the weak source, and `F205` its corresponding composed mode. The phase proof expands the literal source definitions

\[
S_p=\widehat S_{2p}+\widehat S_{2p+1}-2,\quad
J=\sum_pS_p,\quad P=(B-1)J+1,\quad
T=\sum_{p=1}^{m-1}(m-p)S_p.
\]

The old phase forms are

\[
\operatorname{Next}=mJ-T,\qquad Q=(m+1)J-mS_0-T.
\]

The exact residual identity is therefore

\[
B\operatorname{Next}+q_0-Q-mP
=m(\widehat S_0+\widehat S_1)-(B-1)T+q_0-(J+3m).
\]

For `m=1`, this simplifies to `q0-1`. The proof treats `B`, all `2m` original hats, and `q0` as atoms, expanding `J` and `P` from their actual definitions. It needs no zero, Boolean, sign, or phase-validity hypothesis. In particular, changing the formula that computes `B` by weakening the input cone does not affect the identity; the compared weak-parent and child sources compute the same `B`.

Only the two operands of the phase-residual subtraction change. Their difference is identical. Every other residual, every native unit factor, and all subsequent finalizer arithmetic is unchanged. The complete expression DAG is checked using just this separately proved residual identity as a cut. Thus

\[
\boxed{F_{205}(x,Z,\mathbf y)=F_{208}(x,Z,\mathbf y)}
\]

on all integer or rational tuples, indeed as a polynomial identity over any commutative ring. The identity map is consequently a full zero-set bijection on the supplied positive domain. This statement applies separately to the raw and unit modes; it does not equate their polynomials with one another.

## 3. The signed diamond with strong206

The strong206 source computes `P0=3x+Z_s`; the composed source computes `P0=x+Z_w`. The literal affine identity

\[
3x+(Z_w-2x)=x+Z_w
\]

is checked first. A second complete source-DAG proof then compares all residual operands, active interfaces, native factors, and the entire final polynomial under the resulting width cut. This proves

\[
\boxed{F_{205}(x,Z_w,\mathbf y)=F_{206}(x,Z_w-2x,\mathbf y).}
\]

Equivalently, the diagram formed by the strong/weak width rewrite and the phase-residual rewrite commutes at the level of the **complete emitted source** and at the level of the **complete polynomial under substitution**. The checker establishes both assertions independently from the actual two parents.

The integer substitution is invertible, but its positive-domain restriction is not onto. Every positive strong206 tuple maps to a positive composed205 tuple by `Z_w=Z_s+2x`, preserving every residual and the full output. For a general positive weak tuple, `Z_s=Z_w-2x` can be nonpositive. For instance, `x=Z_w=1` gives `Z_s=-1`. The public `integer_pullback` exposes this fact and makes no positivity claim about its result. The saved checks also show different full outputs at identical all-one strong and weak tuples.

The equality of existential positive-input languages comes from the independently proved weak208 semantics and whole-period padding theorem, not from assuming the signed pullback is positive. Since composed205 and weak208 have the same positive zeros, that language theorem transfers immediately. No particular positive weak fiber or proposed duration is preserved by rebuilding a strong padded accepting history.

## 4. Preserved input and native scope

The current input cone remains

\[
P_0=x+Z_0>x>0.
\]

The unchanged computed endpoint and height are

\[
U_f=P_0V_f+x,\qquad D=U_f+\text{phase_initial}+\rho.
\]

Before applying any native classification, positive coordinates give `P0>=2`, `Uf>P0,Vf,1`, and `D>=5` with each required individual endpoint below `D`. All ordinary-input dyadic-width, range, radix, selector, sentinel, reverse-phase, and native constraints remain those of the weak parent. No native equation, protected-unit condition, witness, or input lane is deleted.

The weak parent's soundness and completeness theorem applies to every fixed finite natural Grill program with some admissible dyadic padding `P0>x`. Its full native extension uses the retained positive theorem, not a placeholder numerical Pell assignment. Duration remains arbitrarily large and existentially packed; the compiler does not take a fixed external trace horizon. Its interpretation allows word-closure witnesses with post-halt suffixes while recognizing actual halting at or before the closure length.

The weak and strong existential input languages agree by padding an actual halting word with whole periods of zeros and rebuilding the complete accepting history. The padding reference and the limitation on positive fibers remain in the inherited `input_cone` metadata. No universal recognizer, program translation, or universality decoder is supplied. The 205-operation result is a complete fixed-program cost, not a new universal-Diophantine operation record.

## 5. Full ledgers and metadata

The eight saved forms all save `1M+2A` relative to weak208 and one multiplication relative to their strong206 counterparts. Every emitted gate is live in the final polynomial. These counts include all kernels and the full finalizer, with each binary addition, subtraction, and multiplication—including multiplication by a nonunit constant—charged once.

| Program | Mode | Weak parent | Composed operations | M | A | Positive witnesses | Residuals | Degree upper bound |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| `0` | raw | 191 | 188 | 82 | 106 | 32 | 20 | 304 |
| `0` | unit | 167 | 164 | 76 | 88 | 26 | 11 | 737 |
| `1` | raw | 194 | 191 | 84 | 107 | 32 | 20 | 304 |
| `1` | unit | 170 | 167 | 78 | 89 | 26 | 11 | 737 |
| `011` | raw | 232 | 229 | 98 | 131 | 37 | 20 | 484 |
| `011` | unit | 208 | **205** | **92** | **113** | **31** | **11** | **1187** |
| `201` | raw | 240 | 237 | 104 | 133 | 38 | 20 | 520 |
| `201` | unit | 216 | 213 | 98 | 115 | 32 | 11 | 1277 |

The propagated full-source degree bounds are checked again on the composed schedules. `exact_degree` remains `None`; no exact degree is inferred from an upper bound. Same-polynomial equality with weak208 and the invertible linear substitution from strong206 preserve the respective true degrees, without determining them.

Current scope and `input_cone` describe the weak source. The current `phase_residual_rewrite` names weak208 as its actual parent and strong206 as the authenticated transformation source. `polynomial_identity_parent` explicitly states that `full_polynomial_identity=True` is relative to weak208. The old width-rewrite provenance is moved to `historical_weak_cone_rewrite`, because its ancestor comparison operands are no longer the current phase operands. Existing strong-ancestor metadata remains historical. Removed `Q`, `Next`, and old phase-operand registers have explicit proof-only formulas and are not presented as unpaid live outputs.

The public builder accepts a nonempty exact tuple of natural program entries, checking both complete rewrite orders and the symbolic identities for each built instance. The saved table covers these eight representative forms; it does not claim an exhaustive enumeration of all programs.

## 6. Public contract and replay

`build`, `checked`, `rewrite`, and `polynomial_source` validate the complete canonical source and metadata. `canonical_parent` returns the weak208 packet; `canonical_strong` returns the separate strong206 reference. `rewrite` accepts only the complete canonical weak208 packet. Returned canonical packets and source lists are defensive copies; validation returns the caller-owned packet.

`evaluate` and `identity` require exactly the complete coordinate key set and positive exact integers; explicit `signed=True` enables unrestricted exact integer algebra. `identity` checks the same-coordinate equality to weak208. `diamond_identity` checks the signed substitution to strong206 and reports whether the resulting strong tuple is positive. `integer_pullback` returns its possibly nonpositive slack, while `strong_to_weak_assignment` provides the positive one-way map.

The two direct source pins and all inherited runtime source pins are rechecked on public calls, even when canonical packets are cached. Authenticated bytes are compiled directly. Exact validation rejects float/Boolean coefficients, noncanonical source rows or metadata, wrong coordinate keys or types, and mutable cache substitution. Optimized Python execution is explicitly rejected because historical parents use assertions.

Replay needs the inherited Python dependencies, including SymPy. In this workspace the research virtual environment provides them; adjust its path elsewhere:

```sh
python3 grill_tag_native_composed205.py \
  --root /path/to/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue \
  --expect grill_tag_native_composed205.json
```

The parent source files may be placed beside this child or in the supplied WIP root. `--output PATH` writes a fresh deterministic receipt; `--expect PATH` checks exact typed JSON equality without modifying the saved receipt. The receipt includes all eight full schedules and their proofs. Warm-source tests modify only temporary private copies, leaving the repository and pinned files untouched.

The author receipt records eight literal commuting-source checks, eight complete same-coordinate proofs and eight complete signed-substitution proofs, covering 248 formal residual identities. Numerical checks include 128 full same-coordinate evaluations and 128 full diamond evaluations (64 signed coordinate cases), 3,968 residual comparisons, 16 rational diamonds, and 64 positive one-way assignment maps. Eight explicit identical-coordinate strong/weak separations prevent a mistaken positive-fiber claim. It also records eight ledger/liveness/metadata audits, 309 malformed-input rejections, 32 copy checks, and five private warm-cache pin rejections covering both direct sources, their phase and native ancestors, and an inherited kernel.
