# Independent mathematical and source review

Repository baseline: `f00ba53b331833c6cb64707bd90e48489e5610f5`.

This review checks the three retained mechanisms, their mathematical assumptions, their binding to the maintained definitions, and the exact proposed source changes. It does not rerun Lean and does not certify a full production dependency build. Compiler evidence is supplied separately by the authors. The final code-level nonduplication check is recorded in `novelty_audit.md`.

## Result

All three mechanisms are mathematically sound in the stated scope. R1's concrete patch changes two theorem interfaces and updates the maintained callers. R2's current-tree patch preserves statements and removes two source lines. R3 proves a stronger source implication, including a client for the literal current source rows; it does not yet migrate all downstream theorem signatures. These distinctions should remain visible in the report.

## R1: compare binary rotations through their actual parameters

### Definition-level argument

The maintained definition is

```
binaryRotation v W c =
  rotate (shiftDigits (2^v) (2^(W%v)) c) (W/v : ZMod n).
```

Consequently equal `W % v` and equal `(W / v : ZMod n)` give equal functions by rewriting alone. No bound on the entries of `c` occurs in this argument. The theorem in `packing_work/RotationCongruence.lean` uses the actual imported definition and changes neither the digit-normalization operation nor its carry term.

At `W = 47*(2011*s)`, both remainders are zero, and the quotient residues agree by the existing `physical_shift_eq`. The concrete replacement proof in `rephase-assumptions.patch` performs precisely these reductions. Its `current_numeric_kernel` uses the same constants and the same proof body after unfolding displacement.

### Transport and API boundary

`normalization_rephase` changes the constructed source using the existing source-function equality, then uses the equality of rotations to transport the already supplied normalization facts. The exact existing `carry` and `digits` arguments are retained. Removing the dummy-bound premise is legitimate because it was used only to obtain the old Boolean premise for rotation equality.

The stronger theorem is conditional on an existing normalization `Facts`. It does not assert bounded-carry normalization exists for every unbounded dummy function. The full marked/scalar/mask packing results retain their dummy bound, since their independent consumers still require it.

The patch updates the production `marked_packing_rephase` call and the focused check invocation. A search of maintained Lean source found no further calls of the changed rephase APIs requiring an argument migration. External callers may still need updates, or compatibility wrappers with unused old premises.

### Period extension and degenerate parameters

The period file proves equality after replacing W by `W % (v*n)`. Its two arithmetic reductions are exact: modulo v is unchanged because v divides v*n; whole-digit division becomes `(W/v) % n`, whose natural cast into `ZMod n` is unchanged. Thus v*n is a period for the displacement parameter, even for nonzero partial phases and unbounded digits.

No claim of a minimal period is justified or needed. The theorem also covers v=0 and n=0 under the totalized Nat/ZMod conventions used by Lean; then the displayed period can be zero and periodicity is tautological. The maintained client itself retains its original nonzero-cell assumptions.

### Essential distinction and controls

This does not generalize the Boolean identity `binaryRotation v 0 c = c`. With radix eight and constant digit c=8, zero-phase normalization gives `8 % 8 + 8 / 8 = 1`, not 8. Equality of two identically normalized rotations still holds. The supplied large-digit control exhibits this distinction.

Both coordinate equalities matter for a uniform theorem over arbitrary c. With v=3 and n=5, W=0 and W'=1 have equal whole-digit shifts but give constant outputs 1 and 2 for c=1. With W=0 and W'=3, the phases agree but a single origin bit rotates to a different position. The retained focused checks include a noncongruent-shift negative control.

### Accounting

The main module changes from 122 to 120 physical lines; the check module remains 80 lines. The total measured reduction is two lines across this concrete patch. The standalone congruence/period files are research artifacts, not hidden production helper cost. If adopted as additional production APIs, their source cost must be counted separately.

## R2: interval separation for internal quotient uniqueness

### Current-tree replacement

Suppose `q' = q+s+1` and `r<d`. Canonical additive order gives

```
q*d+d <= q'*d
```

using the additive difference `s*d`. It also gives `q'*d <= q'*d+r'`. Addition preserves the strict inequality `r<d`, so

```
q*d+r < q*d+d <= q'*d <= q'*d+r'.
```

The two division equations identify the first and last expressions, a contradiction. Swapping the roles of the two divisions gives quotient equality, and additive cancellation gives remainder equality.

The patch's orientation of the final equality is correct: `h.1.symm.trans h'.1` has exactly type `q*d+r = q'*d+r'`. The one ring calculation establishes `q*d+d+s*d = (q+s+1)*d`. No positivity or nonstandardness assertion is smuggled into those equalities.

### Scope of the abstract kernel

The kernel requires the canonical-order characterization `a <= b iff exists c, a+c=b`, additive order cancellation, and the discrete successor characterization for the uniqueness corollary. These are valid internal-natural interfaces. They do not identify internal naturals with external Nat, and no external induction on arbitrary internal elements is used.

The claim is not valid over an arbitrary ordered ring if remainders may be negative. For example over integers, `0=0*2+0=1*2+(-2)` and both remainders are less than 2. The canonical-natural-order hypothesis rules that out. Nor does ordinary ordered-field arithmetic provide integer-style quotient uniqueness: over nonnegative rationals, `1=0*2+1=(1/4)*2+1/2`, with both remainders below 2. The discrete successor law is therefore substantive.

No separate d>0 premise is needed: in canonical natural order, r>=0 and r<d already force d>0.

### What is actually simpler

The delivered current-tree patch still constructs the q-gap witness s and still has one ring equality. It removes the second witness expressing the remainder gap and removes the constructed witness for n<n. It replaces the nonlinear self-contradiction with a short order chain, using the existing `le_self_add` for its last inequality. `ObjectNaturalOrder.lean:144` already provides the required `CanonicallyOrderedAdd` instance. The private declaration shrinks from 11 to 9 nonblank lines, with no helper or import cost. No public signature or executable definition is changed.

The earlier zf packet changes other parts of `ObjectDivision`, but leaves this private theorem untouched. The separate checked `quotient_not_lt_ordered` theorem uses the already proposed high-level successor/ordered-semiring interfaces and has no existential gap witness. It is a counterfactual presentation, not the exact current-tree patch. Its nonnegativity premise on d follows from the existing internal zero-le theorem.

## R3: derive the port sign from the source equations

### Kernel proof

Let integers J,beta,L,N satisfy

```
J >= 0, L > 0, N >= 0,
L = (1+J*beta)^2 - 1,
N = (1+J*beta)*(1+L).
```

Write q=1+J*beta. Since 1+L>0 and N>=0, q>=0. The first equation gives q^2=L+1>1; integer discreteness now gives q>=2. Hence J*beta=q-1>0. Together with J>=0 this forces J>0 and beta>0. Then L=q^2-1>=3, so N=q(1+L)>=2*4=8.

The proof in `SourceGuardRecovery.lean` follows exactly this chain. It assumes only nonnegativity of J and N, not their strict positivity. It derives all of J>0, beta>0, q>=2, and N>=8.

### Exact source binding

The client extracts literal source rows 0 and 1. Its `change` statements match the maintained `SplitCertificate59.sourceRows` expressions. Linear combination yields the two integer equations above with J=x0, L=x24, N=x16, beta=ports0. The type `x : Fin 31 -> Nat` supplies J,N>=0, so only x24>0 is required.

The derived `source_Y_ge_two_no_beta` then uses x9>0 and x16>=8 to prove the old weak target `2 <= x16*x9`. Thus an independent positive-beta premise is mathematically redundant in the relevant positive-source setting. The new result does not imply the stronger numerical port bound `15 <= ports0`, nor sign/bound conditions on other ports; those remain genuine hypotheses elsewhere.

### Necessary signs and discreteness

The following are counterexamples to dropping individual abstract-kernel premises, not claimed full 59-row source solutions:

| Omitted premise | J | beta | L | N | Failure |
|---|---:|---:|---:|---:|---|
| L>0 | 1 | 0 | 0 | 1 | beta is not positive |
| N>=0 | 1 | -3 | 3 | -8 | q=-2 selects the negative branch |
| J>=0 | -1 | -1 | 3 | 8 | beta is negative despite q=2 |

The bound N>=8 is sharp for these scale equations: J=1,beta=1,L=3,N=8. Integer discreteness is used for the constants 2,3,8. Over the reals, J=1,beta=1/2 gives q=3/2,L=5/4,N=27/8, satisfying the sign and equation hypotheses but not N>=8.

### Integration and accounting

The source client establishes the exact new implication. It does not by itself remove hbeta parameters from all bootstrap and downstream wrappers. That migration requires choosing between public API changes and compatibility wrappers, checking callers, and counting all added helpers. No net source reduction should be attributed to the unperformed migration.

## Reviewed source identities

These hashes identify the reviewed inputs; later compiler receipts must match the final delivered files.

| File | SHA-256 |
|---|---|
| packing_work/RotationCongruence.lean | `5a442be62d610ed34a40590a58b9182558f8d72e3cedf9b323acf36f0caae33c` |
| packing_work/RotationPeriod.lean | `505bc0344b9f8a58465b7f9511a1ceac0964e2a187a6ff0f022f501ab91de500` |
| packing_work/rephase-assumptions.patch | `268d52817718ddc97b76aae04de5302c029d94f37aa2189ac779b62e1256a20c` |
| semantic_work/DivisionInterval.lean | `12362fcf49866854bcfb09cf72aba16532f11c765e074a33e149bf3537ea27ff` |
| semantic_work/ObjectDivision-interval.patch | `16187a3540203650e2740f269e016d4b2d14abe9b312e736c8e95fd8ba3fb5a5` |
| semantic_work/SourceGuardRecovery.lean | `33ff07f49e811dd30b288b2bdda71e5a61fb1384534cda344660421e3f8494a2` |
| semantic_work/SourceGuardClient.lean | `c61a814b88fb9d413b2869e055f4155af77b4b9863457aa5a62265bfcf38c35a` |

No proposed mathematical correction is required for these reviewed versions. The main presentation requirements are to preserve validation scope, distinguish the concrete current-tree patch from counterfactual higher-level simplification, and avoid claiming line savings for the added source-guard infrastructure or extrapolating large savings from the four-line combined patch reduction.

The final semantic compiler receipts were inspected after the authors replaced the superseded failed attempt. All final listed exits are zero, their SHA-256 values match the reviewed source files, and the eight reported semantic endpoints use only propext, Classical.choice, and Quot.sound. This is inspection of the authors' evidence, not another compiler run by this reviewer. The full ObjectDivision module build remains outside the recorded scope.


## Closing corpus and manuscript review

The exclusion audit was extended to commit `60fcb2a69b7f1fdd4c3592ea5f164223cad50abe`, with 43 placed packets a–zq. All seven newly placed reports, relevant notes and optional/future sections were screened; the new text/code corpus was searched for the retained mechanisms. R1, R2 and R3 remain distinct in the narrow scopes stated above. The full decision and closest new precedents are in `closing-novelty-audit.md` and the opening addendum to `novelty_audit.md`.

The main report and its validation-summary table were independently read. Their mathematical arguments, the two separate two-line patch counts, the unperformed R3 signature migration, and the boundary between checked kernels and complete uncompiled production integration are accurately stated. This manuscript check is separate from the authors' compiler runs and from the final source-byte freshness comparison.

The final historical-note supplement contains 16 additional substantive `.txt` files, all matching the original snapshot; the new seven-packet set contains 171 text/code payloads, all matching the closing snapshot. Focused review found no overlap affecting R1–R3. In particular, zf's internal-arithmetic note explicitly names only successor_step and division_exists as its division clients; its generic successor-order API is assumed available, without counting it again as the new interval-comparison mechanism.
