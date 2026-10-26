# Independent mathematical, novelty, and evidence review

Implementation and validation pin: `7fa06d530df54d4aeb2e18027409df082234c69e`.
Final novelty and compatibility refresh: `6f46a5e3480a2fa2e45993b8090826f256aeaa56`.
Toolchain: Lean 4.32.0, Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`.

This is an independent-task review of the mathematics, final candidate source, prior proposals, and the implementing tasks' receipts. It does not certify a complete repository build. Report prose was checked against those artifacts; the final generated result table must use the measurements below.

## Final disposition

Five mechanisms remain appropriate for the user's non-repetition request, subject to the narrow distinctions below:

1. A scale-parametric Pell ratio estimate.
2. Arbitrary-premise fragment construction with synthesized backward references.
3. Successor-first fork-certificate transport.
4. Projected support-difference separation.
5. The canonical selector/slack/maximum normal form of the quadratic square-pairing certificate.

The final refresh was decisive. Three new intake archives added 203 members and three manuscripts. The complete comparison now covers ten ZIPs, 2,193 inventoried members, and eleven primary manuscripts; `novelty_matrix.json` records 58 excluded mechanism families. The originally promising signed-congruence and affine-depth-budget ideas are explicit in the refreshed corpus and were removed from the final proposal list and candidate code bundle. Stronger local validation does not make a repeated idea new.

No mathematical counterexample or incorrect inference was found in the retained five mechanisms. Their value differs: A, B, and C have measured immediate source reductions; D and E are interface-expansion proposals whose additional clients must justify their overhead.

## A. Scale-parametric Pell ratio estimate

### Mathematical check

Write `xi = (U+1)^(2*r) / U^r`, `epsilon = 9 / (Y*(U+1))`, and `delta = 2*r*epsilon`. The shared original growth argument proves

`c <= k*xi*(1+delta)`.

The original hypotheses imply `U^r>0`, `Y*(U+1)>0`, and `k>0`. In particular `k` is the positive-index second Pell coordinate with parameter `2*U*Y^2+1`. Thus the proof's denominator clearing and cancellation are valid.

The same small-error argument gives

`(Y+1)*delta = 18*r*(Y+1)/(Y*(U+1)) <= 36*r/(U+1) < 1/2`.

The first comparison uses `Y>=1`; the strict final comparison uses `72*r<U+1`. For a real `factor>0`, `xi<factor*(Y+1)`, and `delta>=0`,

`xi*delta <= factor*(Y+1)*delta < factor/2`.

Dividing the shared estimate by `k>0` therefore gives `c/k<xi+factor/2`. No factor-dependent strengthening of the growth assumption is needed. A factor smaller than one is legitimate whenever its stated ratio bound holds. The strict positivity of the factor transports the final strict inequality; the proof does not divide by that factor.

The old `upper_estimate'` body never uses `hYr : U^r<=Y`. It is valid to omit this premise from the new generalized theorem while retaining it in the old wrapper. Factor one recovers that old theorem, and factor two recovers `NativeHalfBinomial.upper_estimate_scaled` exactly. The new theorem remains over the reals with Pell-specific hypotheses; it is not a generic ordered-field theorem.

The helper is placed in the existing lower-level `PellRatio90` file, avoiding a reversed import or a new cycle. Touching that lower dependency outside the requested subtree is necessary to remove the duplication inside the subtree and is disclosed in the report.

### Final evidence

`ratio/integration_checks.json` records exit zero for both complete modified production files. The final source hashes match `ratio/metrics.json`. The whole-file accounting is:

| File | Before | After |
|---|---:|---:|
| `PellRatio90.lean` | 472 lines / 23,237 bytes | 478 lines / 23,855 bytes |
| `NativeHalfBinomial.lean` | 244 lines / 12,130 bytes | 161 lines / 7,858 bytes |
| Total | 716 lines / 35,367 bytes | 639 lines / 31,713 bytes |

The net reduction is 77 physical lines and 3,654 UTF-8 bytes, including the new theorem and retained wrappers. All fourteen old theorem headers in the Pell file and all five in the native file are preserved by the recorded source comparison.

I independently compared `ratio/baseline_axioms.log` and `ratio/candidate_axioms.log`: they are byte-identical. The four audited declarations are `upper_estimate'`, `upper_estimate`, the native `upper_estimate_scaled`, and `source_half_binomial`. Their lists are `[propext, Classical.choice, Quot.sound]`. Previously flagged stale comments were corrected in the final source.

### Novelty qualification

No equivalent factor-parametric estimate was found in the eleven manuscripts. Prior half-radix proposals are division/remainder identities; P10/P11's Pell work concerns sign and parity transport. Neither supplies this analytic generalization.

## B. Arbitrary-premise fragment completeness

### Mathematical check

The collection theorem respects backward-reference semantics. If a first fragment produces `a::tail` and the recursively assembled remaining fragments produce `history`, their concatenation produces `history++(a::tail)`. The new reference to `a` is exactly `history.length`. References already compiled for the remaining premises retain their numbers, because the first history is appended as their suffix. Quantifying the lookup specification over every ambient `seen` is the appropriate append-stability invariant.

The theorem covers empty premise lists, repeated premises, and arbitrary arity. Repeated premises can still produce repeated fragments; no certificate deduplication or optimal length is claimed. The construction eliminates supplied existential witnesses inside a proposition. It does not use `Classical.choose`, change executable checker data, or alter parent-index meaning.

A source statement only about lookup in empty ambient history would need a separate append-stability argument before being used in this composition. The supplied universal invariant includes that obligation directly.

### Final evidence and resolved axiom drift

The complete modified `AnnotatedProofChecker` module compiled. `syntax/validation_manifest.json` records the successful full-module and axiom runs. I independently verified its recorded patch hash and compared the baseline and candidate axiom logs byte for byte.

An early implementation introduced `Quot.sound` into `fragment0` and `fragment1`. This was repaired before final delivery: the collector uses `Nat.le_refl`, whole-history equality transport with `congrArg`, and precise empty/singleton membership proofs. The final logs are identical for all eight audited public declarations:

- `fragment0` and `fragment1`: `[propext]`.
- `fragment2`, `fragment3`, `fragment_exists`, `certificate_exists`, `exists_checked_iff`, and `no_refutation_iff`: `[propext, Quot.sound]`.

The changed region decreases from 55 to 45 physical lines, from 50 to 39 nonblank lines, and from 2,643 to 2,460 bytes. The complete file changes from 388 to 378 lines at the validation pin. At the final refresh, an independent upstream lookup cleanup has already reduced that file to 380 lines; applying this patch preserves that cleanup and yields 370. The original four wrapper statements remain unchanged.

### Novelty qualification

P4 and P6 already propose shared `run`/`Produces` laws and certified fragment composition. P6 `notes/syntax.txt`:76–88 explicitly mentions `fragment2` and `fragment3` and warns about reversed histories. Do not present that infrastructure as new. The retained additional contribution is the arbitrary-premise list compiler, suffix-history-length parent indices, and its lookup invariant. That specific construction is absent from the reviewed corpus.

## C. Successor-first fork certificate

### Mathematical check

On an output `n+1`, natural cast addition and cancellation turn the fork certificate into the ordinary pairing certificate for `(n,a+1,b)` without a guarded predecessor-cast identity. The equivalence keeps each witness `t,s,m` pointwise.

The zero boundary is impossible: the last original row is `out-1-m*m-(a+1)-t*b=0`, with all inputs natural. At `out=0`, nonnegativity of `m*m` and `t*b`, together with `a+1>=1`, contradicts the row. Splitting zero and successor therefore proves the existing predecessor-based equivalence with exactly its old hypotheses.

The final production patch adds the named theorem `forkCertificate_succ`. The impossible-zero proof is local inside `forkCertificate_iff`, not a separate named positivity lemma. Soundness applies pairing soundness and `congrArg Nat.succ`, using `Nat.succ_pred_eq_of_pos`; completeness reuses the original pairing witnesses at the successor output.

### Final evidence

The complete modified `AnnotatedSyntaxGraphs` module compiled. This is an exact production-module check, not merely the earlier copied-definition fixture. The final patch hash matches `syntax/validation_manifest.json`.

The changed region decreases from 37 to 34 physical lines, from 34 to 30 nonblank lines, and from 1,727 to 1,486 bytes. The complete file changes from 169 to 166 lines and from 7,518 to 7,277 bytes, including the new successor theorem.

I independently compared the baseline/candidate logs: all seven audited declaration outputs are byte-identical. These cover the three fork-certificate theorems, `forkGraph_degree`, `forkGraph_binaryOps`, `treeGraph_witnessCount`, and `fixedBodies_graph_counts`; all list `[propext, Classical.choice, Quot.sound]`. Together with B this gives fifteen audited public syntax declarations with unchanged axiom outputs.

### Novelty qualification

No manuscript proposes this exact successor certificate equivalence and isolated zero boundary. It is distinct from general codec interfaces and prior nine-coordinate positive/natural packaging.

## D. Projected support-difference separation

### Mathematical check

The generic theorem is valid for additive commutative groups `G,H`, an additive homomorphism `pi:G→H`, a subset `S`, and an ambient translation `t`. If a nonzero `f x` requires `pi(x-t)∈S`, both nonzero values at `x` and `y=x+delta` would give two elements of `S` whose difference is `pi delta`. Therefore `pi delta∉S-S` forces `f x=0` or `f y=0`.

The concrete implementation keeps the translation in the full group `ZMod (N*cellLength)` and projects only the support test to the cell group. It does not discard whole-cell motion. The set difference is additive-group subtraction, not truncated subtraction on naturals.

For the native cell of length 4,831, the coarse support is `[0,583] ∪ {1203,1807}` in the residue group. Displacement 606 is outside its difference set. Small interval differences, exceptional-point differences, and their wrapped residues all avoid 606. The formal certificate uses the existing `CoarseSupport` definition.

The baseline already has a private natural-number `no_difference_606` theorem. The proposed simplification packages that established obstruction as a reusable projected-support rule; it does not discover the obstruction.

### Final evidence and cost

`arithmetic/final_validation.json` records exit zero for `SupportDifference` and the complete `NativeTemporalSupport54` client. An earlier missing `NeZero cellLength` instance was fixed locally before the final successful check. The preexisting public theorem statements are retained.

The helper is 36 lines / 1,474 bytes. The client changes from 82 lines / 4,190 bytes to 89 lines / 4,025 bytes. The combined count is therefore 82→125 physical lines and 4,190→5,499 bytes. The client shrinks in bytes but grows in lines; the total grows by 43 lines and 1,309 bytes. This is an interface simplification for future reuse, not an immediate net compression claim.

### Novelty qualification

No reviewed manuscript contains projected support-difference separation. P9's univariate degree envelope, P11's one-hot support classification, prior sparse placement, and finite-fiber sum transport have different mathematical conclusions. The report properly requires future additional clients before claiming amortized savings.

## E. Canonical square-pairing witnesses

### Mathematical check

The first row forces the natural selector `t` to zero or one. At zero the other rows give `a<b`, `m=b`, `s=b-a-1`, and `z=b*b+a`. At one they give `b<=a`, `m=a`, `s=a-b`, and `z=a*a+a+b`. These are exactly the branches of `Nat.pair`.

The normal form therefore determines all three auxiliary witnesses in addition to the output. At `a=b`, the only selector is one and the slack is zero. At `a=b=0`, the certificate remains valid with output zero. Soundness, deterministic completeness, and witness uniqueness follow. Unrestricted integer witnesses would invalidate the same branch/slack argument, so the existing natural domains must remain.

The stronger theorem can simplify clients needing witness uniqueness or exact reconstruction. It is not automatically shorter than the existing output-only sound/complete pair. No migrated-client net saving is claimed.

### Final evidence

The accepted artifact is `syntax/CanonicalPairingIntegration.lean`. It imports the production module and binds

`abbrev Certificate := DiophantineConsistency.QuadraticNatPairing.Certificate`.

It therefore proves the result for the actual production predicate; the earlier copied-definition limitation is resolved. Its compile exit is zero in `syntax/validation_manifest.json`, and I independently verified the recorded SHA-256 `b35e9251ee1ff698f77b3890217861a7676c9851cb80282ef82f83b5231c4e99`. Its normal form, soundness/completeness consequences, and uniqueness are checked. This is an optional extension importing the existing module, not a supplied replacement patch with claimed source reduction.

### Novelty qualification

P11 already projects inverse graphs through `Nat.pairEquiv`, including clients in the same quadratic pairing module, and proves canonical Euclidean division quotient/remainder/slack witnesses. The retained claim must be narrower than generic canonical-certificate reasoning. It is specifically the selector/slack/maximum normal form of the existing square-pairing rows; that result is absent from the eleven-manuscript corpus.

## Latest-source compatibility

`syntax/latest_comparison.json` records independent application checks for all four retained production patches against refresh commit `6f46a5e…`. All succeed. Among their existing target files, only `AnnotatedProofChecker` differs from the validation pin; the patch preserves its separate eight-line lookup cleanup. The production `QuadraticNatPairing` source used by the optional extension is unchanged.

Patch applicability is not a full Lean recheck of the refreshed dependency tree. The report correctly keeps compilation evidence tied to the original pin and explains why users on the refreshed tree should apply patches rather than copy baseline whole-file candidates over current work.

## Report QA findings and acceptance criteria

The revised five-proposal report accurately distinguishes immediate deletions from interface expansion, keeps old public contracts, scopes compilation claims, and discloses the late novelty exclusions. Three earlier wording issues were corrected: support groups now explicitly commute, the fork zero proof is described as local, and the repeated depth-budget section is removed entirely. The report's source and refreshed-corpus counts match the recorded inventories.

Two nonblocking editorial precision updates were sent to the parent: state the final 58 exclusion families if reporting a final count; and spell out the Pell coordinate identifications `c=psi_(a+2)(2r+1)` and `k=psi_(2*U*Y^2+1)(r+1)` instead of referring to identities not displayed in the proposition. The exact theorem signature in the supplied source already contains both identities.

Acceptance conditions for the packaged result:

- Count helpers, imports, compatibility wrappers, and certificates in every net size claim.
- Treat exact final axiom outputs and source hashes as evidence; omit superseded failed prototypes from the accepted code bundle.
- Preserve the distinction between the original-pin full-file checks, the production-importing optional extension, and refreshed patch applicability.
- Do not infer runtime or proof-object savings from line counts or single successful compiler runs.
- Keep the sign-congruence and affine-depth mechanisms only in the exclusion record, not as additional new recommendations.
- Make no claim that these edits prove a new consistency theorem or close the project's separate native/internal logical gaps.

The mathematical, novelty, and evidence review is complete for the five retained mechanisms. The report is suitable for delivery after final generated-table and PDF/artifact consistency checks by the parent task.
