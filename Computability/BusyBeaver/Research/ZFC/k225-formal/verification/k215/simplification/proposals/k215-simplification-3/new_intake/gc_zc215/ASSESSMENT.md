# Review of the newly arrived proof-simplification / GC-ZC215 packet

## Source and scope

Read on 2026-10-21 from [the exact incoming ZIP at commit 05d063acef885d47be5a2ce6645b046f98f7ea02](https://github.com/VladimirReshetnikov/ProveIt/blob/05d063acef885d47be5a2ce6645b046f98f7ea02/docs/incoming/Proof_Simplification_and_GC-ZC215_2026-10-21.zip), through the authorized GitHub connector.

ZIP SHA-256: `ab3c6c40a6c8da7fe6dbbfa35a35c204df904137463c6667b3d989991ed1c2c0`.

No received executable was run. `audit_received_data.py` is an independently written finite checker and reads the ZIP as data. It checks all 81 manifest entries, exact table/source interfaces, local transition blocks, and a complete blank prefix. `independent_intake_audit.json` records its results. No Lean/Rocq compiler or full symbolic-runtime rederivation was run. The earlier candidate audit was left unchanged.

## Effect on the recommendation

1. **Keep CM215 as the easiest new formal endpoint by transport from the verified original.** GC-ZC215 is not an exact local transformation of that original. Its local merge is relative to a newly allocated 216-state precursor; the larger scheduler/compiler change still needs formalization.
2. **Add the ZC-style zero-debt architecture as a serious proof-oriented alternative.** Its occurrence-injection proof is considerably cleaner than ST215/common-pop215's quantitative diagonal resource proofs, and its direct command-root initialization avoids their synthetic-AX recovery. This is a real improvement in those obligations, not merely a smaller source count.
3. **Do not claim it beats the original from scratch overall.** The original has a theorem-valued all-zero stack and needs no protected-tail resource theorem at all. ZC introduces a new enumeration and injection proof. The new packet itself makes this distinction and does not claim a shorter completed Lean/Rocq development.
4. **For a clean alternative pedagogy, prefer the basic ZC four-command architecture over adding GC solely to save one command in GEN.** The GC hybrid removes the counter-loading J(i) step, but it also requires a changed AX binder contract, a gate-nonfalsity lemma in GEN, and an extra physical decoder merge. There is no measured proof-size gain for those additions. The explicitly reviewed new hybrid is nevertheless an actual pinned 215-state candidate, not merely a source proposal.

## What overlaps the current simplification proposal

The packet's `proof_refactor/REPORT.md` and prototypes largely agree with the current refactoring direction:

- Prove offset-bisimulation symmetry once, eliminating the 2,240 mirrored checks across 16 Lean backward-check modules.
- Compress Rocq's certificate with sentinel-bit path integers, retaining exact decoded rows.
- Since all offsets are zero, consider ordinary bisimulation with a sufficiently large or parameterized path decoder. The present ordinary decoder's 128-bit fuel would corrupt 622 pairs; the longest path is 176 bits. Retain the offset decoder's 512-fuel behavior during migration.
- Share decoder trace prefixes only with context-sensitive contracts. Source-subtree identity alone does not justify replacing all 4,751 occurrence checks by 202 checks.
- Retain the existing machine-independent runtime and ZFC-calibration layers; do not propose them as missing abstractions.

The proposed Lean symmetry proof is 61 lines, `Cert215Compact.v` is 190,411 bytes versus the 1,499,170-byte original, and `PrefixCredit.v` is a 107-line standard-library prototype. **All three are explicitly UNCOMPILED.** They contain no advertised admissions, but source inspection is not kernel checking.

The 1,118.74 seconds associated with backward modules is a sum from a historical successful build, 24.94% of its 4,485.41 summed module seconds. It is not a measured speedup, elapsed wall time, or timing of the proposed patch. The archive says this clearly. Its existing-proof sources are pinned to `c9dc79323429112c698100f3226a6e4d56c8b782`; the target dense original hash is the same `fdbcef...0090` as our verified baseline. Do not silently attribute these incoming ideas or prototypes as newly produced work in this review.

## The actual new machine

- Correct native table: `hybrid215/machine.native.tm`, also `gc_zc215_start74.native.tm`.
- Native SHA-256: `4122c18a347028ee6643428b70a8d5c81218d4937d672be3626981d7b50bf503`.
- Canonical SHA-256: `b9137bf41deec9dd58dad10730da8521b74489bb4590bf5be3a21ca1c5296072`.
- Source SHA-256: `401bd1c9f08fcd63790b580f63ea942b1e4a1045cdd600bb1bd172fb06d01e8a`.
- 215 working states, 430 rows; native start 74, canonical start 0. Both presentations retain the separate halt label 254, not 215.
- Source: 203 distinct subtrees, 4,752 leaves, maximum address depth 47, total address length 160,312.
- Claimed full runtime: 6,177 arbitrary-natural guarded cases, 1,698,909 symbolic rules, all 430 rows. We checked receipt/input hashes but did not rerun that proof constructor.
- Independently replayed blank prefix: 117,004 transitions to native dispatcher 84, head -4, PC `000`, registers `(N,T,W,A,D,H,X,Y,L)=(1,0,5,0,0,0,0,0,0)`, gap 20, a nonempty mixed spare list, exactly 86 one-cells and zero elsewhere.

The whole tape was independently reconstructed from the declared frame and compared with both native set-based and canonical byte-array simulations. This confirms a genuine command-root frame, not just a plausible register tuple. The incoming raw runtime file has a start-0 serializer comment; the final native artifact correctly says start 74. We verified the transition rows are identical, so its runtime receipt transports across that header correction. The earlier 69,143-step frame is intermediate and must not replace the 117,004-step root in the proof.

## Why zero debt is a genuine simplification

The four-command parser uses DROP tag 0, NIP tag 1, MP tag 2 and AX tags at least 3. DROP and NIP each have one field. The changed refill returns to the root so that initial N=1,L=0 enumerates every raw candidate `0,1,2,...`, including the nonempty word `[DROP]` encoded by zero. Subsequent nonempty continuations are stored with a successor, preserving final zero-valued DROP commands.

For each NIP occurrence `(candidate n, position j)`, replace that one NIP by DROP and re-encode the entire word as m. Strict monotonicity of Cantor pairing and successor gives m<n. Parsing round trips preserve position j. Raising that same DROP back to NIP uniquely recovers n, so this is an injection from pop occurrences into push occurrences in strictly earlier candidates.

Consequently every finite execution prefix has at least as many DROPs as NIPs; immediately before any NIP, at least one unmatched safe push exists. MP and AX need only contribute nonnegative stack length. No AX batch-size, diagonal-density estimate, finite reserve computation, or positive initial safe-head reserve is needed. The opaque initial tail 5 is never exposed. A logical finite wrapper of theorem heads handles numerical zero aliases without treating numeric code magnitude as stack length.

The argument is sound on its stated interfaces. It crucially requires exact parsing round trips, equal push/pop arity, strictly monotone encoding, exhaustive increasing enumeration from zero, preservation of the stack across candidates, and actual execution remaining a prefix of that schedule. It does not apply automatically to the original's cutoff-four scheduler or to skipped-candidate/forced-transfer variants.

Completeness also becomes simpler at the scheduler layer: exhaustive enumeration from zero requires one successful encoded word, rather than a separate cofinal family above an arbitrary cutoff. Strict residual descent and termination of arithmetic macros are still required. The generic 107-line Rocq prototype proves only finite-list/injection consequences; its candidate-specific codec and machine-schedule hypotheses remain to be discharged.

## GC's limited additional saving

GC changes only AX's ninth head from `Q_D(oldH)` to `Q_C(oldH)`, leaving the numerical calculus and other axiom families unchanged. The source delta is register operands 4 to 3 at ordinals 46 and 51; addresses, primitive kinds and jump depths remain identical.

GEN can then use:

    B_X; DROP; NIP; AX(i;0,0); NIP^9; DROP; NIP; NIP.

This removes J(i). But the AX gate need not be zero now. The final cleanup tests its saved value, so one must use the fact that the gate is either zero or implication-coded, hence not falsity 1. Reusing the old GEN proof by textual substitution would miss this obligation. Other strong-compiler blocks reportedly need only the discarded ninth head's non-1 tag, so their binder value is irrelevant; this is a proof-reuse claim to verify when formalizing.

The physical merge combines unmerged roles 129 and 303. Their only incoming edges write distinct predecessor markers, so the invariant is simpler than CM's exceptional incoming history. Our finite audit checked the complete incoming census, all unchanged rows up to the state map, and exact whole-tape block lengths 1,3,1,5 for the four role/read combinations. Nevertheless this establishes equivalence only with the new 216-state precursor. It does not transfer the original 215-state kernel endpoint by itself.

## Boundary and other claims

The packet asserts an ordinary all-natural consistency calibration for the corrected exact machine, relying on the explicitly inherited numerical-calculus/ZFC theorem. Our assessment finds its written zero-debt and changed-GEN arguments coherent and confirms their finite machine/startup interfaces. This does not constitute a new full independent mathematical rederivation of every layer, and still less a compiled exact-table endpoint.

The packet claims no 214-state machine. It also includes a correction rejecting both SB215 and SB215-AB because their CC3 return targets ordinal 23 instead of the scheduler, eventually manufacturing cache 1. We read that correction, but did not rerun its nested archive. Its abstract fairness theorem cannot repair a wrong concrete return. FT215 is explicitly excluded from that rejection.

## Files to use

- `received.zip`: complete exact incoming source archive.
- `receipt.json`: verified source URL, Git blob identity, ZIP bytes and hash.
- `audit_received_data.py`: owned independent finite audit, executable with `python3 -I` and no external dependencies.
- `independent_intake_audit.json`: successful finite replay and exact scope.
- `text/`: selected verbatim README/proof/report excerpts read for this assessment, not executed.

The prior `candidates/` package remains unchanged. This supplement is the appropriate place to qualify its earlier “no demonstrated overall winner from scratch” conclusion: the new zero-credit architecture is a strong conceptual challenger on initialization/resource accounting, but still does not establish a shorter complete proof than the refactored original.
