# Independent audit: bounded-horizon arithmetic companion for Report 64

Audit date: 4 October 2026. Verdict: **ACCEPT the arithmetic theorem and its exact displayed-construction ledger.** No mathematical correction is required to the frozen arithmetic proof. Transport to physical runs is a conditional corollary whose physical premise must be discharged by the separate Report 64 compiler audit.

The `65` in the source packet identifier is a provenance identifier. This audit is intended for integration into the single user-facing Report 64, not as a separate delivered Report 65.

## 1. Source binding and independence

Frozen source directory: `/workspace/shared/bounded-horizon-diophantine65-20261004`.

| Source | SHA-256 |
|---|---|
| `PROOF.md` | `5d9d7de3c9b6ca5551d7cd537b0e3570c0272af6716ba814453d5ad2123aea6a` |
| `MANIFEST.json` | `54d8abdcc872f628e9ae6639f4119b15cd1d4bacd33ba412ffd85155110b3824` |
| Retained physical proof | `85f5de45c0a30f8bdf45b82a613ef9e5a8c766b5d8215d17a3ebbbd0f60b370f` |
| Retained physical manifest | `e5d9f9a399ab9515a13b66ea4160b063a585c801002105b62f4528da516c1589` |
| Fresh independent checker | `fdec02843191eaa965c702bb540b98f2151a3fc1a149e6047edaf66959d7540f` |

All six entries in the frozen manifest were independently hashed and matched. The retained physical manifest's proof hash agrees with the retained physical proof. This checks provenance, not physical correctness.

The audit reconstructed the arithmetic directly from the fixed instruction semantics. The frozen checker and its evidence were inspected as source/data but never imported or executed. The auditor authored and inspected `independent_certificate_audit.py` before its execution. Its sparse polynomial representation uses sorted variable-name monomials, independently of the frozen checker's exponent-vector representation. All arithmetic is exact integer arithmetic using Python's standard library.

No author/upstream program, physical simulator, collision-schedule search, native-machine interpreter, Lean, Coq, or other proof assistant was run. Finite exhaustive tests enumerate complete candidate polynomial assignments after algebraic elimination; they do not follow a machine's enabled next transition.

All source file content reads used `O_NOATIME`. `source_snapshot_before.json` and `source_snapshot_after.json` record byte hashes, file sizes, modes, atime, mtime, and ctime at nanosecond precision; `source_preservation.json` records their comparison. No source file was edited or its metadata reset. The audit artifacts are in a separate sibling directory.

## 2. The theorem that is actually established

Fix one finite deterministic two-counter program, one initial state, distinct integer control-state codes, and one halt state. Every ordinary state has exactly its specified increment edge or zero/decrement pair. Add exactly one virtual halt self-loop. Let E count all these edges and Z count the zero edges.

For each externally fixed integer T >= 1, there is an explicit integer polynomial P_(M,T)(A,B;W), with positive integer native inputs A=a+1 and B=b+1, such that:

1. A positive witness exists exactly when the native program first reaches its halt state after at most T transitions.
2. If a witness exists, its entire tuple is unique, including all inactive selectors and all padded counters.
3. The tuple has exactly T(E+2) entries, and the displayed construction uses T(E+Z+4)+1 residual slots before summing their squares.
4. The final polynomial has total degree exactly four, including the inputs as variables.

This theorem follows independently of signal machines, universality, MRDP, or an unbounded-trace encoding. Its source anchors are frozen `PROOF.md` §§1–5, lines 5–166.

## 3. Independent reconstruction and correctness

### 3.1 Selectors and counter variables

For each time t<T and edge e, let w_(t,e) be positive and s_(t,e)=w_(t,e)-1. Impose s_(t,e)(s_(t,e)-1)=0 and sum_e s_(t,e)=1. Over integers these equations force one selected edge per time, with w=2 on that edge and w=1 on every other edge. In particular, inactive edges supply no arbitrary padding variables.

Use only A_1,...,A_T and B_1,...,B_T as additional witnesses, with A_0=A and B_0=B as inputs. The exact affine updates are

    A_(t+1)-A_t-sum_e d_e s_(t,e)=0,
    B_(t+1)-B_t-sum_e f_e s_(t,e)=0.

For every zero edge on a counter C, include s_(t,e)(C_t-1)=0. A selected zero branch therefore requires the corresponding native counter to vanish. A selected decrement gives C_(t+1)=C_t-1; since the next shifted counter is positive, C_t>=2. Thus the entering native counter is positive. This is the entire positive guard, with no slack witness or hidden residual. The reasoning requires one-hot selection and the positive-integer counter domain.

### 3.2 Control consistency

One initial source-code equation, T-1 target-to-next-source equations, and one final target-code equation give T+1 control residuals, also for T=1. Distinct codes and one-hot selectors make each equation compare actual states, not averages. There are no state witnesses.

Every solution therefore names a guard-valid deterministic trace ending at H. Conversely, a native trace that reaches H by T extends to length T by the unique virtual loop and supplies a solution.

### 3.3 Complete witness uniqueness

Induct from the fixed initial configuration. At an increment state there is exactly one candidate. At a test state, shifted value 1 permits only its zero edge; shifted value at least 2 permits only its decrement edge. This remains true when both edges have the same target. At H, exactly one loop is available. The chosen edge fixes both next counters by the affine updates. Consequently every selected edge, every inactive selector, and every counter witness is fixed.

Determinism and the prohibition on duplicate enabled edges are genuine assumptions, not cosmetic ones. An intentionally invalid fixture with two identical increment edges gives two distinct positive selector tuples, as expected; it is excluded by the source hypotheses.

## 4. Ledger, sum of squares, and exact degree

| Group | Residual slots | Maximum degree |
|---|---:|---:|
| Binary selectors | TE | 2 |
| One-hot selection | T | 1 |
| Two counter updates | 2T | 1 |
| Zero guards | TZ | 2 |
| Initial, linking, final control | T+1 | 1 |
| Total | T(E+Z+4)+1 | 2 |

The witness count is TE+2T=T(E+2). There are two additional input variables. If I is the number of increment states and C the number of conditional states, then E=I+2C+1 and Z=C, giving T(I+2C+3) witnesses and T(I+3C+5)+1 residual slots.

Take the sum of the squares of all residuals. Over integers it vanishes if and only if every residual vanishes. Every residual has degree at most two, so the sum has degree at most four. For every selector, its own squared binary residual contributes w_(t,e)^4 with coefficient one. Other residuals are at most linear in that selector and cannot supply another pure fourth power. Because E>=1 and T>=1, at least one such monomial is present, proving degree exactly four.

**Ledger precision:** the exact count is a count of the displayed construction's residual slots, not an assertion of independence, minimality, or distinct nonzero polynomials. For example, in the one-state halted program with state code zero, every control residual is identically zero, but the template still has its stated slots. The independent schema tests include this degenerate case.

## 5. First-halt and zero-horizon edge cases

For T>=1, add the one residual sum_(t<T) s_(t,h)=0. The already-proved binary selector conditions make every summand nonnegative. Thus the sum vanishes exactly when no virtual halt loop was used. Together with the final-halt equation, this means the first arrival at H occurs at transition T, counting T transitions after the initial section.

This adds one residual and no witness, giving T(E+Z+4)+2 residual slots. Its square has degree two and does not change the quartic degree. The unique-witness proof remains unchanged. If the initial state is H, the by-horizon solution is the all-loop tuple and its added residual equals T, so its exact-halt polynomial is T² rather than zero.

For T=0, use the constant (q_0-H)² with no witnesses. Its sole possible witness tuple is empty and is admitted exactly if q_0=H. The positive-T quartic and residual formulas must not be applied. The zero polynomial in the already-halted case does not have degree four; the source correctly calls this a separate constant case. Source anchors: §§6–7, lines 167–198.

## 6. What the checks established

The fresh checker exited successfully. `execution.log` gives the terminal result, and `independent_results.json` contains all cases and exact values.

- **54 schema instances:** nine different fixed graphs at T=1,...,6, covering halt-only, zero-coded halt, both increments, both zero/decrement tests with coincident branch targets, a counter-transfer graph, a nonhalting increment loop, and a mixed seven-edge graph
- **201 exhaustive finite-polynomial instances:** 33,640 complete candidate edge words, with all integer counter witnesses determined by exact affine elimination; every satisfying positive assignment counted, including inactive selectors through their forced values
- **22 declared/adversarial fixtures:** both guard directions on both counters, increments, zero and out-of-range selectors, no selected edge, multiple selected edges, wrong counters, broken links, wrong final control, initial halt, and real halt followed by virtual padding
- **One excluded-hypothesis counterexample:** duplicate enabled increments produce two witnesses, verifying the necessity of the stated restriction
- **T=0 checks:** zero and nonzero constant cases, with zero witnesses
- **Saved evidence cross-check:** independently reproduced the frozen four-edge graph's ledgers and 40, 81, 122, 163 expanded monomial counts at T=1,...,4

The exhaustive procedure first uses the already-audited binary/one-hot equations to reduce the selector possibilities to the finite set of all E^T complete words. For every candidate, it simultaneously substitutes

    A_k = A + sum_(j<k) d_(e_j),
    B_k = B + sum_(j<k) f_(e_j)

into the remaining equations, rejects nonpositive counters, and evaluates control and guard residuals. These substitutions uniquely solve the linear update equations, so no counter bound or unsearched positive counter range is hidden in the finite-instance counts. The procedure does not compute an enabled next instruction and does not run a physical schedule. General correctness and uniqueness remain mathematical arguments; finite tests alone are not their proof.

Selected exact adversarial results:

| Fixture | By-horizon P | First-halt P | Domain |
|---|---:|---:|---|
| Correct three-step first halt | 0 | 0 | Positive |
| Same halt padded to four steps | 0 | 1 | Positive |
| Initially halted, T=3 | 0 | 9 | Positive |
| Wrong zero branch on a positive counter | 1 | 1 | Positive |
| Fake positive output for decrement of zero | 1 | 1 | Positive |
| Decrement of zero with next shifted counter 0 | 0 | 0 | **Outside positive domain** |
| Two edges selected in the declared trace | 6 | 6 | Positive |
| Selected-edge witness changed to 3 | 7 | 7 | Positive |

The zero-domain example is not a counterexample to the theorem. It explains why a report must retain the words “positive-integer witnesses.”

## 7. Physical transport and the unbounded boundary

The native inputs are A=a+1 and B=b+1. At a fixed positive rational scale D, the physical initialization is separately

    x=D(1/20+(1/10)2^(-(A-1))),
    y=D(19/20-(1/10)2^(-(B-1))).

These are rational coordinates on the encoded family, not additional polynomial terms or arbitrary physical coordinates. The certificate arity and degree ledger do not include a Diophantine encoding of exponentiation or of arbitrary rational coordinates.

Provided the frozen Report 64 simulation theorem is established, native first halt after k transitions corresponds to first arrival at its designated physical halt section after those k simulated instructions. For k>0 its elapsed time satisfies kD<tau<10kD and there are at most 32k binary collisions **through that section**. The optional escape convention has three additional crossings after the designated section; those crossings are not part of the arithmetic padding or the 32k prefix bound. If k=0, the section is already halting. Physical first arrival at a halt section is distinct from cessation of all motion or a fixed collision horizon.

The halt self-loop used for arithmetic padding is virtual. The physical messenger may instead leave to the right, so the actual physical run is only required to realize the prefix up to the first halt. Nothing in the arithmetic proof requires post-halt physical loop execution. The retained physical proof states these interfaces and bounds in §§1, 7–8; this audit checks the logical composition and source match, not the collision geometry.

Finally, T indexes a family whose witness arity grows with T. It is not an additional free input to one fixed-arity polynomial. Halting is equivalent to the existence of a witness for some family member, but that family-level union supplies no fixed-arity packing construction. Indeed, when first halt occurs at k, the by-horizon family supplies a witness for every T>=max(1,k). Uniqueness at each fixed T therefore must not be advertised as a finite-fold or single-fold representation of unbounded halting. The exact-halt variant removes extra successful horizons, but still does not encode arbitrary-length traces with finitely many witnesses. No MRDP, Pell, exponentiation, packing, or universal-polynomial module is established here.

## 8. Primary-source scope

The cited instruction-set reference was independently opened: Andrej Dudenhefner, *Certified Decision Procedures for Two-Counter Machines*, FSCD 2022, Definition 2 on p.16:3 and Theorem 6 on p.16:4. Definition 2 increments to the next instruction and branches on a successful decrement; its zero branch goes to the next instruction. The packet's specified-target instruction set includes those operations. Theorem 6 concerns undecidability for that instruction model; it is neither needed to prove this finite-trace certificate nor evidence for a finite-fold unbounded Diophantine claim. The paper also warns that changing the instruction set can change universality properties.

Primary source: https://doi.org/10.4230/LIPIcs.FSCD.2022.16

Direct PDF: https://drops.dagstuhl.de/storage/00lipics/lipics-vol228-fscd2022/LIPIcs.FSCD.2022.16/LIPIcs.FSCD.2022.16.pdf

## 9. Integration-ready conclusion

The fixed-program, fixed-horizon arithmetic certificate is correct as written, with unique full positive witnesses, the stated template ledger, exact quartic degree, the one-residual exact-first-halt refinement, and the separate zero-horizon convention. It can be included in Report 64 once physical transport is presented with its independently audited premise. Retain the growing-arity and native-input qualifications explicitly. No source correction, physical simulation, or unbounded Diophantine claim is needed or warranted.

## 10. Portable, read-only replay contract

The checker requires `--source` and `--output-dir`, both absolute. The output directory must not yet exist. It rejects output overlap with the source or checker tree, output paths with symlink components, and existing output paths. Repeatable `--protected-root` arguments add complete release trees to the overlap protection. In an extracted release, pass `--protected-root "$PWD"` from that release's root and select an external output location.

After inspecting the archived independent checker, a suitable invocation from the extracted release root is:

    CHECKER=/absolute/path/to/archived/independent_certificate_audit.py
    RUN_PARENT="$(mktemp -d)"
    python "$CHECKER" --source "$PWD/science/arithmetic" \
        --output-dir "$RUN_PARENT/results" --protected-root "$PWD"

The source argument names the relocated arithmetic packet containing the pinned `MANIFEST.json`, not an old absolute workspace location. The checker hashes and reads the packet as data and writes only `independent_results.json` into its fresh external output. The successful execution retained here used this interface. Six negative interface tests passed: source overlap, checker overlap, broader protected-root overlap, relative output, already-existing output, and a symlink alias. Their exact outcomes are in `replay_interface_checks.json`.
