# Mathematical audit of Elliot Glazer's K230 endpoint

Audited checkout: `elliotglazer/k230-rocq`, commit `3142e4dd980f0be12f4abb636c4ae2528afc17eb`.

## Finding

The inspected proof source contains the complete chain from the frozen binary table to ordinary first-order ZFC refutability. The endpoint is not conditional on a model interpretation, an unproved source equivalence, or a conjectural equiconsistency statement. Both directions of the compact-theory comparison are supplied as finite syntactic derivation transformations. The initial nonzero enumeration seed is handled explicitly.

This audit read the theorem statements and the proof-composition files, checked the definitions used in the conclusion, inspected the principal set-theory bridges and numerical decoding cases, and traced the treatment of initialization. It did not run a fresh Rocq build. The author's successful clean-build and assumption-audit reports are repository evidence and should be attributed as such unless independently rerun.

The precise final statement in `coq/tm/Correct230.v` is

`halts tm c0 <-> StandardZFC ⊢TC ⊥`.

Its nonhalting corollary is the negation of both sides of this equivalence. There is no premise asserting consistency of ZFC. `StandardZFC` is defined in `coq/settheory/KQuotZFC.v` by

`StandardZFC(phi) := (ZFc(phi) or phi=ax_reg') or phi=ax_ac`.

Here the pinned reference theory `ZFc` already includes the extensional ZF axiom schemata and infinity; `ax_reg'` is Foundation and `ax_ac` is Choice. The relation `⊢TC` says there is a finite list of theory axioms and a classical first-order derivation of the conclusion. Thus the endpoint is about ordinary finite syntactic refutations, not a claim that ZFC has a model or is actually consistent.

## What theory K says

For a formula phi(y,p,q), where q denotes all its other parameters, define

- `p ⊆ u := forall z, z∈p -> z∈u`;
- `W_phi(p,C) := (exists y, phi(y,p,q)) -> exists y, (y∈C and phi(y,p,q))`;
- `H_phi(C) := forall u, u∈C -> ((exists p, phi(u,p,q)) and forall p, p⊆u -> W_phi(p,C))`.

The schema requires, for every a,x,

`exists C, ((phi(x,a,q) -> x∈C) and H_phi(C))`.

The support-and-witness condition H is required even if the designated seed premise is false. It cannot be weakened to an implication whose whole consequent is disabled by a false seed. This detail appears literally in `output_root`, `kprime_core`, and the emitted `kcore` formula.

The ordinary theory `KPrimeOrd` has the closed instances of this schema and the ordinary equality axioms. `KPrimeOrdIR` adds irreflexivity `forall x, not(x∈x)`, which supports the native use of a membership atom as falsity. The proof establishes that both ordinary theories are equiconsistent with StandardZFC.

K retains a full schema over arbitrary finite formulas and arbitrary finite parameter tuples. It is not an assertion about all semantic relations, nor a finite first-order axiomatization of ZFC. The axiom recognizer nevertheless stays short because a numerical matrix code is reused verbatim at each occurrence, with its own value serving as a guaranteed-fresh private variable label.

## The two mathematical reductions

### From a ZFC refutation to a K refutation

`KPrimeOrd_standardZFC_inconsistent` in `KQuotZFC.v` first applies the pinned reference theorem `ac_reg_relcon`, eliminating the consistency-strength effects of Choice and Foundation from the reference proof system, and then applies `KPrimeOrd_ZFc_inconsistent`.

The latter theorem is in `KQuotZFTransfer.v`. It is a syntactic interpretation of every source axiom and every inference rule. The interpretation uses a tagged domain and bisimulation equality. The tagged domain has a witnessed object, so the transfer does not exploit an empty-domain model. `qaxiom(phi)` is a universally closed translation guarded by a raw-empty marker; at the final contradiction the marker is supplied by a separately derived empty object.

The lower development reconstructs the translated equality axioms, Extensionality, Empty Set, Pairing, Union, Power Set, Separation, Replacement, and Infinity. The Power Set construction bounds canonical representatives and accounts for equivalent representatives through the quotient relation; it does not silently assume a power set of all raw codes. `K0_qomega` derives the reference omega axiom from the locally supplied Infinity statement and the reference transfer theorem. `K0_qtranslate_closed` handles the actual finite derivation, while `collect_theory_proofs` collects only finitely many proof witnesses by induction on a list.

The auxiliary K0 schema is itself derivable from the emitted output-root K schema. `kprime_core_to_seed` and `seeded_core_to_kp0` establish this at the formula level; `K0_derivation_to_KPrimeOrd` lifts it to finite derivations.

### From a K refutation to a ZFC refutation

`KPrimeOrdIR_standardZFC_inconsistent` in `KUpperConsistency.v` does not assume a semantic model of ZFC. It translates the finite K proof into a finite proof inside the reference constructible-hierarchy interpretation.

For each K schema instance, `upper_core_insts(n,phi)` is an explicit finite list of reference axioms. `upper_core_insts_ok` proves every listed formula belongs to the allowed reference theory. `L_kprime_core` derives the relativized K instance from those finitely many axioms. `KPrimeOrd_holdsL` packages the instance proof; `KPrimeOrdIR_holdsL` handles the added irreflexivity using the reference Foundation axiom.

The reflected level is chosen to support both subset closure and matrix witnesses. A single combined reflected formula supplies the two requirements; Separation then selects supported outputs. The proof keeps track of finite parameter bounds through `fb`, so it treats arbitrary finite formulas rather than a bounded list of tested examples.

The final upper proof collects the finite axiom lists needed by the finitely many K axioms used in the refutation, constructs an explicit finite context `G0`, proves every member belongs to StandardZFC, invokes the reference `L_ex` theorem to witness the interpreted domain, and transfers the finite deduction of bottom. This gives an actual contradiction translation in the required direction.

Consequently `KPrimeOrdIR_standardZFC_equiconsistent` proves both directions, and `KPrimeOrd_standardZFC_equiconsistent` removes the added IR axiom for the plain ordinary presentation.

## Complete endpoint chain

| Layer | File and declaration | Exact role |
|---|---|---|
| Literal table and blank run | `coq/tm/Boot230.v`, `boot` | Computes 408,419 literal transitions and proves arrival at the exact initial interpreter frame. |
| Binary simulation | `coq/tm/Sim230Main.v`, `tm230_rm` | `halts tm c0 <-> rm_halts p230 ([],R0)`. |
| Source/certificate bridge | `coq/prog/ProgramBisim230.v`, imported by `Main230.v` | Validates the frozen finite program relation and connects the released source tree with the verified structured program. |
| Enumerator implementation | `coq/prog/Main230.v`, `prog230` | `rm_halts p230 ([],R0) <-> halts_from seed230`. |
| Actual initial seed | `coq/logic/Seed230.v`, `seed230_iff_thm` | `halts_from seed230 <-> thm230 1`, with `seed230=mkState 0 3 0 0 3 0`. |
| Numerical/ordinary logic | `coq/logic/Bridge230.v`, `thm230_iff_KPrimeOrdIR` | Exact numerical refutability agrees with ordinary K plus IR refutability. |
| Set theory | `coq/settheory/KUpperConsistency.v`, `KPrimeOrdIR_standardZFC_equiconsistent` | Both finite-refutation transformations between K plus IR and StandardZFC. |
| Final composition | `coq/tm/Correct230.v` | The halting equivalence and its nonhalting corollary. |

The numerical bridge explicitly covers disabled gates, equal input/output labels, fresh matrix labels, and exceptional low codes. `KPrimeOrd_proves_decoded` splits the cases `c=a`, `c=b`, `a=b`, and all-distinct roles, rather than invoking freshness in a case where it fails. In the same-role case, independently derived empty objects and singleton hosting discharge the degenerate formula. This matters because the literal machine enumerates all natural codes.

## Bootstrap and verification scope

The frozen machine has working states 0 through 229, separate halt 230, initial state 0, and an all-zero tape. Its table hash is `e7ccbcec074534cfd955f0ab94d16f13594e81974074309dc2ce663b9dfd7ba8`.

Its bootstrap is 408,419 transitions, not the 409,835 transitions of the supplied 235-state package. The terminal bootstrap state is 84; the right tape has 181 zero cells followed by the delimiter and 176 register blocks. The first nine physical register values are `[0,0,0,3,0,0,3,0,0]`; the remaining 167 spare values are all 1. The matching enumerator seed has next candidate 3 and parameter counter 3. `seed230_complete` proves that enumerating from this seed still reaches a compiled refutation word. It does not presume an all-zero cache/register initialization different from the released table.

The runtime checker is proved sound before it is used to verify the finite sites. Its site theorems quantify over arbitrary nonnegative extra gaps, arbitrary register values, and sufficiently long finite register-block lists. Four runtime box hypotheses in the local checker section are parameters subsequently discharged by the literal-table block lemmas. Their appearance as section hypotheses is not an unresolved assumption of the final theorem.

The repository records two successful clean builds of 216 proof files and two final declarations reported `Closed under the global context`. `AuditCorrect.v` contains the two `Print Assumptions` commands. The build driver checks exact input hashes and table rows before compiling. Its optional `coqchk` invocation checks the final module and dependency closure without `-admit` or `-norec`. This audit has not independently reproduced those builds.

## Ordinary ZFC provability and internal PA claims

The inspected argument is an ordinary proof of an arithmetic equivalence: halting of one finite machine agrees with existence of a finite ZFC derivation of contradiction. Its proof ingredients are finite syntax, primitive recursive machine execution, induction on natural numbers and finite proof trees, and explicit first-order derivation transformations. These are the ingredients needed to express and formalize the argument in ordinary ZFC. No assumption `Con(ZFC)` is needed for the biconditional.

The repository's formal endpoint is an external Rocq theorem. It does not export a separately encoded derivation in PA of this equivalence, and its README explicitly distinguishes that project. One should not relabel the existing Rocq declaration as a completed internal PA endpoint. Likewise, a new table produced by further optimization does not inherit the theorem merely by having fewer states: it needs an exact semantic reduction to the frozen table or a new verified source/table simulation.

## Transfer of the older machine optimizations

Source reassociation and entry-bit state sharing are general techniques, but their concrete certificates depend on exact source trees, decoder states, and tape invariants. The difference `243-235=8` cannot simply be subtracted from K230. K has a different emitted theory block, different source sharing, a different table, and a different bootstrap.

There is one exact source transfer immediately visible in the K230 source: four occurrences of `((CD6,(CI5,CC2)),CI5)` can become `(CI5,(CD6,CC2))`. Both fragments implement `(R6,R5)=(n,m) -> (0,m+n+1)` for every n,m and preserve all other registers. The separate `k230_posttest/proof.md` proves that identity uniformly, and `build_k230_posttest.py` builds the exact changed source. Its census goes from 5,125 to 5,121 primitive occurrences, while the DAG node count stays 212. Any resulting binary state saving must be checked against the proposed literal table.

## Pinned primary references

- https://github.com/elliotglazer/k230-rocq/tree/3142e4dd980f0be12f4abb636c4ae2528afc17eb
- https://github.com/elliotglazer/k230-rocq/blob/3142e4dd980f0be12f4abb636c4ae2528afc17eb/coq/tm/Correct230.v
- https://github.com/elliotglazer/k230-rocq/blob/3142e4dd980f0be12f4abb636c4ae2528afc17eb/coq/settheory/KUpperConsistency.v
- https://github.com/elliotglazer/k230-rocq/blob/3142e4dd980f0be12f4abb636c4ae2528afc17eb/coq/settheory/KQuotZFC.v
- https://github.com/elliotglazer/k230-rocq/blob/3142e4dd980f0be12f4abb636c4ae2528afc17eb/coq/logic/Seed230.v
- https://github.com/elliotglazer/k230-rocq/blob/3142e4dd980f0be12f4abb636c4ae2528afc17eb/docs/proof-overview.md

These references were inspected from the downloaded pinned checkout. Browser retrieval of the individual GitHub pages was unavailable in this audit; no browser citation identifiers are used as if they contained retrieved source text.
