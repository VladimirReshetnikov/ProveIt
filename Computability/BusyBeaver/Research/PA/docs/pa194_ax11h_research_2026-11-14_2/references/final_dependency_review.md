> Release note: this review was written before final integration of the physical/source proof. The completed written theorem is now in `proof/physical_ipra_audit.tex`. The source-to-command and PA-calibration obligations identified here remain open. See `claims.json` for the final status.

# Independent final dependency review

Snapshot: ProveIt `1c9524d8bf2e0a27b9a16ff622359927f536e663`.

Reviewed the new `proof/ax11h_preservation.tex` and
`proof/ipra_simulation_theorem.tex`, the pinned PA README and forward-compiler
audit, and the retained PA195 calibration and IΣ₁-transfer descriptions.

**Update after the physical audit:** the root reports a new written iPRA
soundness argument for the literal symbolic rules, all 4,778 positive
primitive-source durations, and exact CFG endpoints. If that argument
establishes the stated uniform hypotheses, it discharges the physical-to-
primitive-source portion discussed below. It does not automatically
discharge the intervening primitive-source-to-command-scheduler interface.
The precise remaining interface and reusable inherited arithmetic are
reviewed separately in `source_command_interface_review.tex`. The PA
calibration conclusion below is unaffected.

## Conclusion

The available proofs do **not** establish the user's complete statement

    iPRA ⊢ Con(PA) ↔ ¬Halt(M)

for either new literal table. The gap is not merely the absence of a new
Lean or Rocq build. The displayed new proofs deliberately stop before two
uniform weak-arithmetic connections: the literal table/source/scheduler
connection and the PA-refutation/numerical-calculus connection. Neither
can be supplied by relabeling an ordinary PA theorem as an iPRA theorem.

There is no identified mathematical contradiction in the desired result,
and no argument here that completion is impossible. It remains plausible
that suitable explicit proof transformations and finite execution
certificates can be verified in the required base. Those verifications
have to be supplied.

## What the new written arguments establish

### Abstract AX11H and QAX11H schedulers

The new command proof works with explicitly defined total primitive
recursive functions for the four-parameter AX command, no-push MP, and
cached-only Shift. It handles the changed Pop behavior correctly: Pop
halts when the preserved top is one. Consequently the all-store
refutation compiler ends with Pop, not with a plain Shift whose cache
would still be zero.

The bounded-input compiler invariant is a legitimate route to ordinary
mathematical iPRA provability. The proof predicate for a bounded collection
of stores can be represented by a primitive recursive Boolean fold.
The earlier-line input bounds increase sufficiently to cover the actual
intermediate input to every premise word. This avoids induction on an
unbounded universal-store predicate. The soundness annotation is likewise
a Boolean invariant of finite derivation lists and canonical Cantor stacks.

Subject to the chosen primitive recursive coding and the explicitly
specified abstract scheduler equations, these arguments establish

    Halt(R_11H) ↔ ∃ e Prf_C4(e,1),
    Halt(R_Q11H) ↔ ∃ e Prf_C4Q(e,1)

in iPRA. They are written mathematical arguments, not just finite tests.
The objects on their left are abstract schedulers, and the proof predicates
on their right are numerical-calculus proof checkers, not PA's checker.

### Positive simulation theorem

The generic simulation theorem is sound under its explicitly stated
hypotheses A--G. Positivity gives cofinal boundary times. Absorbing halts
then reflect an arbitrary target halt at time t to a source halt by time t,
without decoding an arbitrary interior physical tape. The cumulative
duration and forward witness maps are primitive recursive.

However, the theorem's hypotheses are required to be **iPRA theorems**.
For a particular table one must provide the actual frame predicate,
encoding, segment duration, preservation proof, exact endpoint equation,
halting-flag agreement, and startup equation. Standard-natural symbolic
execution alone is not such an instantiation. In particular, the symbolic
checker must justify its unbounded run/list rules uniformly and provide
primitive recursive duration bounds. A halted-source encoding must also
retain enough information for its exact physical endpoint.

## Exact sufficient assumptions for the full target

Let C denote C4 for AX11H or C4Q for QAX11H. Fix explicit Boolean proof
checkers for C and the intended standard PA presentation. The following
are sufficient when proved in iPRA, uniformly in their arguments:

1. Physical binding:

       Halt(M) ↔ Halt(R).

   The current positive simulation theorem gives a clean sufficient
   interface for this, but its concrete hypotheses must be discharged.

2. Forward logical calibration, for a specified primitive recursive f:

       Prf_PA(p,0=1) → Prf_C(f(p),1).

3. Reverse logical calibration, for a specified primitive recursive g:

       Prf_C(e,1) → Prf_PA(g(e),0=1).

Together with the new abstract scheduler theorem, these prove the
positive existential halting/refutation equivalence. Intuitionistic logic
alone then gives the requested equivalence of nonhalting and consistency.
One need not assume consistency of PA, use Markov's principle, or assert
truth of arbitrary PA formulas in this argument.

Explicit witness maps f and g are a particularly transparent sufficient
form. Other completed weak-base proof-existence arguments could also
discharge the same positive implications. The point is that their
correctness must be proved in the intended base, not simply in PA.

## Q premise exchange is not the central obstacle

The Q emitter only reverses the two curried premises in a quantifier
distribution head. The inherited restricted implicational basis has a
fixed premise-exchange derivation independent of either distribution head.
This is a finite-template transformation. After supplying the literal
template and checking the restricted-rho side conditions using the Cantor
constructor bounds, its uniform validity should admit an elementary iPRA
proof. Proof-list translation then uses Boolean proof-checker induction.

The current preservation document labels its inherited exchange
translations PA-verified. That label alone is not already an iPRA theorem;
the finite-template justification just described would establish the
stronger claim. This appears to be a small completion task, unlike the
PA-to-numerical-calculus compiler.

Even a completed iPRA equivalence between C4 and C4Q would only identify
their refutations. It would not identify either proof checker with PA's.

## Why the available PA calibration does not close the gap

The inherited PA195 calibration explicitly reuses the upstream PA196
PA-refutation compiler and states PA-provable correctness. The repository's
forward audit identifies two real meta-level uses of unrestricted PA
induction: `ordinary_derivation_requested` on an invariant quantifying
over derivations and environments, and `fuel_invariant` on a table-wide
realization condition. These have not been shown to be Σ₁ invariants or
replaced by quantifier-free certificate constructions. The separately
repaired formula-substitution agreement does not remove these other
dependencies.

Primitive recursiveness of a function proves its availability and totality
in PRA; it does not by itself prove an arbitrary correctness property of
that function in PRA. For example, a proof checker is primitive recursive,
while its universal rejection of contradiction proofs is a consistency
statement. Therefore "the maps are primitive recursive" is not an
adequate reason to weaken the metatheory of their correctness proof.

There is also an important distinction about PA induction. Constructing a
PA proof whose object-level induction formula is an arbitrary translated
formula is compatible with an iPRA metaproof of syntactic correctness.
The obstacle is not the occurrence of a PA induction axiom in an output
proof. It is a remaining use of full induction in the metaproof that all
internal inputs have valid output proofs.

## Existing work that can shorten completion

The current repository is stronger than a collection of standard-natural
tests. Its modeled-scheduler fairness result works in arbitrary IΣ₁ models.
The distinct-label gate premise has been discharged, and the modeled
scheduler has a checked consistency-to-nonhalting direction. This is
potentially reusable for the numerical-calculus-to-PA half, after exactly
identifying the new C4 proof checker with the existing TargetProvable
encoding. Such an identification must cover the seed families, guard,
proof rules, contradiction code, and proof-code translation. It should
not be silently inferred from similar notation.

The reverse PA-to-C4 direction remains the main logical obligation.
The current PAeq proof transport is conditional on a uniform supplier of
translated source-axiom proofs; the remaining finite suppliers, arbitrary
induction-schema supplier, and numerical proof compiler must be completed.

## A clean completion route

1. Fix the PA proof presentation and use the repository's existing literal
   machine arithmetization for the two tables. This avoids proving a new
   equivalence between unrelated halting encodings later.
2. Work initially with AX11H and C4. Establish the physical/source/command
   correspondence in IΣ₁ or directly in iPRA, extracting total segment
   durations and exact endpoint equalities from the runtime certificates.
3. Identify C4's finite proof checker with the existing modeled numerical
   calculus and reuse the established reverse soundness work where the
   definitions match exactly.
4. Complete the PA-to-C4 compiler using actual coded realization histories
   or a bounded tabulation of the necessary environments, with a proved
   uniform construction and bound. The new AX11H bounded-input argument
   is a useful pattern; it is not itself a proof of this different compiler.
5. Compose to obtain the literal halting/refutation equivalence in IΣ₁.
   Apply the already established machine-independent IΣ₁-to-iPRA transfer
   together with its supplied PA witness-bound certificate. Alternatively,
   if every component was proved directly in iPRA, compose there.
6. Add the finite Q premise-exchange translation to obtain QAX11H.

This route does not assume an unfinished PA-calibration theorem. It makes
the missing compiler and physical obligations the actual work to be done.

## Appropriate result wording

The supported present result is two graph-distinct 194-state candidates,
with reproduced physical certificates and a written iPRA calibration of
their explicitly defined **abstract command schedulers to their numerical
calculi**. An unconditional iPRA consistency equivalence for the literal
tables remains unestablished. Calling this only "not yet formalized in
Lean" would omit the stronger proof-dependency limitation.
