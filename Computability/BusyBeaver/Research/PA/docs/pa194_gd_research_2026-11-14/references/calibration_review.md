# Independent reading of the updated AX11H written calibration

## Scope and identity

Reviewed the ten TeX components copied in the incoming AX11GH packet under
`references/AX11H/`, at the requested ProveIt snapshot
`8d31445d858761a8f6150c2e5012adae8895e932`.  Their source is the updated incoming
`pa194_ax11h_research_2026-11-14.zip` from revision
`1e1a41f799d4658b829cdd0eabae3775a0c8c4a0`, archive SHA-256
`93ee082ef035b2d32e71d6af5239b25b4bea1773f03bea4d2c39810a7fe15075`.
The package records them as inherited mathematical dependencies.  They total
4,608 TeX lines.  This note is an independent mathematical reading, not a
new proof-assistant build or replay of every cited upstream source recipe.

## Assessment

The updated packet does contain a substantial written proof of the requested
iPRA equivalence for its AX11H and QAX11H tables.  It is not merely a conditional
endpoint with the old machine-specific hypotheses renamed.  No concrete
mathematical error was found in the displayed arguments during this reading.
The repository's top-level statement that the formal Lean endpoints remain
open must not be used to dismiss this stronger written result.  The two
statuses are compatible: ordinary written theorem, incomplete end-to-end
kernel formalization.

The following especially delicate points are addressed explicitly and appear
correct.

1. The physical interpreter is given finite-support tape semantics.  Literal,
   unary, and four list-traversal rules have exact endpoint equalities and
   primitive recursive durations.  List-width slot 12 is tied to the same
   spare list as the symbolic tape atoms.  Exterior-zero normalization is
   numerical tape equality, not an equality of untrimmed raw lists.
2. The physical source frame includes the changing gap and spare list.  An
   increment appends a spare entry and a positive decrement grows the gap.
   The finite endpoint check establishes padded-prefix equality with the
   actual successor site; word equality alone is not substituted for CFG
   equality.
3. The cumulative physical clock is zero after canonical source halt.
   The reverse simulation correctly uses the conditional bound
   `z_k != Halt -> tau(k) >= 3k`, and the decidability of the halt code.
   It does not incorrectly invoke unconditional clock cofinality after halt.
4. Exact register-source templates establish the three abstract command
   effects and their clocks.  I checked the displayed unpairing, pairing,
   and destructive-comparison costs against their primitive template cases.
   The AX fallthrough consumes a genuine fourth field, including its
   nonzero case; it is not silently treated as a three-field AX protocol.
5. The cached-only Shift changes the Pop contract: Pop halts exactly when
   the saved top is one.  The proof compiler allows early halt and preserves
   the protected base stack.  Its MP word reserves a zero under both premises.
   All calculations use total Cantor projections, including `[0;0]=0`.
6. The all-store command compiler uses a valid bounded-input induction.
   Its decreasing allowances
   `B(j)=Phi_K^(L(N-1-j))(s0)` ensure that any earlier premise-word call made
   within a current word lies in the earlier induction allowance.  Thus it
   does not perform quantifier-free induction on an unbounded universal
   assertion about all stores.
7. Source soundness carries explicit proof-list annotations.  The reverse
   numerical-to-PA calibration uses Sigma_1 induction in I-Sigma_1 models,
   with witness vectors for prior PA proofs, rather than calling unbounded
   provability quantifier-free.  The cited conservation/negative-translation
   endpoints supply the iPRA negative implication.
8. The forward construction replaces full-PA all-environment induction by
   finite query trees.  Same-family ranks decrease; arity is at most two;
   query and local proof constructors are primitive recursive; cross-family
   calls go to completed lower strata.  A binary demand tree of depth bounded
   by the input rank, followed by reverse evaluation, is primitive recursive
   even when formula codes and proof codes grow rapidly.  The Boolean validity
   invariants described are legitimate quantifier-free invariants.
9. Term coherence is completed before vector realization.  Consequently the
   bound-variable vector case may call uniqueness on a much larger replacement
   term without violating the source-term rank argument.  The substitution
   and environment-padding side conditions are stated, rather than hidden in
   a choice of witnesses.
10. The Foundation adapter distinguishes the current square-pairing proof
    encoding from the machine's Cantor codes.  It supplies explicit opening
    and closing constructors and a bounded induction-axiom witness extractor.
    It treats the changed `addEqOfLt` axiom and the historical/current
    I-Sigma_1 hierarchy comparison separately.  Equality replacement is
    bounded by syntax skeleton size when opening a binder increases raw code.

## Remaining audit limits

The lower closed relational leaves are imported finite `*NativeProof`
recipes with pinned source references.  Their very large numerical codes
are not printed or evaluated by the written proof itself.  This reading did
not reconstruct every one of those recipes or rebuild its transitive Lean
closure.  The result should therefore be attributed to the supplied written
calibration and its cited finite dependencies.  It would be inaccurate to
describe it as independently kernel-verified here, or to imply that checking
the runtime Python certificate alone checks the logical calibration.

For a new table with a separately established iPRA halting equivalence to
AX11H/QAX11H, composition with this written theorem is a legitimate ordinary
mathematical route to the requested result.  The relative reduction and the
absolute inherited calibration should be stated separately for review.

## External-program transfer findings

- The ZFC K215 engine's old `81/0 -> 0 L 111` optimization is already present
  in the primary PA194 native table.  It cannot supply another deletion by
  being counted twice.
- The ZFC protected-tail startup relaxation has already been enlarged in the
  PA sub-194 work.  The known 301/88 runtime quotient has documented failed
  starts; no new blank-start theorem follows merely from the protected-tail
  observation.
- The ZFC parameter-free-MP/residual-counter construction has a complete
  source-level compiler argument, but its own best saved physical pricing is
  larger than K215.  It supplies an idea, not an already shorter binary engine.
- Directly replacing the target calculus by ConciseIPRA would calibrate
  consistency of iPRA, not consistency of PA.  Full PA induction must still be
  represented or recovered.  Its compact Python checker size is not a binary
  blank-start TM state count.
- The DiophantineConsistency results principally concern ZFC and fixed large
  coefficient tuples.  A small algebraic expression is not by itself a short
  binary blank-start machine: coefficient generation, witness enumeration,
  arithmetic evaluation, and the exact PA calibration all need pricing.

## A fresh reachable-source analysis

`abstract_source.py` performs a sound forward abstract interpretation of the
primary PA194's 3,673 source instructions using the per-register classes
zero, one, and at least two.  Starting at site 25 with logical registers
`[2,0,0,0,0,0,0,0,0]`, its least fixed point takes 22,739 worklist transfers.
It finds 3,670 potentially reachable sites.  Sites 8, 3635 and 3636 are
unreachable; decrement sites 7 and 3634 have only the zero branch.  The
remaining predicates are deliberately an overapproximation.

The consequent symbolic decoder coverage (`reachable_coverage.py`) has the
same 379 observed rows before and after discarding those impossible outcomes.
Thus this simple invariant alone frees no decoder row.  The redundant
transfer at source sites 3634--3636 could support a source rewrite, but a new
source layout and physical certificate would still be required.  No state
saving is claimed from this analysis.
