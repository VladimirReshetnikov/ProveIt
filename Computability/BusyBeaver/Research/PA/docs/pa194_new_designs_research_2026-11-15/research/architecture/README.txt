ARCHITECTURAL REDUCTION RESEARCH
===============================

This component records bounded unsuccessful attempts to go below 194 states,
and preserves two small, exact negative examples. It does not claim an
optimality theorem. The successful source-level MP reassociation is the
separate mp_construction component.

EVIDENCE STATUS

previous_run_record.json is explicitly a pre-reset session record. Four
bounded grammar searches considered 10,022,440 proposals in total. Their raw
logs and intermediate grammars were lost when the volatile workspace reset;
the recorded counts were not freshly rerun. A stochastic search without a
successful candidate proves no impossibility result. Its objective values
must not be read as state counts of verified Turing machines.

The two counterexamples below HAVE been reconstructed and freshly replayed.
Their compact programs and full finite-support witnesses are provided.

1. REJECTED ROOT ROTATION

The source transformation
  ((node7,node20),(node170,node23))
    -> (node7,((node20,node170),node23))
preserves all 3,671 resolved instructions. The four proposed physical target
edits were 84/0->68, 310/0->53, 53/0->69, 53/1->214. This moves the shared
ReadW entry from address prefix 01 to 100, changing ancestor context used by
later selectors. Source control-flow identity is therefore insufficient.

At source site 11 / path 100000 (decrement logical register 2, zero case), start
in native control 84 / head 0 with every logical register zero except logical
register 8, L=1, a single unit spare, and extra gap 0. The correct continuation
is source site 19 / path 100010 with the same registers. Literal simulation of
the proposed raw201 table instead enters terminal control 254 after 17,392
transitions. With extra gap 1 it halts after 17,648. L=0 controls reach the exact
expected frame in 468 and 476 transitions. Complete initial, expected and final
one-cell sets are in root_rotation_counterexample.json; all other cells are
zero. These are exact full-tape witnesses, not bounded failure-to-halt tests.

Replay from the final archive's top directory:
  python3 -B research/architecture/check_root_rotation.py --mp mp_construction \
      --output /tmp/root_rotation_replay.json

The program uses the sibling source resolver only to establish instruction
identity and the expected continuation. All actual TM steps use its own
literal set-of-one-cells simulator, without the symbolic runtime or arithmetic
macro oracles. The witness refutes this all-register primitive contract; it
does not rule out other source encodings or infer a blank-input consistency
failure.

2. DUAL-B LOGICAL OBSTRUCTION

Writing I for implication, U for universal quantification,
N(A)=I(A,1), and Ex(d,A)=N(U(d,N(A))), the old scheme is
  I(Ex(d,U(d,H)),H).
The proposed equally short replacement is
  I(H,U(d,Ex(d,H))).
Its tempting reverse derivation uses explosion/double negation elimination.
But code 1 is M(0,0), not an independently given bottom constant; that inference
cannot silently import a property whose upstream derivation used the old
scheme.

There is a Boolean interpretation with material implication, code 0=true,
M(a,b)=true exactly when a=b=0, all E(a,b)=false, and every U(d,A)=true. Then
code 1 and every N(A) are true. The restricted rho scheme, h2--h6, diagonal,
gate and proposed dual-B scheme are true, and modus ponens and generalization
preserve truth. The old B instance at H=M(1,1), code 17, is false; so is 1->H.
The finite truth-case checks are in dual_b_countermodel.json.

Replay:
  python3 -B research/architecture/check_dual_b.py --output /tmp/dual_b_replay.json

This obstructs an identity/theorem-preserving translation. It does NOT prove
inequiconsistency with PA and does not exclude a different refutation compiler.

3. K, S AND PEIRCE

Keeping old B and replacing the dominated implicational rho scheme by K, S
and Peirce is logically plausible in both directions. The upstream
RestrictedImplication.lean gives fixed derivations of K, S and Peirce from
restricted rho. Conversely, given f:(H->u)->D and g:D->H, assume h:H->u,
apply f and g to derive H, discharge h with K/S, and apply Peirce to infer H;
discharge the unused A and then g,f. This needs no bottom/explosion assumption.

The investigated source construction changes the rho portion from 12 to 24
tokens, total word length 190 to 202 and stack use 11 to 13. It admits 576 seed
variants (96 old flavors times 6 parameter permutations). The recorded search
best price 70 plus the optimistically unchanged 134-control remainder is 204;
the larger selector and full physical compiler were not certified. This is
research evidence, not a completed 204-state machine or a lower bound.

4. SHORTER SCANNER

The old seven-zero detector follows native 2,3,5,9,15,23,34,75. Deleting 34
and directing 23/0 to 75 suggests one physical state saving if all reachable
addresses and bootstrap satisfy the stronger marker condition. AX11H has 26
six-zero source addresses; three lie outside AX, including source 0=000000,
source 25=1000000 and source 3572=10010101000000. Root and MP reassociation
remove those three source-address obstacles, but the proposed root physical
implementation is refuted above. The constrained AX grammar searches also
failed to produce a maximum-five-zero grammar with the required reader price.

A six-zero substring test on addresses alone does not establish the complete
scanner invariant: the instruction selector changes adjacent marker bits,
and startup must be proved separately. In the recorded baseline startup,
native 34 had 463 read-zero visits and 6 read-one visits. The source CFG also
reaches site 0 from seed 25; final instruction 3670 is jump 0. Thus naive deletion
has neither a generic unreachable-source argument nor an automatic bootstrap
argument. A value-sensitive invariant or a more careful selector redesign
could still make progress.

5. RELATED SOURCE IDEAS EXAMINED

The following are notes from pinned commit 793c68737d94bffa4e32a75bce6cc8058d6d22f0,
read before the reset; they are not newly extracted source excerpts here.

* Computability/BusyBeaver/Research/ZFC/candidate-k220/README.md and
  candidate-k215/proof.md separate abstract source rotations from history-bit
  selector repair, universal local tape contracts and blank startup. Their
  repairs around non-pure decoder 132 and marker-sensitive 69/213,164/201 are
  directly relevant: counting grammar nodes alone misses physical context.
* Computability/DiophantineConsistency/IPRA_AXIOMATIZATION.md uses native
  intuitionistic primitive-recursive symbols with intensional codes and
  quantifier-free induction. Predicate translations need explicit proof maps.
  Its low-variable/high-degree polynomial metrics do not count binary-TM
  states; arithmetic evaluation, enumeration, constants and bootstrap still
  need a priced compiler, and its ZFC target needs a PA-specific replacement.
* Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Native.lean
  and NativeBiInterpretation.lean provide a very small syntax and a native
  inconsistency correspondence with iPRA. Unmodified, that checker targets
  Con(iPRA), not Con(PA). A PA/HA-level strengthening and explicit translations
  would need a complete counted binary checker before yielding a PA bound.

No failed search here weakens the positive mathematical relative proof for
PA194AX11HMP. Conversely, none supplies a verified 193-state result.
