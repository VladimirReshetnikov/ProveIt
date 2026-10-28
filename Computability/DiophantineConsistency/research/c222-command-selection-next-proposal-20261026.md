# Actual C222 finite selection and rule-contract plan

26 October 2026. Read-only next-checkpoint proposal. No new theorem was
implemented or compiled. Re-read actual Block183, old Leaf/RuleExecution254
as guides, the literal Nat EnumPerm blocks/build, and the generic
DominatedImplication derivation. No historical evaluator theorem is proposed
as an import. All formulas, codes, counters and stacks below range over an
arbitrary internal IΣ1 model; fixed lists/counts are external finite notation.

## First leaf: selection, truth and conditional false termination

Propose only `ArithmeticCommandLeafPerm222` plus Checks, approximately
190–250 main lines and55–70 checks. Import only the frozen BlockPerm222
after its completed root acceptance. Define the literal contract

```
Contract word X := ∀ top S,
  evalValue word (stateValue top S 0 0) = 0 ∨
  evalValue word (stateValue top S 0 0) = someState X S 0 0.
```

The two alternatives distinguish halt0 from successful option-encoded
state+1. Arbitrary top and saved stack are essential, especially for the
later MP major. The contract is Pi1 using the existing total Delta1 eval,
state and someState graphs; proving this definability adds no induction or
proof-validity premise. `Contract discardWord 0` follows from exact discard.

The reusable finite `select_entry` theorem uses

```
selector xs ys = appendValue (nipsWord (xs.length+1))
  (dropWord (nipsWord (ys.length+2)))
```

and proves evaluation from
`stateValue g (pushL (xs ++ x :: (ys ++ [last])) S) 0 h`
equals `someState x S 0 last`, assuming h,g,x and every member of xs/ys
differ from1. `last` may equal1 because it is loaded at the final pop and
never tested afterward. Reassociate pushL with the existing generic lemma;
apply the proved NIP continuation equation, DROP, and another finite NIP
sequence. No internal-model stack is reinterpreted as a finite Lean list.

Define the actual fixed-position word, for external `j : Nat`,

```
leafWord j a b c u = appendValue discardWord
  (appendValue (Jword u)
    (axWord c (a-u) b
      (appendValue (nipsWord j) (dropWord (nipsWord (11-j)))))).
```

For `u≤a`, `axList a 0 b c u=xs++x::ys`,
`xs.length+1=j`, and `ys.length+2=11-j`, derive the stronger exact evaluation
to `someState x S 0 0` for every top/S, then its Contract. The actual AX
non-false entries discharge all selection guards. This generic theorem
covers all nine fixed positions; useful named source leaves are:

| Source result | Word parameters after j |
|---|---|
| rho1 a b | j=1; a,b,0,0 |
| rho2–rho5 a b c | j=2–5; a,b,c,0 |
| rho6 a b | j=6; a,0,b,0 |
| growG a b c | j=7; a,b,c,0 |
| rho8 a b c u, **u≤a** | j=8; a,b,c,u |

The rho6 parameter change is mandatory because physical AX pushes rho6(a,c).
Position7 is growG, never old rho7. Position9 is `wal u 0` in this discarded
state; it does not yet prove generalization of an arbitrary child result.

Define `bundleWord a b c` as the same setup with u=0 followed by ten NIPs.
First prove the unconditional exact output
`someState (gateValue a b c) S 0 0`. The seed contract follows under only
c≠a and c≠b; either collision instead gives the truth0 contract. There is
no a≠b or c>0 guard, and labels0 remain valid internal values.

For false handling, define `terminatorWord=dropWord(nipWord(nipWord 0))`.
Prove its evaluation from `stateValue 1 S 0 0` is halt0, and hence
`Contract word 1 → ∀top S, evalValue (appendValue word terminatorWord)
 (stateValue top S 0 0)=0`. This is conditional termination of an existing
false-target block, **not an unconditional false1 axiom leaf** or a proof
that a false-target block exists. The first NIP sees cache0 and loads1;
the second NIP actually tests1. Truth0 is supplied by discard separately.

## Second leaf, only after selection freezes: GEN and MP

The next separately authorized `ArithmeticCommandRulePerm222` could be
about150–190 main lines plus focused checks. Its exact GEN suffix is
`DROP; J(i); NIP; AX(i,0,0); NIP^9; DROP; NIP; NIP`.
For any H including1, evaluation from `(H,S,0,0)` succeeds at
`(wal i H,S,0,0)`. DROP gives top0/cache0 with H saved; J(i) keeps that
cache0; the first NIP loads H, and AX immediately consumes it without a
further NIP test. AX has old counter i and pushes
`rho6 i i`, `growG i H i`, `rho8 i H i i`, and `wal i H`.
The gate is truth0 by c=a. The eight earlier rows and universal result are
not false1. This proves `Contract p H → Contract (append p genTail) (wal i H)`
without requiring H≠1 or i>0. The J(0) empty case is indispensable.

For MP, retain the actual word
`pa; DROP; pab; NIP; DROP; NIP; MP(B); AX(B,0,0); NIP^10; DROP; NIP; NIP`.
The major contract must be instantiated at top0 and stack `P A S`, rather
than at the original stack. Derive the exact suffix law from
`(wim A B,P A S,0,0)`:
`if A=1 ∨ B=1 then 0 else someState B S 0 0`.
The initial NIP safely loads A from cache0; after DROP the next NIP tests A.
Successful MP sets old d=B. Cleanup AX therefore has fourth/GEN label B,
not0, and gate0; the final cleanup tests B as cache. Either false branch is
an allowed halt in Contract. No A≠1/B≠1 premise may be added to the public
`Contract pa A → Contract pab (wim A B) → Contract (mpBlock B pa pab) B`.

## Remaining represented row10 obligation

The actual checker accepts unrestricted rho8(a,b,c,u). Direct AX selection
provides only u≤a. Nat `EnumPerm.build_c222` uses the representation-
independent `DominatedImplication.rho8_all`, not a hidden physical AX with a
fourth operand. The generic source needs only reflexivity and growth of ≤
inside implication operands, so its finite proof can be reused over
internal V. Its existing Nat adapter must not be invoked as an internal
arithmetic theorem.

An existential internal `∃word, Contract word (rho8 a b c u)` alone is not
yet the required represented uniform row function. The subsequent concrete
checkpoint should reify the finite restricted-rho8/MP witness into a fixed
four-input command circuit, with constructors for pairing, sums, truncated
subtraction, conditional zero-J and represented append. One precise route
interprets the generic derivation over formula-expression syntax and
`T f := ∃fixedCircuit, ∀model inputs, Contract (eval fixedCircuit inputs)
 (eval f inputs)`. Restricted rows use the actual dominated leaf; MP uses
the actual restored-stack block. Keeping the circuit existential **outside**
the model/input quantifiers avoids choosing a different unrepresented word
for each model point. Prove the fixed circuit graph/evaluation before
using it as row10. This work is explicitly outside the proposed first pair.
No new proof-word history, validity induction, scheduler or HA endpoint is
included in either finite selection or rule contract proposal.

## Exact prospective cache boundary

`c222-command-selection-next-cache-plan-20261026.json` authenticates123
custom cached modules, including95 Foundation,408 artifacts,38 external
boundaries. It adds only the frozen Block main to the prior122-module
runtime closure. Current selected source/import/object/boundary hashes
were rechecked. Its provider is the accepted independent root primary
`/tmp/arithmetic-command-blockperm222-root-peer-wnu8dt24/lib/DiophantineConsistency/ArithmeticCommandBlockPerm222.olean`,
SHA `1e6a5be6f8399cb9026e1f2a87b5e55108c7815ad660a24884822b4b94cbeac7`.
Root accepted Block at commit `f2843e0ebb`; its ROOT record is
`d735d815fff669402407f4bd77d23e940cab362528760a4751151c627b4e8a23`.
The prior plan and original byte-identical author provider are retained in
the cache metadata. After the
first pair freezes, Rule adds just its main primary:124/95/409/38, with no
new Foundation dependency. History222/ProofConstructors222 remain outside
both leaves. Historical guides and generic DominatedImplication are pinned
in the plan; no historical execution module is a proposed import. Any
later authorized builds retain private fresh outputs, Lean4.32 caps and the
512 MiB reserve. This proposal performed no Lean execution.
