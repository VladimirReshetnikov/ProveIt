# Strategic review: remaining proof compression after phase nine

Review pin: `2ca3a5c16f0876d2cab842056353c03a1ed2f5f0`.
Paths below are relative to ProveIt. This note concerns proof organization for
the accepted K215 table, not a new machine.

## 1. What the accepted endpoint establishes

`Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/README.md`
states the distinction precisely: the existing Lean and Rocq results are
external proof-assistant theorems equating literal blank-tape halting with
finite ZFC refutability. The record does not supply a proof encoded in ZFC's
own formal syntax or the internal PA endpoint for K215. Ordinary mathematical
formalizability in ZFC and a checked internal derivation are different status
claims. Neither consistency nor unconditional nonhalting is a hypothesis or
conclusion of the equivalence itself.

`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` already has a
small final composition: the dense-table bridge, terminal condition, box
contract, site coverage, blank bootstrap, bootstrap relation and source
calibration feed the generic endpoint theorem. Shortening this final wrapper
cannot materially reduce the lower proof closure.

The new work should retain the exact public statement and separate four kinds
of evidence: newly compiled components; inherited compiled endpoint receipts;
new finite computations; proposed integrations. A successful local theorem
does not by itself refresh the entire endpoint's receipt. Source-only equality
and unchanged compiler object bytes are not sufficient cache-invalidation
criteria when executable dependencies change, as phase nine's rejected first
combined run already documents.

## 2. Current adopted work and remaining gap

The current `DominatedImplication.lean` core already uses 58 condensed-detachment
steps for three public goals without a truth constant. Earlier proposals for
positive stuttering, terminal drain, normalized source correspondence,
semantic seed normalization, sparse seed theories, guarded arithmetic CFGs
and sharing Rocq calculus modules should receive their existing attribution.
They are not new discoveries of this review.

`k225-formal/verification/k215/simplification/phase9/README.md` records a checked
shared Home return and a checked source-to-primitive-entry decoder prefix.
The decoder prefix can take zero physical steps; its endpoint is before the
primitive action. The record explicitly leaves primitive/continuation
factoring open. That is the principal unfinished seam to target.

For a normal source edge at site Q, a useful contract is:

1. For every admissible register file R and tape frame F, decoding the literal
   source path reaches the exact primitive entry representing (R,F).
2. The primitive takes at least one concrete step and changes precisely its
   specified register (or no register for a control operation), retaining a
   frame that the return contract accepts.
3. The continuation reaches the existing dispatcher relation for the exact
   successor path. Overflow, gap growth, spare blocks, tape orientation and
   all exterior cells are part of this relation.

If their respective lengths are d, p and r, then concatenation is a concrete
run of length d+p+r. From d,r >= 0 and p >= 1 follows d+p+r >= 1. Thus the
existing positive-progress simulation premise is recovered even when the
prefix length is zero. This is an ordinary compositional proof, not a new
positive-stuttering theorem. The halt edge uses a separate terminal contract.

The primitive theorem should be proved once per semantic operation/branch
family, with an exact checked table-entry premise. Site-specific information
should select a theorem instance; it should not replay the whole primitive.
The first integration can keep old checked Boolean sites as compatibility
instances and replace one operation family at a time. It is essential that
the contract accounts for the entire tape, not only the head state and a
bounded window. A minimum positive macro length cannot be inferred from
source-path length alone.

## 3. A measured alternative: source reachability pruning

I independently reconstructed the source control graph from the current
`candidate-k215/sites215.json`, SHA-256
`17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba`.
The reconstructed primitive graph has 3,326 vertices and is bytewise equal
after canonical JSON parsing to the previous packet's primitive graph. The
source retains all 4,751 leaf sites, including break/continue leaves. The
runtime's present all-register coverage has 6,176 site outcomes.

### The initialization really is the K215 initialization

`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/SeedPerm.lean` defines
`L2Perm.bootRegs := upd (fun _ => 0) 0 4`. It also proves `enc_seed`, matching
the source program registers to the command enumerator's clean seed.
The corresponding Rocq file is
`k225-formal/rocq/rocq-extension/coq/215/Regs215.v`, where `R0p` updates zero
registers at logical register 0 with 4.

`KSim.lean` defines physical register order `[2,8,1,4,3,7,0,5,6]`, so the same
logical initialization is `[0,0,0,0,0,0,4,0,0]` on tape.
`KBoot215.lean` uses exactly that list followed by 40 spare blocks.
`KEndpoint215.boot_rel` connects this tape to `L2Perm.bootRegs` and the empty
source path. Older 217/219 boot examples with `param1=3` are inapplicable here.

### Finite abstract domain and soundness obligation

For a cutoff c>=1, partition natural numbers into exact values 0,...,c-1 and
the tail [c,infinity). An abstract register value is a set of these classes;
the state domain is the product over the nine registers, plus unreachable.
Initialize logical register 0 with either every value, every positive value,
or the abstract class containing the concrete value 4; initialize every other
register with 0. (For c<=4 this deliberately overapproximates the singleton
{4}; for c>4 it represents {4} exactly.) Propagate through all
source edges to the least fixed point, joining each register separately.

Increment maps class i to min(i+1,c). Zero decrement admits only class 0 and
leaves it unchanged. Positive decrement maps each exact class i>0 to i-1;
the tail maps to the union of class c-1 and the tail. Other registers and
control instructions remain unchanged. These abstract transformers contain
every concrete successor: inspect the finite exact classes, then the tail
inequalities. If initial inclusion and post-fixpoint closure are certified,
induction on finite source runs gives the invariant at every reached site.
An outcome whose guard has empty intersection with the tested abstract
register is therefore impossible on such runs.

This soundness argument is ordinary mathematics. The experiment additionally
checks every post-fixpoint edge after the worklist terminates. The generic
transformer-soundness theorem, source-leaf/CFG semantic connection and
invariant-indexed runtime simulation have not been compiled in Lean or Rocq.

### Results

All three choices for the initial counter give the same counts at each
cutoff:

| Numeric partition | Counter modes checked | Abstractly reachable sites | Remaining runtime outcomes | Removed outcomes |
|---|---:|---:|---:|---:|
| 0 / positive (c=1) | 3 | 4,749 | 6,173 | 3 |
| 0 / 1 / >=2 (c=2) | 3 | 4,748 | 6,171 | 5 |
| c=4 | 3 | 4,748 | 6,171 | 5 |
| c=8 | 3 | 4,748 | 6,171 | 5 |
| c=16 | 3 | 4,748 | 6,171 | 5 |

Zero-based leaf indices removed at c>=2 are:

| Leaf | Path | Instruction |
|---:|---|---|
| 4672 | `110100101110010` | increment register 6 |
| 4673 | `110100101110011` | continue 2 |
| 4734 | `1111001101` | continue 2 |

The two impossible guarded outcomes are the positive branch of decrement
register 1 at leaf 4671 (`11010010111000`) and the positive branch of decrement
register 6 at leaf 4733 (`1111001100`). Their invariant values for the tested
register are exactly zero. The first branch and its two dead descendants
already appear in prior state-search discussion; this experiment does not
claim their discovery. It supplies a new quantified comparison of this
simple abstraction family as a proof-compression strategy.

Five outcomes are only 0.081% of 6,176. Increasing the cutoff beyond 2 brings
no gain in these runs. Proving the new invariant-indexed simulation interface
solely for this pruning is unlikely to repay its added proof complexity.
Sharing the repeated primitive execution remains the better first target.
This is not a lower bound on relational, disjunctive or arithmetic invariants,
and it is not a measured compiler speedup.

## 4. Reproduction and delivered scope

`reachability_census.py` needs Python 3.10+ and the source leaf JSON. The
optional `--compare-cfg` argument checks the old primitive-graph agreement.
The JSON output includes every c=2 exact-counter4 abstract state so the
claimed inductive certificate is reviewable. The script makes no writes to
the repository and does not change any machine action. Its finite computation
does not turn an omitted branch into an accepted formal runtime contract.

Example, from a ProveIt checkout:

```sh
python3 /path/to/reachability_census.py \
  --sites Computability/BusyBeaver/Research/ZFC/candidate-k215/sites215.json \
  --output /tmp/reachability_result.json
```

Source references for the main roadmap are `KSim.checkEdge`,
`KSim.runTo_sound`, `KSim.Rel`, `KSim.halts_iff`, `KDecoderPrefix215`,
`KHome`, `KHomeReady` and the phase-nine checkpoint record. They should be
read at the pinned commit when evaluating proposed integrations.
