# Ground-equational proof-generator cost

The measured complete register-control source compiles to **299 working states**
(238 decision states and 61 framework states), before supplying a ZFC-specific
query and its writer. Its isolated seven-equation emitter is 171 states. The
unshared controls are 331 and 203 states respectively. These are actual finite
binary tables, with every decision edge independently reextracted. The
299-state table has 598 transitions, start 0, and terminal 299.

This experiment replaces matching and context parsing with generation of valid
equalities. It retains the published candidate-enumeration, DROP/NIP, and
cache shell, and replaces its AX and MP operations. The arithmetic and Wade
backend are attributed to the unchanged busy-beaver snapshot at
`297ab8df7e5de329605c3875b4934643b371a5e3`. The E7 basis is recovered directly
from the Git ZIP at arrival `61e77836565f63582561f54745f633d50efd9c7d`, member
`zfc_consistency_research_20261016/experiments/equational/basis.json`.
The driver records exact input hashes and does not depend on a future inbox
file remaining present. The source report's ordinary algebraic calibration
and validity reduction do not supply the missing literal ZFC query here.

## Representation and command contracts

Term codes are 0=c, Q(n)=3n+1, R(n)=3n+2, and NAND(a,b)=3P(a,b)+3, with the
published dual Cantor pairing P. Every natural is a finite ground term code.
An equality record is rawP(a,b). In particular0 denotes c=c. The demonstration
query is cached record 1=P(1,0), namely q(c)=c; it has no ZFC calibration.

At a command boundary, top, cache, and every head of the infinite unshifted
stack stream must be E7-derivable equalities; axiomcode and scratch 6/7 are 0.
Next-candidate, proof-pointer, and additive-parameter registers are natural
counters. Temporary term operands may occupy the stack inside a command.

The original command tags1/2 retain DROP and NIP. DROP saves top and loads the
cache. NIP halts when the cache equals the query, otherwise loading the stack
head. Tag0 reads an additional field:0 transitivity,1 symmetry,2 Q congruence,
3 R congruence,4 first-argument NAND congruence, and every larger value
second-argument NAND congruence. The dispatcher restores axiomcode 0.

Transitivity maps top P(a,b) and cache P(d,e) to P(a,e) when b=d, otherwise to 0.
Both branches restore the entire stack and clear cache/additive/scratch data.
Symmetry and Q/R congruence preserve cache and additive data. Each NAND
coordinate operation takes its arbitrary sibling term from the additive
register, clears the cache, and preserves the complete underlying stack.
Full binary congruence follows by two coordinate operations and transitivity.

Tags 3+z emit all seven basis instances with x=additive, y=cache+the next
field, and z=the residual tag, then clear axiomcode/additive/cache. The basis
has 33 parameter occurrences, 19 NAND nodes, 17 Q nodes, 12 R nodes, and 7 equality
records: 88 postfix constructor calls in all.

## Coverage argument and finite verification

There is a concrete normalization macro, using zero additive fields:

    DROP; SYM; TRANS; Q; TRANS; NIP; DROP; NIP

It preserves the current proved equality and underlying stack and sets cache
and additive data to 0, or halts on an equality already proved equal to the
query. After the first transitivity, Q makes q(b)=q(b). Its next transitivity
against c=c fails because3b+1 is positive, producing the harmless c=c record.
The final three stack operations restore the saved equality and stack.

One emitted axiom instance can be selected by fixed stack operations, the
known finite AX prefix discarded, and this macro applied. Thus all ground
substitutions are available from zero parameter/cache data. Reflexivity is
built from c=c by constructor congruences. Finite equational derivations can
then be compiled recursively, saving and recovering premises for transitivity.
The retained pairing-based candidate list represents every finite augmented
command list. This is an ordinary source-level coverage argument; no new Lean
theorem or binary simulation is supplied by this experiment.

The completed checks compare 14 exact AST endpoints and execute 492 constructor,
256 transitivity,208 other-inference,8 dispatcher, and 6 full main-field-read
cases against their declared register contracts. An initial wider NAND grid
was interrupted because unary arithmetic expanded nested Cantor stacks; it is
not counted as a successful run. The completed NAND grid uses endpoints and
siblings0..1. Exact-word Re-Pair seeds 0..31 preserve all 88 emitter calls; seed 24
produces the smallest measured controls. Only the emitter word is reassociated.
Every emitted decision edge in all 66 measured tables is checked against its
source DAG. The sole undefined row 1.inc/read1 is totalized as write1,R,halt,
with no additional state.

An independent read-only review of the initial construction found no semantic
defect, supplied the normalization/storage argument, and checked that no stale
hash-cons entry was actually reused. Its snapshot hashes and scope are retained
in `results/equational-generator-independent-audit.json`. The permanent driver
adds provenance, grammar alternatives, functional checks, and edge reextraction.

## Reproduction and scope

From the repository root:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/equational_generator_cost.py \
  --seeds 32 --scratch /tmp/zfc-equational-generator-replay \
  --output /tmp/zfc-equational-generator-replay.json
```

The recorded run is `results/equational-generator-cost.json`. Tables, source
DAGs, and label maps were saved under`/tmp/zfc-equational-generator-final`.
The best complete-control table is `control-seed24.tm`, SHA256
`e836cf8a6c88a88608d7ac76e25a6b4acfc4736a5b81a191c00624891a574a25`.

The generic Wade bootstrap is included in the state count. Its establishment
of this new source invariant remains unverified, as does general binary
runtime simulation. The actual ZFC target, its construction/writer cost,
formal equational-calculus completeness, and arithmetic consistency endpoint
remain open. Adding that target can also change sharing and dispatcher cost.
The 299-state result is a cost baseline for this architecture.
