# Two alternative 215-state machines

This packet contains two 215-working-state, two-symbol Turing machines, each started on an entirely blank tape. The primary machine is the re-encoded source with changed blank bootstrap described below. The secondary machine changes the rho6 axiom sampler and is described in secondary/. Each machine has its own exact source, startup evidence, and full runtime certificate. Their consistency calibration is inherited from the attributed parent construction included in parent/. The primary uses the same numerical calculus and the same primitive register-machine operations, not a new formalism. The secondary changes a numerical axiom sampler under its separately supplied all-natural source/compiler argument.

## Primary: what is materially different

- Seventeen native transition rows differ from the delivered primary 215-state machine.
- The labelled transition graph is nonisomorphic even without fixing its initial state to the delivered primary, delivered secondary, and the separately published 11/134-wrapper variant. The verifier supplies color-refinement certificates and an independent rooted-mapping contradiction.
- The source retains 202 DAG nodes and 4,751 primitive occurrences, but changes 4,519 instruction addresses. The number of addresses containing six consecutive zeros falls from 37 to 33. Both independent guarded-control resolvers prove identical ordinal/register-store semantics.
- Blank execution first diverges from the primary at step 3,307. It reaches a genuine zero-PC root after 716,307 steps, rather than 95,714. The new logical seed is (N,T,W,A,D,H,X,Y,L)=(4,0,0,0,1,0,0,0,0), with head -9, gap 152, and 185 spare registers. This is not an instruction-interior dispatcher frame.
- The nonzero additive counter requires the explicit seed calibration in proof/seed_calibration.md. The physical runtime proof covers arbitrary natural register values, so no restricted reachable-state bitmap is needed.

The alternative is not a speed improvement and is not a 214-state construction. Its material novelty is the physical encoding, transition graph, and bootstrap behavior.

## Reproduce the checks

Use Python 3.10 or later, with assertions enabled, from any working directory. The supported entry point is verify.py; the inherited runtime helper modules are imported libraries, not standalone command-line tools:

    python /path/to/packet/verify.py

The default verifier checks the exact file manifest; safely extracts and verifies the included pinned parent; reconstructs all table presentations and the source from explicit recipes; proves source correspondence using two independent complete guarded-CFG resolvers; replays every blank transition and independently decodes the entire root frame; checks graph nonisomorphism; and verifies the complete stored symbolic certificate inventory and its exact byte bindings.

To freshly derive every arbitrary-natural primitive case for the primary, additionally run:

    python /path/to/packet/verify.py --runtime

For the secondary fresh runtime derivation use --secondary-runtime. Both flags may be combined. Each full derivation can take several minutes or longer. The default verifies the stored certificate inventory and its binding, not a fresh universal derivation. This is an ordinary mathematical symbolic-induction proof, not a new Lean/Rocq or internal-PA proof-assistant endpoint.

Use --work /new/directory to retain regenerated audit receipts and logs. The directory must not exist and must be outside the packet. The verifier does not modify this packet or the included parent archive.

## Secondary: a changed rho6 sampler

The secondary replaces two native transitions in the included original primary parent: 199/1 becomes 1R12 and 206/0 becomes 0R76. It changes the rho6 sampler from the old parameter pair to (A,B), with the exact all-natural source/compiler argument in secondary/proof/. It reaches its independently checked blank root after 95,714 steps and has a fresh complete certificate for 6,176 cases, totaling 1,699,838 symbolic rules.

The same semantic source appeared in the public intake199 work. No source or semantic priority is claimed. The supplied physical table differs from that public prefix-only allocation and has its own complete runtime/startup verification. See secondary/evidence/intake199_comparison.json and its attribution.

## Contents

- machine/k215.tm: dense canonical states 0 through 214, halt 215.
- machine/k215.native.tm: inherited native labels, halt 254.
- machine/k215.normalized.tm: discovery labels; native 301/302 are normalized 79/102.
- machine/canonicalization.json: exact bijections and byte hashes.
- source/sites215.json: complete current source; DAG and table recipes specify its reproducible construction.
- code/reconstruct.py: generator from the exact included primary parent, with old-row assertions for all seventeen replacements.
- code/check_source.py and source_tools.py: all-natural source bisimulation checks.
- code/check_seed.py: complete blank replay and exact zero-PC root decoder.
- code/check_novelty.py: comparison with three pinned baseline tables.
- code/validate_native.py and code/runtime/: full universal symbolic runtime verifier.
- evidence/: the full runtime certificate, compressed case records, compressed literal startup trace, and exact root seed.
- parent/: the complete attributed primary/secondary parent release, including its inherited calibration dependencies.
- proof/seed_calibration.md: soundness and cofinal completeness from the changed counter seed.

The published wrapper comparison table is included solely as novelty evidence. It is not a construction or logical-calibration dependency. See provenance/input_pins.json and the included licensing/attribution records.
