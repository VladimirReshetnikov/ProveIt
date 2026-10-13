# Conditional type propagation: prepared experiment and proof boundary

Prepared during the fixed-U1 publication benchmark. No script has been executed
and no matching queries, LPs, rays or Pachner searches have been run in this
slice. Parent release after the benchmark is required before executing probe.py.

For a fixed valid source and current sorted mask J, let a=(tet,type) belong to
J. Form J_a by removing the other types at that tetrahedron and retaining all
other types in J. Any compatible matching vector with q_a>0 is supported in
J_a. Thus a proof that every nonnegative Q matching vector on J_a has q_a=0
licenses removing a from J while preserving all compatible matching vectors.

The existing matching_support arithmetic applies to arbitrary masks supplied
to _assemble_sector_kernel: triangle graph elimination, cycle nullspaces,
one/two-row sign closure and original STANDARD row provenance use no
quadrilateral compatibility hypothesis. It never calls the compatible-only
SectorKernel.lift. This is a code/proof inspection result, not experimental
validation of effectiveness. The existing public build_sector_kernel parser
and matching-support verifier intentionally allow at most one type per tet.
The scratch record therefore labels returned old-schema packets as raw private
producer provenance. It does not silently expand any native certificate schema.

The scratch replay independently reconstructs every row combination on the
original STANDARD equations. Every triangle coefficient must vanish. Remaining
Q coefficients on J_a must be nonnegative except for coordinates already
forced to zero earlier in this SAME local proof. Coefficients outside J_a may
have either sign because those coordinates are zero in this conditional test.
Each row forces its strictly positive remaining coordinates. The local forced
set starts empty for every tested a. Only if a is in the resulting local forced
set is a deleted globally. Other forced types are retained globally, since their
vanishing has only been proved under the condition selecting a's tetrahedron.

A new maintained implementation would need a new explicit sequential
mask-reduction schema: source digest, initial mask, tested types, original row
proofs and exact retained mask. The checker should derive each J_a itself.
The final restricted-mask negative Euler tree must be composed with this
coverage packet to infer original admissible negativity. A partial-mask tree
alone is not a full-root negative certificate, and existing native schemas
must keep their present meanings. Every topology reduction starts over on its
new source. No normal surface is altered by this algebraic preprocessing.

For nested masks J' subset J, K_J' is a coordinate face of K_J. Every root
extreme ray in the smaller face is an extreme ray of the larger cone. Its
fixed-source canonical lift, Euler value and conflict set are unchanged.
Therefore the positive incompatible-ray hypergraph of K_J' is a subhypergraph,
and its parameter h_J' is at most h_J. This is MASK monotonicity. The original
full-source h(T) has not changed. In particular a negative tree on a final mask
with split union B gives only h_J <= |B|; even when the elimination packet and
tree together decide the original admissible problem, they do NOT establish
h(T) <= |B|. No uniform small h_J theorem or algorithmic speedup is assumed.

The deterministic scan uses sorted types and restarts after each accepted
single deletion. If initially k<=3t, at most k deletions and O(k^2) tests occur.
Each sufficient closure/kernel/provenance computation has polynomial arithmetic
and bit complexity on these finite source equations. The code's row-space
sign closure is incomplete; a fixed point does not certify that surviving types
are feasible, and a capped test makes no assertion about q_a positivity.
No full LP support oracle is used in the first experiment.

The six exact diagram-authenticated U1 endpoints come from the frozen staged
archive: T7,F10,TT16,T25(11),T27(17),W34(31). Each source has an approved cap of
1,000,000 explicit check() invocations across _prepare, all kernel assemblies,
and all sufficient closure/provenance calls. Total discovery checks are at most
6,000,000. This cap counts callback invocations, not CPU time or every bit
operation. Independent solver-free replay work is explicitly excluded. There is
no wall cutoff. Every attempted current/conditional mask, successful provenance,
no-effect outcome, preparation failure and capped partial query is retained.

Files:
- probe.py: bounded pure matching propagation; writes probe.json.
- replay.py: solver-free source-chain and original-row replay; writes replay.json.
- Any negative control deleting another conditionally forced type is produced
  only if a real retained proof supplies such another type. No manifold or
  geometry fixture is fabricated to manufacture that coverage.

After parent release, planned commands are:

    python -B /tmp/conditional-type-elimination/probe.py --max-checks 1000000 > /tmp/conditional-type-elimination/probe.txt
    python -B /tmp/conditional-type-elimination/replay.py > /tmp/conditional-type-elimination/replay.txt

All source pins are captured fresh at generation/replay. These files preserve
full returned source arrays and bind the source archive by exact byte digest.
The independent checker does not import the kernel or matching-support producer.
General quasi-polynomial recognition remains unproved.
