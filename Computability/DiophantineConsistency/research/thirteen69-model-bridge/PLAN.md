# Model bridge for the thirteen-variable 69-operation carrier

This is a source survey and plan, not a completed iPRA equivalence or a new
kernel replay. The fixed positive-variable graph is
[`polynomial69.json`](../thirteen-variable-independent/polynomial69.json)
(SHA-256 `3400069ead0bbf7b85d382c47fdd790bc18d68d9979e049f475d4e1c52d4182f`).
The separately reviewed finite audit and its exact scope are in the
[graph review](../thirteen-variable-independent/ROOT_FINITE_REVIEW.md): 13
positive variables, 69 binary operations (39 multiplications, 16 additions,
14 subtractions) and exact total degree 174. The audit checks every row and
an exact nonzero degree-174 leading form. The graph uses the **whole
phase-split2471 tuple**, not the distinct 2011 or compact44 tuple. Its four
ports, their entire byte bindings and the ordinary proof are documented in
[the graph packet](../thirteen-variable-independent/README.md).
The count treats fixed integer ports as leaves; it is not a count of decimal
digits or a claim of global minimality.

The new [`ModelThirteenRestoration.lean`](../../Lean/DiophantineConsistency/ModelThirteenRestoration.lean)
(SHA-256 `8e1f80500e54ee71b40085a01cdb00c22e69e66426fc823950dd07ab69380bfc`)
proves `restores_positive_zero69`: with a positive beta port, all 13 coordinates
positive, appropriate ordered-ring facts and its signed-residue hypothesis, a
zero of `ThirteenCarrier.value69` restores a positive `Carrier65.value` zero
at the *same four ports*. Its `modelSignedResidue` supplies that hypothesis in
the difference ring of an arbitrary model of IΣ₁. Instantiating all the ring
facts and translating between ring-positive elements and model coordinates,
and between this evaluator and the exact literal expression, are still explicit
bridge steps; the imported theorem by itself is not a native iPRA derivation.

The other direction exists over standard integers:
[`ThirteenCarrierComplete.lean`](../../Lean/DiophantineConsistency/ThirteenCarrierComplete.lean)
(SHA-256 `5f971560bae4ca88ba157fcb8a398e6f3f0bf418cd70491051c69bb8bf278fc0`),
`positive_zero_completes`, uses `PortBounds`, a native mask `Interface` and
`MC % 4 = 2`. It preserves the outer coordinates and replaces the four private
ones with fresh positive Pell witnesses. This is an integer theorem; it does not
by itself supply witnesses in an arbitrary nonstandard model.

To obtain the missing all-model direction without circularity:

1. Translate the stated parent-zero consequences, including the rank's
   required residue class, canonical Pell ordinate, positive transport `G`
   and beta-times-J divisibility, to the chosen model and exactly the same
   port tuple. Establish each mask and port premise from its native
   specification rather than assuming the desired equation equivalence.
   For the distinct current-2011 tuple, the [actual-zero outer theorem](../thirteen-model-current-outer/README.md)
   now derives the positive divisible transport and carrier ordinate; its
   paired replay passed an [independent artifact audit](../../reviews/thirteen-model-current-outer-independent-audit/README.md).
   The actual-zero rank phase `R mod 4=3` also passed an [independent artifact
   audit](../../reviews/thirteen-model-current-phase-independent-audit/README.md).
   The full graph converse remains open, and the parent prefix and suffix
   have no complete printed axiom inventory.
2. The fresh model-level [strong Pell seed](../thirteen-model-strong-seed/README.md)
   now supplies positive `t,f,i` with ordinate `b*i*c²` when `b,c>0`;
   its paired replay passed an [independent artifact audit](../../reviews/thirteen-model-strong-seed-independent-audit/README.md).
   A subsequent [model auxiliary seed](../thirteen-model-auxiliary-seed/README.md)
   supplies positive `T,u,y` and the stated quotient residues when also
   `R mod 4=3`; its paired replay passed an [independent artifact audit](../../reviews/thirteen-model-auxiliary-seed-independent-audit/README.md).
   A separate [audited model residue](../../reviews/thirteen-model-negative-residue-independent-audit/README.md)
   proves the required `y+1` divisibility under the stated phase and base
   assumptions. The conditional [fresh-private model assembly](../thirteen-model-fresh-private/README.md)
   combines these ingredients and constructs a signed carrier with positive
   `m` given `G>0` and `b ∣ G`; its paired replay passed an [independent artifact audit](../../reviews/thirteen-model-fresh-private-independent-audit/README.md).
   Deriving those assumptions from the parent zero remains open. The
   standard-integer `ThirteenFreshSeed.fresh_private_seed` is not an
   arbitrary-model theorem.
3. The [69-row DAG binding](../thirteen69-dag-binding/README.md) now proves
   the generic-ring equality to `value69` and its shifted 2011-port model
   statement. Its [independent audit](../../reviews/thirteen69-dag-binding-independent-audit/README.md)
   checks the 69 rows and four symbolic port slots externally. An [independent
   degree audit](../../reviews/thirteen69-degree2011-independent-audit/README.md)
   also verifies exact degree 174 for the distinct 2011 tuple. The 2011-port
   candidate still needs both model implications with the same full tuple,
   and any displayed equation needs its own exact binding. No single scalar
   bound or matching beta alone establishes equality of four whole constants.
   The [conditional current-2011 converse](../../reviews/thirteen-model-fresh-graph-independent-audit/README.md)
   constructs a shifted 69-literal zero from a positive parent zero in each
   `IΣ₁` model under four explicit port equalities. Its [fixed-port specialization](../thirteen-model-exact-port/README.md)
   discharges those equalities; the paired replay passed an [independent artifact audit](../../reviews/thirteen-model-exact-port-independent-audit/README.md).
   The opposite model direction and iPRA endpoint remain separate checks.
4. Prove the phase-split2471 tuple's native checker/calibration and link its
   interpreted refutation predicate to the particular consistency statement;
   a theorem for another 2011 or compact44 tuple does not supply this link.
   Only then apply the repository's independently justified all-model to
   internal-provability bridge with its exact theory and axiom assumptions.

A distinct [2011-port route](../thirteen-model-2011-port-route/README.md)
would instantiate a newly constructed thirteen-variable expression at the
already calibrated 2011 tuple. It still needs the uniform model converse,
exact new literal and size binding, and a coherent endpoint replay; it would
not calibrate the original phase-split2471 graph.

The completed 70-source difference-ring pair and its independent audit
([receipt](../../reviews/ordinary12-coexistence-pair-independent-audit/CHECK.json))
provide useful prior evidence, but the newly merged restoration and odd-residue
modules are outside that frozen closure. Any replay of them needs an
out-of-tree, authenticated source snapshot of their full transitive import
closure and a coherent rebuild or separately audited ancestry; never splice
fresh model sources into incompatible historical project objects. The source
survey here neither proves that closure compiled nor asserts fixed-port
calibration, fresh-seed completeness in models, or an iPRA endpoint.
