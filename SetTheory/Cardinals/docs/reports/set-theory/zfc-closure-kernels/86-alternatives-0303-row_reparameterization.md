# Exact logical-row reparameterization

## Measured result

A bounded search over independently reparameterized logical axiom schemas
found a **267-working-state** complete Wade table, compared with the matched
268-state original-word control. The source DAG has205 decision nodes instead
of206, with maximum zero depth7 in both. This is not better than the separately
audited201-node global grammar or the246-state optimized machine. Its useful
output is a new exact-same-theory source word for stronger compiler searches.

The reparameterization search method itself is prior work: the preserved
`19-subst-engineering-full_logic_search.py` already supports the six ordinary
row maps and twelve single-u rho8 maps. The new item here is the measured
267-state result and its exact emitted artifacts, not invention of that
search freedom.

The search examined218 combinations of parameter maps and29,886 safe grammars.
Files in `permuted_rows/` contain the complete534-row table, its source DAG,
macro word, selected grammar and all measured parameters. Its table SHA-256 is
`fa866a802fc61cda9aae388750a0253088086470e0f86b5167cdcb4168a2b70e`.
The compiler independently re-extracted every emitted source edge; one unused
undefined framework row was totalized as in the matched baseline.

## Exact changes

Keep GEN, the theory bundle, its conjunction layout, all gates, and the order
of emitted logical rows unchanged. Change only the parameter maps of four rows:

| Row | Old parameters replaced simultaneously by |
|---|---|
| rho8(a,b,c,u) | rho8(b,u,a,c) |
| rho7(a,b,c) | rho7(b,c,a) |
| rho6(a,b) | rho6(a,c) |
| rho5(a,b,c) | rho5(b,c,a) |

All other rows remain identical. The rho6 map is implemented by the full
permutation swapping b,c, even though the old formula does not mention c.
These are row-local changes: the theory C/G formulas continue to use the
original a,b,c meanings.

Each map is a bijection on the universally ranging numerical parameters.
Consequently each row emits **exactly the same family of numerical formulas**
as before. This does not need a new quantifier theorem, equality erasure,
set-theoretic interpretation or formula renaming lemma: it is ordinary
reindexing of the axiom schema's metalanguage parameters. This is different
from changing bound names *inside a fixed formula instance* without changing
the correspondingly selected instance.

## Complete proof-enumerator adaptation

For an old desired rho_j instance at parameters v, the new leaf block chooses
the AX parameters given by that row's inverse permutation. The existing
AX-selection block then extracts the same desired numerical code. The other
rows emitted by that AX call may differ, but the block discards them. Their
outer implication codes still cannot equal1, so the original NIP cleanup is
valid. The bundle leaf is unchanged; its other pushed rows are also discarded.
GEN and its old-cache behavior are unchanged. Thus the original induction on
C254 derivations gives completeness after replacing each logical leaf's
parameter tuple by the indicated inverse. Soundness follows from membership
in the same old axiom family. The exact native derivability predicate and its
Con(ZFC) target are unchanged.

The special fourth parameter u requires an implementation restriction. The
original helper reads u from the remaining candidate stream directly at its
single occurrence; it is not a persistent scalar register that can be copied
arbitrarily often. The search therefore permits a rho8 permutation only when
the resulting formula contains u **exactly once**. The winning map satisfies
this: u takes the old b position, while the old u position is filled by c.
Symbolic emission confirms that the fourth field is consumed once and that
all nine pushed rows and the bundle are precisely the intended formulas.

No claim is made that arbitrary permutations with repeated u are implemented
by the present scalar emitter; those would read additional candidate fields
and would be a different source interface.

## Search and verification scope

`permuted_row_search.py` imports only the preserved compiler/helper modules
used for the matched control. It considers the six a,b,c maps for each
ordinary row and the rho8 bijections satisfying the single-u constraint.
Coordinate descent uses shared grammar seeds, followed by1,000-seed deep
searches for the eight best layouts. Every grammar expands exactly to its
selected macro word; every best emitted machine passes edge re-extraction.
This is finite optimization evidence, not a lower bound or a proof-assistant
certificate for the full emitted binary machine and its startup.

A separate bounded follow-on, `permuted_rows_global.py`, applies the preserved
source67 finite-dictionary closed-association optimizer to this new word,
The first finite dictionary model, with zero depth<=7 and path depth<=39,
was infeasible. The raw Wade source has actual path depth95; a finite phrase
dictionary need not contain its shallower associations. Removing the artificial
path-depth restriction returned a **204-node,266-state** solution, with
zero depth7 and path depth95, in22.84 seconds. The solver reports optimality
only within its finite length20 repeated-phrase dictionary, not among all
programs or grammars. Exact results are in
`permuted_rows_global/results.json`. It compares
canonical closed-sequence/control trees before emitting a complete table;
that comparison is only reassociation of this changed source, not a claim
that the original and reparameterized instruction traces are identical.

## Additional gated-component label swaps (negative)

An independent bounded follow-on swaps a,b separately inside each of the four
bundle components C,G,Vrel,Veq, holding c fixed and keeping the original gate
c!=a,b. Each swap preserves its exact gated component family: replace the AX
parameters a,b by b,a, which preserves both gate inequalities. The full bundle
theory is unchanged because its components are individually projectable and
recombinable with the retained full propositional calculus. No alpha-renaming
or numerical freshness theorem is needed for this schema reindexing.

This differs from permuting c, which is both matrix code and hull index and
also appears in the gate; arbitrary three-way component permutations are not
claimed safe by this argument. It also differs from source19's within-formula
conjunction rearrangements.

`bundle_label_swap_search.py` tested all16 component-swap masks, then deeply
searched the four best. Across21,600 safe grammar trials, the best remained
the unchanged mask0 at267 working states. Exact per-mask costs and the
complete table are in `bundle_label_swaps/results.json`. This fixed-layout
family supplies no additional saving.
