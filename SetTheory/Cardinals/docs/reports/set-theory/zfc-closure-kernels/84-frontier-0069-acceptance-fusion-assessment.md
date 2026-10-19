# Can atomic acceptance reuse an existing tag test?

## The unchanged source has no such test

In the published 219-node DAG, nodes 142, 145 and 148 test the *command* field A
against the MP/DROP/NIP/AX partition. They do not compute a formula tag.
Nodes 119, 180, 181 and 182 construct implication, universal, membership and
equality codes in T. Intermediate subformulas at these constructors are not
certified theorems; accepting a constructed membership atom there is unsound.

At NIP (152), H is a proved cache value, but the only existing acceptance test
is the full comparison with one through nodes 132 and 123. At MP (150), the
program constructs `wim(T,D)` and compares it with H at node 130. Successful
comparison certifies `C254(D)` immediately before the edge into node 166.
This is a legitimate acceptance site, but it has not computed D modulo four.
These facts are directly reflected by `L2Control254.mp_branch`, `ifeq_par1`,
and `nip_branch`.

Thus the current program has no latent theorem-certified residue branch into
which the new acceptance predicate can be inserted without new computation.

## A prior alternative does have the relevant residue branch

The existing research source
`SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/53-span-semantics-deterministic_mp_cost.py`
replaces guessed-conclusion MP by a parser for the cached implication. At its
MP entry, it divides H by four using a four-decrement loop. Failure of the
first inner `require_unit` means the incoming H has residue one. The other two
inner failures mean residues two and three. Since the entry H is C254-derived,
only the first of these failures can soundly be redirected to halt by the
atomic-target theorem.

This would be a fusion with an existing class test *in that alternative
architecture*. It is not a mutation of the current 246 source with a free
residue test. The saved price control reports 302 raw Wade states for that
alternative with the old NIP halt, or 305 with an additional birth test. Those
figures are prior experimental controls, not newly verified results here.

## Obligations for a future implementation

- Prove that the differentiated residual branch is exactly the incoming
  residue-one case, even though H has already been destructively reduced.
- Retain the C254 invariant for H at parser entry, before treating H as a
  quotient, an antecedent or a numeric temporary.
- Check whether specializing the first residual failure breaks existing DAG
  sharing. Reusing an arithmetic loop does not imply zero extra binary states.
- If the old NIP halt is removed, prove that every refutation is forced to a
  new acceptance site. The deterministic MP variant changes success/failure
  behavior for arbitrary guessed D and has its own compiler-completeness
  obligation. The continuing-prefix argument for the simple atomic NIP patch
  cannot simply be transplanted to it.
- Supply the complete literal binary binding, bootstrap, positive whole-frame
  runtime argument and full state price for the actual changed source.

There is a useful logical fact for retiming acceptance: code F is neither the
truth code, a generalization, a rho-row root, nor a bundle root. Any C254
refutation therefore has a final modus-ponens inference. This identifies MP
success as a completeness-relevant production point, but it does not by itself
implement or price a cheaper test.
