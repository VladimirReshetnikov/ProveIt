# HA addition and multiplication: independent root review

26 October2026. Root read the complete111-line additive module and81-line
checks, and the complete220-line multiplicative module and97-line checks,
including their author receipts. All statements construct actual finite
`HA.Proves` derivations. They do not convert standard arithmetic truth or
classical PA derivability into HA theoremhood.

The additive module proves successor addition, commutativity and
associativity. Each universal family uses the actual formula-induction
rule proved from HA's induction axiom. The multiplicative module proves
zero/one laws, both distributive laws, successor multiplication,
commutativity and associativity. Six universal families use actual formula
induction. The additive interchange used for distributivity is an explicit
chain of HA equalities. Arbitrary ambient terms are shifted around the
substitution hole; nested quantifiers and independent free parameters are
retained in the checks. No metatheoretic ring normalization replaces an
object-language derivation.

Root independently compiled all four new leaves with `-M6000 -j1
-DElab.async=false`. All passed, both main logs are empty, all four objects
are byte-identical to the corresponding author objects, and all36 reports
use only `propext` and `Quot.sound`. The additive pair reused eight custom
prerequisites, with21 source/cache-source/object observations; the
multiplicative pair reused nine, with23 observations. Compiler and package
identities were also checked. Cached prerequisites and package boundaries
were reused, rather than freshly rebuilt. Every selected pin was checked
again after compilation.

Exact sources, objects, commands, logs and pins are durably recorded in
[ha-additive-arithmetic-root-replay/ROOT.json](ha-additive-arithmetic-root-replay/ROOT.json)
and
[ha-multiplicative-arithmetic-root-replay/ROOT.json](ha-multiplicative-arithmetic-root-replay/ROOT.json).
The author dependency inventories remain unchanged. The isolated root
driver is saved with its exact execution hash in each replay folder.

These results supply conventional HA semiring facts needed to discharge
Foundation's translated arithmetic axioms. The actual translated axioms,
arbitrary induction/closure comparison and final equation/consistency
equivalence remain separate obligations. The displayed equation is unchanged.
