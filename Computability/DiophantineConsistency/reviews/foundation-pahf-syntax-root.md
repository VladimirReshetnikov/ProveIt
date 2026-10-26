# Foundation arithmetic syntax to PAHF: independent root review

26 October 2026. Root read the complete252-line main,87-line checks and
author receipt, and inspected the complete dependency inventory against
the previously accepted Foundation GG and HA prerequisite records.
Root independently compiled both leaves in
`/tmp/foundation-pahf-syntax-root-peer-cd103i4h` with Lean4.32, `-M6000 -j1`
and source-level async disabled. Both passed. Their objects and logs are
byte-identical to the author's. All15 axiom reports use only `propext`
and/or `Quot.sound`; there are no final errors or warnings.

The translation uses independent environments for bound and free terms,
then places bound index i at i and free index j at n+j. It maps0,1,+,*
to0,S0,+,* and preserves equality and the intuitionistic logical constructors.
Strict order is explicitly existential: a<b means there exists z
with a+S z=b. Both arguments move beneath this extra binder, so the new
witness captures neither source free variables nor existing bound ones.

Generic term/formula substitution and source-rewriting compatibility are
proved structurally, including the actual `Rew.q` quantifier equations.
The canonical laws cover both binders, opening exactly one outer variable,
shifting unbound formulas, one-variable instantiation and insertion under
a new binder. The depth restrictions are explicit; no unrestricted
bound/free identification is assumed. Focused literal checks exercise two
source binders plus the new order binder, a free-variable-containing
replacement under another quantifier, equality orientation and a closed
example. Root checked these index calculations directly.

The59 Foundation records are exactly the prior accepted GG inventory,
and the five PAHF records are exactly the prior HA inventory. Root checked
all369 source/cache-source/trace/object SHA pins before and after replay,
plus compiler/toolchain/manifest identity. Private symlinks reuse those
objects; no prerequisite, vendor or shared object was rebuilt or modified.
The earlier Foundation Lake-hash authentication retains its scope; this
packet is not a fresh Foundation/PAHF/package closure validation.
Durable root commands, logs and pins are in
[foundation-pahf-syntax-root-replay/ROOT.json](foundation-pahf-syntax-root-replay/ROOT.json).

These are syntax identities. They supply no intuitionistic proof-tree map,
translated arithmetic axiom proofs, induction transfer or HA consistency
equivalence. The literal translation of x+1 still contains addition;
identifying it with successor needs an arithmetic derivation. A general
target-sentence closedness theorem is not supplied by one closed example.
The module remains a narrow standalone leaf, without an umbrella import;
combining broad Mathlib matrix imports with Foundation still needs explicit
compatibility work. The decimal equation artifacts remain unchanged.
