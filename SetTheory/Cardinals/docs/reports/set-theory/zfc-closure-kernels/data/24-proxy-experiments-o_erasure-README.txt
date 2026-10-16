OUTGOING-PROFILE PROXY: COMPLETE-FRONTEND COMPILER CONTROLS
========================================================

Scope
-----
These are new compiler measurements for a mathematically complete source
interface, not end-to-end consistency machines. The principal strict EPSC
control has 288 working states. Its ordinary source proof-calculus argument
does not establish a register-enumerator or binary-TM simulation theorem.

The full report supplies the ordinary proofs. The key new observation is
that equality can be represented, in raw EPSC models, by the four-node
formula E(x,y) = forall z (R(x,z) -> R(y,z)). This is outgoing-profile
inclusion, not incoming-profile equality and not literal raw equality.

The direct proof uses the following full observational profile relation:

  O(x,y) iff [forall z (R(z,x) iff R(z,y))]
             and [forall z (R(x,z) iff R(y,z))].

EPSC first gives an empty object (use its false-matrix instance), then exact
classes for every subset-bounded equality-free predicate psi(y) (use the
constant matrix rho(x,y)=psi(y)). Since O(y,a) implies y is a subset of a,
there is an exact O-singleton s_a. Reflexivity gives R(a,s_a). If E(a,b),
then R(b,s_a), so O(b,a). Conversely O(a,b) immediately implies E(a,b).
Thus EPSC proves E=O. In particular E is an equivalence and a congruence
in both arguments of R. No Extensionality, global irreflexivity, or
incoming-profile saturation is used in this local result.

Reserved-zero translation
-------------------------
For source variables numbered 0,1,..., translate:

  bottom       -> R(0,0)
  R(i,j)       -> R(i+1,j+1)
  i=j          -> forall 0 (R(i+1,0) -> R(j+1,0))
  A -> B       -> translation(A) -> translation(B)
  forall i A   -> forall (i+1) translation(A).

The source has genuine bottom. Target R(0,0) is a distinguished formula F.
Every source binder becomes positive; binder zero occurs only inside the
equality proxy, whose body contains no F. Given a raw EPSC model, choose
any empty object e and fix assignment v_0=e. Then F is false. Interpret
source equality as O (equivalently E), or work in the actual quotient by O.
Formula induction proves the exact satisfaction translation. Generalization
at positive indices preserves this pointed semantics. Generalization at
index zero is excluded from the strict frontend.

This is why the strict EPSC control needs no separately emitted IR axiom.
Allowing unrestricted GEN0 would invalidate the pointed-model argument;
the report includes an explicit finite negative control.

Complete ordinary source interface
----------------------------------
The strict frontend preserves all eight original logical axiom patterns,
including existential equality, Euclidean equality, and both membership
transports. Equality atoms in these patterns are expanded by the translation.
Both atomic vacuity components are retained; every variable role is shifted.
Generic payload roles are not numerically shifted. The source calculus is
the ordinary complete equality Hilbert calculus specified by those patterns,
with genuine bottom, MP and GEN. It is not the retired equality-deleted
calculus. The equality-pattern images are valid in raw EPSC models because
E=O; they need not be pure logical tautologies over arbitrary relations.

Translate a finite source proof line by line. Implication and all source
binders translate homomorphically, MP translates exactly, and source GEN i
becomes target GEN(i+1). Every translated source logical axiom is one emitted
pattern. The source axioms are full EPSC instances, with arbitrary matrices
and finite parameter tuples. Their images are equality-free relative-F
wrappers: equality in a matrix is replaced by E, and every source Bottom
in the wrapper is replaced by F. They are not literally ordinary EPSC
axioms with genuine Bottom. At the chosen valuation v_0=e, all wrapper
binders are positive, so every wrapper-level F remains false. The image
is then equivalent to the genuine-Bottom raw EPSC instance for the
translated matrix. If zero is a free parameter of that matrix, the raw
schema universally closes it; instantiate that parameter at e. The
translated source axiom itself does not universally close zero.

For an exact numerical wrapper bridge, choose the canonical source auxiliary
binder for matrix phi to be code(translation(phi))+2. Its target binder is
then precisely code(translation(phi))+3. Such a source choice is legitimate:
it is fresh, and ordinary source logic identifies all capture-free choices
of bound names. No target alpha-conversion lemma is assumed to establish
this axiom-image step. One can take the source syntax without primitive Top,
so translated source formulas have positive codes and the numerical Top-at-0
normalization is absent from this proof translation.

Consequently the stated abstract strict target calculus is refutation-complete
for EPSC, and a model of raw EPSC gives a pointed model with F false. Combining
these two directions with the repository's ordinary EPSC consistency
calibration gives the desired abstract designated-target equivalence in ZFC.
This is an ordinary mathematical argument, not a serialized arithmetic proof
or a Lean proof, and not a correctness theorem for the tables in this folder.

Exact measured wrapper
----------------------
The EPSC emitter uses input variable 1, output variable 2, and k=c+3, where
c is the actual decoded matrix code, not a source variable index. Its local
bound is y subset k. Its initial active inputs are every raw empty object.
Support is unrestricted: y in C implies exists x rho(x,y). No support witness
is required to be active or to belong to C.

Base-three coding is Imp=3P, Rel=3P+1, All=3P+2, with Cantor P(a,b).
Code zero means Truth. Every decoded label is below its positive code,
and k=c+3 is always distinct from 1,2 and all matrix labels, including the
exceptional codes 0 and 1. The EPSC formula is pushed before atomic vacuity;
the original c!=a,b gate applies only to the current vacuity formula.

The distinction between object-variable roles and formula-payload roles is
essential. For example, All(a,B) shifts its binder a but leaves the scalar
payload B unchanged. The symbolic checker inspects full emitted ASTs after
every macro and compares them with independently transformed formula patterns.
It does not infer correctness merely from a state count.

Measurements
------------
The experiment tried the ordinary sharing control and 32 fixed grammar seeds
for each of eight declared cases, for 264 complete compilations. This is a
small selected family, not a global search or a lower bound.

  CG, strict, original order:             287 states = 224 + 63
  CG, strict, alternative order:          287 states = 225 + 62
  EPSC, strict, original order:           288 states = 225 + 63
  EPSC, strict, alternative order:        292 states = 229 + 63
  EPSC, symmetry, original order:         289 states = 225 + 64
  EPSC, symmetry, alternative order:      289 states = 226 + 63
  EPSC, combined, original order:         288 states = 226 + 62
  EPSC, combined, alternative order:      288 states = 225 + 63

The two summands are decision and framework states under the inherited
backend's naming convention. Every whole-machine count includes initialization.
The strict EPSC source interface is the main mathematically justified design.
The older collision-prone CG controls use ZFC's global IR for source soundness.

Optional symmetry and combined controls
--------------------------------------
These permit generic quantifier rules at every label, including zero, and
therefore use ZFC's global irreflexivity for relative-falsity soundness. Their
generalization is not justified by the pointed empty-object semantics alone.

The symmetry control replaces Euclidean equality by E(a,b)->E(b,a). No UI
or equality law is used to recover Euclidean equality: put
X_ij=(R(i+1,0)->R(j+1,0)). GEN0 of the propositional transitivity tautology,
followed by QI0 twice, gives E(i,j)->(E(j,k)->E(i,k)). Symmetry then yields
E(c,a)->(E(c,b)->E(a,b)). This derives the original Euclidean row.

The combined control additionally places both membership transports in one
conjunctive consequent, sharing E(a,b). Propositional conjunction elimination
and parameter renaming recover each original transport schema. These ordinary
derivations are not proof-assistant certificates. Neither shortened frontend
improved the 288-state strict EPSC measurement, so no broad optimization
search is recommended on this basis alone.

Reproduction
------------
Python 3.10 or newer, no third-party packages or network access:

  python measure_proxy.py --replay
  python audit_proxy_artifacts.py

The first command checks vendored input pins, reconstructs the eight frozen
best recipes, checks exact expanded macro words and symbolic emitted formulas,
and verifies state counts and named-table hashes. Outputs go to reproduced/.
The frozen evidence remains in measurement/.

To repeat the entire bounded family instead:

  python measure_proxy.py --seeds 32 --output another_output_directory

The second command executes 405 scalar-push/offset checks and 144 base-three
constructor checks with the independent structured-register interpreter.
It totalizes every frozen named table and independently compares every original
write/move/target action under the recorded bijective state renaming. Exactly
one previously undefined row, 1.inc/read1, is filled by write1,R,halt.
This preserves missing-transition halting and final tape contents, with one
extra final move; it is not exact step-by-step equivalence.

The principal total table is audit/epsc-strict-12345678.tm, with 288 working
states, 576 rows, blank/start state 0, and terminal label 288.

Attribution and pins
--------------------
The eight original logical patterns and published register DAG come from the
Mira-Cult machine, with Jeff's upstream verification, pinned upstream commit
297ab8df7e5de329605c3875b4934643b371a5e3. The full upstream verification was
not executed or ported here. The public binary backend is Andrew Wade's
MIT-0 code; its LICENSE.wade file is preserved.

The ProveIt recovery, symbolic-constructor, helper-interpreter and normalizer
tools are preserved unchanged in vendor/proveit/. The weighted exact-word
grammar tool is preserved unchanged from the incoming zfc_small_machine
report, source research pin 96836f9eea3540e96322c3d28c7127a582aae223, and
credits earlier source-08 grammar work. See vendor_source_pins.json.

The new files are measure_proxy.py and audit_proxy_artifacts.py, together with
this note and their generated measurements. They neither edit the upstream
snapshot nor confer proof status on inherited compiler code. The full
register-enumerator simulation, blank-entry binary simulation and final
Con(ZFC) equivalence for any emitted table remain open.
