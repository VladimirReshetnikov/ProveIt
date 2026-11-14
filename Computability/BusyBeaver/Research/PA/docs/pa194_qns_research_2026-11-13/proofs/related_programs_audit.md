# Theory audit and transferable ideas

Snapshot: `317b07268681b44ff352d173a162e2a8c241b2fe`.
All paths below are relative to the ProveIt repository.

## Exact proof status of the PA baseline

`Computability/BusyBeaver/Research/PA/README.md` explicitly distinguishes the
ordinary mathematical PA calibration from the newer, stronger formalization
goal inside iPRA. Neither machine-specific direction in iPRA is currently
established for primary PA194, original PA195, or PA196. The primary PA194
packet states an ordinary mathematical PA-provable equivalence and supplies
finite and symbolic implementation certificates. Source coverage, scheduler,
quotient, clock/source composition, and the exact zipper bridge are reusable
formal components; they do not on their own prove either machine-specific
internal iPRA consistency reduction.

The ordinary source calibration is documented explicitly in
`Computability/BusyBeaver/Research/PA/docs/pa194_conpa_2026-11-13/report/calibration.tex`.
It supplies both syntactic reductions using PA proof annotations and a
PA-refutation compiler. Its treatment of finite binary comprehension is a
syntactic proof supplier, not a uniform arithmetical truth predicate. The
coincident-label gate case and numerical aliases I(0,0)=0 and p(0,0)=0 are
handled separately. A new source-equivalent or proof-equivalent design may
inherit this calibration, but must identify that dependence.

## What transfers from ZFC

The ZFC README records actual Lean/Rocq endpoints for exact K215, but separates
that external equivalence from the still-open internal PA endpoint for K215.
An exact internal PA theorem is recorded for the older 240-state machine.
Thus one should not cite every ZFC construction as already internally
calibrated in PA.

Useful ideas concern implementation and finite proof transformations:

* History-sensitive reader folding, source reassociation, and simultaneous
  local checks are neutral with respect to whether the proof calculus targets
  PA or ZFC. They need the actual new table's incoming-context invariant.
* The no-push successful-MP command and compiler-supplied spare zero are
  established in
  `Computability/BusyBeaver/Research/ZFC/candidate-k215/alternatives/zero-spare-transfer/report.tex`,
  section "Removing the successful MP zero push." The changed ZFC source
  needed 216 physical states despite fewer source operations. This is a clear
  warning that source shortening alone does not establish a TM state saving.
* Hereditary formula-code and variable-label recoding occurs in
  `Computability/BusyBeaver/Research/ZFC/k218-ks-mixed-commutation/README.md`.
  Co-translating variable labels is indispensable for diagonal self-vacuity.
* The protected-stack-tail credit proofs and arbitrary-clean-seed theorems
  can justify new startup regimes, but their exact command balances and
  initial theorem annotations must be re-established for a PA controller.
  The PA baseline already has a clean seed, so an exotic unsafe seed would
  add proof obligations without an automatic state advantage.

The new head-exchange derivation needs only K, S, and modus ponens. It can be
instantiated in either arithmetic program once the dominated-rho8 template
has supplied K and S. This is a reusable proof transformation, not reuse of
the ZFC consistency calibration itself.

## What transfers from ConciseIPRA

`Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/README.md` defines the project
as complete presentations bi-interpretable with full first-order iPRA. Its
metric counts a standalone Python proof checker (normalized significant
tokens, AST nodes, and bytes). The native scalar core uses a numerical
iterator, equality, Q and D formula constructors, and the Hyp/Tr/QE/DE/DI
rules; familiar logical connectives are derived.

Those are useful lessons in identifying redundant proof-checker machinery
and compiling semantic interfaces into a smaller primitive language. They
do not directly give a smaller PA-consistency machine:

1. The theorem to preserve here is refutability of PA. A proof checker for a
   theory bi-interpretable with iPRA has a different calibration target.
2. A compact Python module can use large runtime primitives such as binding,
   recursive substitution, and list traversal. These operations must be
   implemented on the single binary tape and charged to the state count.
3. The PA source's syntactic proof supplier for finite comprehension uses
   full PA induction on arbitrary formulas. Replacing its numerical calculus
   by the small iPRA core requires a new PA refutation translation, rather
   than an appeal to the core's simplicity.

A promising long-term route is a small certificate calculus whose PA-strength
induction is encoded structurally, together with a finite compiler accounting
for every binding and substitution operation. No such lower-state compiler
was established in this task.

## New mathematics isolated by this investigation

`calculus_transports.tex` proves two independent changes:

* Exchange the curried premises in either or both membership-rewriting heads
  (and optionally the already-known universal-distribution exchange). A fixed
  61-node K/S/MP proof DAG supplies exact conclusion-preserving translations
  in both directions. Parameters of each universally instantiated head may
  also be permuted independently.
* Swap quantifier/equality constructor residues 2 and 3, keeping implication,
  membership, truth, and contradiction fixed. Hereditary recoding F is an
  involution of all natural codes. It must act on labels as well as formulas.
  Its failure of monotonicity (F(2)=3, F(3)=2) is repaired at dominated-rho8
  leaves by the unrestricted finite proof template.

`command_compiler.tex` is a complete proof compiler for the no-push controller
with the original t+h=1 Shift guard, accepting either changed emitter once its
literal implementation has been verified. It explicitly covers the zero
aliases, dirty incoming stores, arbitrary carried stack tails, finite
candidate enumeration, and both refutation directions.
