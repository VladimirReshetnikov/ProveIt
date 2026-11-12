# Protected guarded certificates

## Acceptance and trust boundary

An input is one JSON array. Its final item is the closed goal; previous items
are instruction packets. Packets are consumed right to left using `pop`.
Unused prefix data is inert. Acceptance is normal exit with exactly
`ACCEPT\n`; no assertion or producer is part of the trusted implementation.

Every checker is self-contained and imports only the JSON parser. The three
compact profiles are different implementations of the same canonical theory,
but are not asserted to accept exactly the same noncanonical raw aliases.
The global token profile uses a global eigenparameter floor; the other profiles
use lexical floors. The local profiles initially retain `[]`, interpreted as
administrative truth; the global profile starts with an empty context.

## Public language

Canonical numerical terms are zero, successors, and scalar iterators. Their
raw forms are `0`, `[t]`, and `[n,a,h]`. An iterator binds one state variable in
its update. Its counter and initializer have dummy coordinates in the arity
codec; those dummy coordinates do not add mathematical operators.

The public formula grammar is:

- An equation `[s,t]`, where both `s` and `t` are iterator terms at the root.
- A paired binder `[B]`. If `B` is an equation, both of its terms must have
  the guarded form `I(y,0;u.h)`. If `B` is compound, it must itself satisfy the
  public grammar recursively.

The wrapper `W(s)=I(0,s;u.0)` makes every numerical equation available in the
public language. The contradiction is `W(0)=W(S0)`.

For a closed public raw goal, `strict_checker.py` checks exactly these
conditions. At an atomic D matrix, the required raw term prefix is `[5,0]`:
the bound index y occupies coordinate 5 inside the iterator's dummy counter
slot. The parser admits canonical odd protected-slot coordinates, not negative
free labels or Boolean substitutes for integers.

The compact kernels do not perform this public-goal check. The strict
standalone interface, including its parser and JSON input, is separately
measured. Intermediate computation axioms need not be protected public atoms.

## Administrative formulas and opening

Raw formula arities 1, 2 and 3 encode D, equality and Q. A canonical Q resource
is three copies of its body. Numerical root depth is 3 and formula root depth
is 0. Visiting a child of an array of arity r adds `5-r` to the depth. A
protected numerical slot has width 2; the odd representatives are `3+2j`.
Negative integer labels denote proof eigenparameters down to the current floor.

Opening preserves an admitted numerical coordinate. An unprotected relevant
coordinate is a substitution hole, and its proposed image is itself validated
at numerical root depth 3 before insertion. Even-depth padding remains truth.
An absent numerical image at an actually used hole fails. Witness opening
precedes allocation of the new eigenparameter.

Empty and surplus formula arities have administrative truth meanings in the
inherited sorted interpretation. In numerical positions, other arities can
serve as zero annotations. They are not extra public arithmetic constructors.
No theorem about interchangeability of arbitrary aliases is asserted.

All public and administrative D formulas use the same ordinary reading
`exists x (B(x,0) -> forall y B(x,y))`. Atomic progress introduction is sound
for this reading by equation induction under the conditional base; compound
case introduction is sound by numerical coverage. Thus every raw inference is
an instance of the inherited Choice-DI calculus. The public grammar restriction
is needed for reverse translation and formula round trips, not for ordinary
soundness. No completeness or formula-composite claim is made for arbitrary
unguarded administrative statements. An alternative progressive reading can
also establish soundness for unguarded atomic D, but is unnecessary here.

## Instructions

Every instruction is `[major,source,initializer,template]`.

1. The major is checked recursively. Local neutral major `[]` closes using
   the initial retained truth. In the global protocol a falsy major is a
   dispatch marker rather than a checked formula.
2. A truthy source selects the equality major `[source,initializer]`. A
   falsy source selects `[template,template,template]`, the Q resource.
   If the target instance of the template equals the current goal, checking
   continues with its source instance. Thus canonical literal-zero sources
   are not primitive equality-transport instances.
3. A successful unary D major exports its Q resource at a fresh witness.
   Other successful arities export only administrative truth.
4. With a neutral major and truthy initializer, a computation equation is
   constructed. A falsy source selects I0; a truthy source is the predecessor
   used to construct an IS source. Literal-zero initializers and literal-zero
   predecessors use the inherited certified-zero expansion in the producer.
5. With a neutral major and falsy initializer, exact argument unpacking opens
   a unary D goal at the given witness. The matrix root determines the only
   introduction rule: an equation gets its progress instance as hypothesis;
   a compound matrix gets its zero instance. The continuation is the successor
   instance in either case. The former explicit choice bit is absent.

The equality/Q dispatcher and the root-determined introduction are the two
composed reductions. Protecting public atom heads supplies a common setting
for their compatibility argument; it is not a claim that the two upstream
admissibility proofs can simply be concatenated without that argument.

## Verification record

`reproduce.py` measures all whole modules and records every test result in
`evidence/validation.json`. It audits all generated named proof trees for
literal-zero transport sources and every atomic D occurrence for the guarded
shape. The normalizer preserves goals and matrices. Its implemented domain is
explicitly narrower than a universal translation theorem and is documented in
`tests/protected_producer.py`.

The command runs ordinary Python and `python -O`. Raw scope and malformed-data
tests exercise the compact programs as well as the strict program, so their
rejection cannot be attributed solely to the optional public-goal parser.
