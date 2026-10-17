# Finite quotient certificates for the source44 closure kernels

This experiment gives an exact finite-stage checker and an ordinary proof that
its ideal unbounded refutation search has the same consistency contract as
FC15*/FC16*. It supplies no RM/TM compiler, measured state saving, Lean theorem
or PA representation. The source44 quotient/Herbrand argument and theory
calibrations are attributed to intake155, arrival
`fab89c5d26b81cd2ccab2ee5d213ff23725c7726`, archive
`zfc_finite_closure_2026-10-17.zip`, ProveIt input
`61e77836565f63582561f54745f633d50efd9c7d`. Source44 was placed at `799bcd094d`.
The finite certificate interface, code-segment staging and single-word
checker below are this follow-up; no historical priority claim is made.

## Reproduce from the original archive

From the repository root:

```sh
uv run --no-project python Computability/BusyBeaver/Research/ZFC/finite_quotient_frontend.py --output Computability/BusyBeaver/Research/ZFC/results/finite-quotient-frontend.json
```

The driver calls the existing batch155 helper with `--prepare-only`, recovering
the exact committed original layouts into a temporary directory. It executes
no submitted top-level suite, bulk manifest loop, Lean or Coq build. It reads
source44's two reviewed modules and checks both complete clause streams against
the delivered `.bits` artifacts. No recovered input is rewritten.

An already recovered source44 copy can be supplied explicitly:

```sh
quotient_scratch=$(mktemp -d)
uv run --no-project python SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/reproduce_155.py --prepare-only --output "$quotient_scratch"
uv run --no-project python Computability/BusyBeaver/Research/ZFC/finite_quotient_frontend.py --package "$quotient_scratch/44/zfc_finite_closure"
```

`--run-stage K --theory fc15|fc16` requests an unrestricted additional stage
decision. There is no fuel parameter. Large stages can be impractical; the
default tests decide only the actual native stages k=0,1, check explicit native
k=2 witnesses, and exhaust small satisfiable/unsatisfiable controls.

## Exact checker interface

Keep the delivered total radix16/Cantor term codec and its nine retained
functions V,C,N,A,Q,W,Y,Z,H. For k=0,1,... put B=2^k and D={0,...,B-1}.
Every decoded child is smaller than its parent, so D is subterm-closed without
a collected term set. The seven padded unary functions receive no congruence
obligations, exactly as in the source's retained-language reduct.

One candidate integer W has kB+3B² bits. Its low kB bits contain B consecutive
k-bit class labels pi(i); the remaining bits contain three predicate tables
on label pairs. Explicitly,

```text
label(i) = (W >> (k*i)) & (B-1)
Eq(a,b)  = (label(a) == label(b))
P_p(a,b) = bit(W, kB + p + 3*(B*label(a) + label(b)))   (p=0,1,2).
```

For k=0 the sole label is0. No canonical-partition or representative-idempotence
test is needed. All labelings, including noninjective ones, are enumerated.
Packing labels and tables into one word is a bijection with the two finite
fields; there is one candidate counter, with no inner counter to reset.

`Frontend.prepare_stage(k,theory)` produces the native finite constraints.
It evaluates each exact native template under every variable assignment in D;
it keeps an instance only when every endpoint term code is in D. Its actual
literal interface is `(sign,predicate,leftTerm,rightTerm)`. It constructs no
numeric atom code and performs no atom-level Cantor pair/unpair roundtrip.
Cantor operations remain necessary for ground terms and their children.

`Frontend.valid(stage,W)` checks two conditions:

1. For each pair of positive codes a,b<B with the same retained-function tag,
   if corresponding arguments have equal labels, their output labels agree.
   The maximum arity is three. Padded tags9..15 are skipped.
2. Every retained native ground clause has a true literal under the label/table
   interpretation above. Negative equality literals compare labels too.

Native equality is thus handled by equivalence classes rather than syntactic
equality of term codes. Predicate congruence follows from class-indexed lookup;
retained-function congruence remains an indispensable explicit check.

`Frontend.decide(stage)` enumerates exactly
`range(2**(k*B + 3*B*B))`, returning SAT at a verified witness and UNSAT only
after the whole range is exhausted. `Frontend.stage_exists(k,theory)` prepares
the actual stage and returns that exact Boolean decision. There is no SAT
oracle, timeout, fuel-based verdict or catch-all exception conversion. Host
memory, integer and other execution errors propagate. These finite loops have
the intended total mathematical interpretation with unbounded resources;
finite host capacity is not claimed sufficient for arbitrary k.

## Ordinary equivalence with the complete source theory

Let G_B contain the kept native ground instances, reflexivity/left-Euclidean
instances on D, retained-function congruence for application terms in D, and
predicate transport on argument quadruples from D. This is a finite ground
CNF; the Python decision engine does not construct its equality rows.

A valid W induces a valuation of all ground atoms on D. Label equality
satisfies the two equality laws. The function check gives each retained
function-congruence row. Class-indexed predicate lookup satisfies transport.
Native validation supplies the remaining clauses, hence SAT(G_B).

Conversely, a valuation satisfying G_B makes Eq an equivalence relation on D.
Label each i by the least code in its Eq-class. Predicate transport in both
directions makes each predicate constant on class pairs. Store those truth
values, filling unused label-pair positions arbitrarily. Function congruence
and the native clauses verify both checker conditions. This encodes a W in the
finite range. Therefore `stage_exists(k)` is equivalent, in ordinary mathematics,
to SAT(G_(2^k)), retaining all colliding substitutions and equality classes.

The G_B are nested. Every ground instance of all29/30 equality-completed source
templates occurs in some G_B, or follows from its equivalence/congruence rows.
An application's code can greatly exceed its arguments, but some B eventually
exceeds every endpoint. Conversely each G_B contains only source instances
and their consequences. Propositional compactness therefore gives:

```text
all finite stages have a certificate
    iff all ground instances of the complete source theory are satisfiable.
```

Apply source44's padded term-algebra/reduct/quotient construction and ordinary
calibration to get the same unbounded nonhalting/consistency criterion. Padding
is forgotten before the global quotient, so no congruence for padding functions
is inferred. A finite certificate is not a model of the whole closure theory.
This unbounded argument is ordinary mathematics, not a conclusion from tests
or a formal theorem about CPython.

## Concrete cost baseline and limitations

The submitted equality-template enumeration with B substitution values has
exactly B+B³+8B⁴+4B⁶ instances:14,394,18,500 at B=1,2,4. The quotient check
instead visits at most B(B-1)/2 pairs, applying at most three label comparisons
per matching retained tag. Reflexivity, left Euclidean law and predicate
transport have no runtime clause instances in this representation.

| Theory | Stored native clauses | Original completed clauses | Native bits | Completed bits |
|---|---:|---:|---:|---:|
| FC15* |15 |29 |881 |1616 |
| FC16* |16 |30 |1088 |1823 |

Both remove735 stored bits and14 equality-template rows. They add label
extraction and a function-pair loop. The actual interface also avoids an
independent Eq truth table, canonical partition validation, sparse symbol
tables, DPLL/resolution controls and atom-code pairing. Ground-template
evaluation, term Cantor arithmetic, fixed arities, bit lookup, finite counters,
enumeration, initialization and the complete binary runtime still need pricing.
No part is assigned a TM state saving here.

The native templates have at most four local substitution variables; the
completed templates need six. The separate function check compares decoded
argument labels coordinate by coordinate, rather than instantiating a
six-variable congruence template. This gives a concrete smaller substitution
interface to price, although its eventual register allocation is not proved.

The stage schedules differ, so these are obligation counts rather than a
runtime comparison at equal B. Containing all native instances from delivered
stage0 first requires k=33 for FC15* and k=166 for FC16*. Their largest endpoint
codes are4,876,177,250 and
53,478,160,790,649,930,763,063,879,706,299,886,265,361,113,390,229.
Even k=2 has56 candidate bits, allowing over72 quadrillion candidates; k=3
has216 bits. A SAT witness may occur early, but full exhaustion cannot be
assumed practical. The cutoff representation can be catastrophically slower
than sparse DPLL. Its possible control savings remain unmeasured.

## Finite evidence

The saved result records:

- Both complete source clause streams reproduced exactly, plus all kept
  native instances at k=0,1,2 independently matched against the delivered
  signed-atom instantiator.
- Four actual native k=0/1 decisions return SAT at W=0. Native k=2 witnesses
  W=2,097,728 validate for both theories and expand to satisfying valuations
  of the explicit local equality CNFs; full k=2 enumeration was not run.
- 300 sampled partitions agree with explicit equivalence/congruence clauses.
  The latter function rows use full decoded trees independently of the checker's
  arithmetic tag matcher. All 4,104 congruent relational valuations on a
  two-element carrier are recovered.
- Five controls include an empty clause, contradictory equality, equality
  transport of a predicate, and a nontrivial disequality witness. Each of the
  three UNSAT cases exhausts all 16,384 candidates. Seven malformed inputs are
  rejected, and an injected memory failure propagates without becoming UNSAT.
- A required retained-function control rejects pi(0)=pi(1)=0, pi(17)=1:
  codes1 and17 are V(d,d),V(term1,d). A padding control permits unequal labels
  for codes10 and26, padding9(d),padding9(term1), with equal argument labels.

The next concrete compiler target is the pure `(k,W)` validator followed by
its single-counter stage loop. The implementation and ordinary proof now
specify that target; a complete costed backend remains separate work.
