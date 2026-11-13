# Independent audit of removing literal-zero-source transport

This note audits the mathematical argument proposed during the present session.
It is a written proof review by another assistant instance, not a proof-assistant
formalization. It concerns the abstract native calculus. The separate Python
implementation still needs its arity-codec and certificate-correspondence proof.

## Verdict

The restriction is admissible: keep transport only when its source term is
syntactically different from the constant `0`. All original transport instances
can then be derived. The important new ingredient is a derivation of

    0 = t  |-  t = 0

without using literal-zero-source transport. The derivation uses only the
unchanged native numerical case rule, equation induction, iterator computation,
and transport at syntactically nonzero terms. Its numerical functions are fixed
scalar-iterator terms, so no predecessor, equality test, general logical
reconstruction, or hidden primitive-recursive evaluator is assumed.

The proof below also verifies full equality transitivity, atomic-formula
transport, and both Q/D binder steps. It avoids invoking the old binary formula
selector before full transport has been recovered.

## 1. Restricted calculus and safe elementary rules

Write `Tr+` for transport from `p=q, A(p)` to `A(q)` when the source term `p`
is not literally `0`. A variable, a successor, or any iterator expression is
an admissible source, even if its numerical value happens to be zero.

All other primitive rules are unchanged: hypotheses, the two computation
equations, QE, DE, case-DI, and literal-equation progress-DI. In particular:

* Contextual induction on literal equations follows from progress-DI with an
  unused witness coordinate, DE, and QE. This derivation needs no transport.
* Numerical cases for arbitrary native formulas follow from case-DI with an
  unused witness coordinate, DE, and QE. This also needs no transport.

Use `K(a) := I(0,a;u.0)`. Thus `K(a)=a` is a computation axiom and `K(a)` is
always syntactically nonzero.

### Reflexivity

From the computation `K(a)=a`, transport that same equation in the template
`v=a`, using source `K(a)`. The result is `a=a`. This works when `a` is zero.

### Symmetry at a nonzero source

If `p` is syntactically nonzero, `p=q` and reflexivity `p=p` yield `q=p` by
Tr+ in the template `v=p`. The target `q` may be zero.

### Numerical congruence at a nonzero source

From `p=q` with `p` syntactically nonzero, and reflexivity `H(p)=H(p)`,
transport only the second displayed occurrence through the numerical template
`H`. This gives `H(p)=H(q)`. Fixed occurrences of `p` on the other side are
parameters of the formula template, not substitution holes.

### Joining two nonzero terms with a common value

Suppose `p=r` and `q=r`, where `p,q` are syntactically nonzero; `r` need not be.
Numerical congruence gives `K(p)=K(r)` and `K(q)=K(r)`. Symmetry of the second
equation is allowed at source `K(q)`, yielding `K(r)=K(q)`. Transport at the
nonzero source `K(r)` gives `K(p)=K(q)`. Finally use the two computation
equations `K(p)=p` and `K(q)=q`, at their nonzero sources, to obtain `p=q`.

This lemma is essential when two computed expressions both equal zero. Merely
saying "by transitivity and symmetry" at that stage would hide the forbidden
zero-source step. The boxing proof above does not.

## 2. Fixed iterator terms

Let `1=S0`, `2=S1`, and define the selector

    C(n,a,b) := I(n,a;u.b)

with `u` unused. Its equations are `C(0,a,b)=a` and `C(Sn,a,b)=b`.

Define:

    Z(n) := C(n,1,0),
    N(n) := I(n,0;u.Z(u)),
    R(n) := I(n,0;u.C(u,1,2)),
    L(n) := N(R(n)).

Only the fixed values `N(0)=0`, `N(1)=1`, `N(2)=0` are needed. In particular,
the proof does not require a general theorem about parity. Also:

    Z(0)=1,       Z(Sn)=0,
    R(0)=0,       R(1)=1,       R(2)=2.

Every displayed finite computation can be proved by forwarding a computation
equation through a numerical template at the iterator on its left-hand side.
Those sources are all nonzero syntax. If a displayed equality must be reversed,
its computed iterator expression can be used as the nonzero source.

### The two-step plateau of R

Equation induction proves `R(S(Sn))=2`.

The base is the finite computation `R(2)=2`. In the step, the induction
hypothesis has source `R(S(Sz))`, which is nonzero syntax. The successor
computation expresses `R(S(S(Sz)))` as `C(R(S(Sz)),1,2)`. Transport the
induction hypothesis through that selector and compute `C(2,1,2)=2`.

Consequently:

    L(1)=1,       L(S(Sn))=0.

These follow by transporting the computed R values through N and then using
the fixed N values. Again, the R and N sources are nonzero syntax.

### The singleton-one identity

Numerical cases now prove

    L(Sn)=Z(n).

At zero, both sides equal `1`. At a successor, both sides equal `0`. Both
displayed sides are iterator expressions, so the common-value joining lemma
from Section 1 applies in the successor case. No unproved zero-source
transitivity is used.

## 3. Lifting 0=t through successor without Tr at zero

Fix a term `t`, and retain the assumption `0=t`. If `t` is literally zero,
the final symmetry result is already reflexivity, so consider the case where
`t` is syntactically nonzero.

Put `U_t(n):=I(n,t;u.Su)`. Apply equation induction to

    E(n): n=U_t(n).

All parameters in `t`, and the assumption `0=t`, remain fixed throughout.

### Base

The computation `U_t(0)=t` has nonzero source, so its permitted symmetry is
`t=U_t(0)`. Since `t` is nonzero syntax, use this as the Tr+ major on the
retained equation `0=t`. This gives `0=U_t(0)`, exactly the base instance.

### Step

The induction hypothesis is `z=U_t(z)`, with fresh variable `z`, hence an
allowed source. Transport it through successor to get
`Sz=S(U_t(z))`. The computation

    U_t(Sz)=S(U_t(z))

has nonzero source and a syntactically nonzero successor target; its symmetry
may therefore be used at the nonzero source `S(U_t(z))`. This yields
`Sz=U_t(Sz)`.

The induction consequently gives `1=U_t(1)`. Ordinary finite computation,
again using nonzero iterator sources, proves `U_t(1)=St`. Transport at
`U_t(1)` gives

    0=t  |-  1=St.

This is the first step that a proof based only on direct equality rewriting
would miss. It uses permitted equation induction rather than assuming
successor congruence at the forbidden source zero.

## 4. The unconditional reconstruction identity

Numerical cases prove

    n=C(Z(n),n,0).

For `n=0`, let `r=C(Z(0),0,0)`. First compute `r=0`, using `Z(0)=1` at
its nonzero source and then the selector computation at counter `1`.
Symmetrize `r=0` at the nonzero source `r` to obtain `0=r`.

For `n=Sz`, let `r=C(Z(Sz),Sz,0)`. The equation `Z(Sz)=0` has nonzero
source. It transforms the counter of r to zero, where the selector computes
to `Sz`. Thus `r=Sz`; symmetry at source r gives the required `Sz=r`.

The case variable is fresh and the theorem is unconditional. It can therefore
be instantiated at any fixed term `t`, including terms containing parameters
from an arbitrary retained context.

## 5. The new zero-source symmetry theorem

Under `0=t`, Section 3 gives `1=St`. Its source `1` is nonzero syntax.
Apply it to `L(1)=1` in the formula template `L(v)=1`, obtaining
`L(St)=1`. The unconditional singleton identity `L(St)=Z(t)` has nonzero
source `L(St)`, so transport yields

    Z(t)=1.

Use this equation at its nonzero source in the reconstruction identity:

    t=C(Z(t),t,0)  ==>  t=C(1,t,0).

The selector computation has source `C(1,t,0)`, also nonzero syntax, and gives
`t=0`. This proves

    0=t  |-  t=0

for every term t. The literal-zero t case was already covered by reflexivity.

No ordinary implication, conjunction, existential encoding, ex falso,
successor injectivity, predecessor function, or Boolean equality reflection
was needed in this derivation.

## 6. Full equality laws recovered without a circular use of Tr

### Unrestricted symmetry

If the source of an equation is nonzero syntax, Section 1 applies. If it is
zero, Section 5 applies. Thus every equation has its converse derivable.

### Unrestricted numerical congruence

For a given equation `p=q` and numerical template H:

* If p is not literally zero, use the primitive source-p congruence.
* If p=q=0 syntactically, use reflexivity.
* If p is zero and q is nonzero syntax, Section 5 gives `q=0`.
  Apply this permitted source-q transport to reflexivity `H(q)=H(q)`,
  changing only the first occurrence. The result is `H(0)=H(q)`.

This proves numerical congruence for every equality. It does not assume
formula transport at zero.

### Full equality transitivity

Given `p=q` and `q=r`, unrestricted numerical congruence gives
`K(p)=K(q)` and `K(q)=K(r)`. Their shared middle source `K(q)` is nonzero.
Primitive transport yields `K(p)=K(r)`. Unbox using the two computation
equations to obtain `p=r`.

### Atomic-formula transport

Suppose `p=q` and `f(p)=g(p)` are retained. Numerical congruence first boxes
the second equation:

    K(f(p))=K(g(p)).

Apply numerical congruence to `p=q` with the templates `K(f(v))` and
`K(g(v))`. This supplies

    K(f(p))=K(f(q)),       K(g(p))=K(g(q)).

Use these two equations as primitive transport majors, first on the left,
then on the right, of the boxed equation. Their source terms are nonzero
iterator syntax. The result is `K(f(q))=K(g(q))`. Two computation transports
unbox it to `f(q)=g(q)`.

This is full transport for literal-equation formula templates, including all
cases where an unboxed endpoint is literally zero.

## 7. Transport through Q and D

Induct externally on finite native formula syntax. The atomic case is
Section 6. The induction hypothesis is available in both directions because
unrestricted symmetry has already been proved. Rename all numerical binders
and fresh eigenparameters away from the terms p,q and the retained context.

### D binder

Assume `D_{x,y} B(p,x,y)`. Eliminate it at a fresh witness a, obtaining
`Q_y B(p,a,y)`. To introduce `D_{x,y}B(q,x,y)`, use witness a and case-DI.
Its local base assumption is `B(q,a,0)`. The reverse induction hypothesis
turns this into `B(p,a,0)`. QE supplies `B(p,a,Sz)` at the required fresh z;
the forward induction hypothesis supplies `B(q,a,Sz)`. Close case-DI and DE.

No progress rule is applied to a compound formula in this argument.

### Q binder

Assume `Q_y B(p,y)`. Case-DI with an unused existential coordinate introduces
`D_{u,y} B(q,y)` as follows: from its local base `B(q,0)`, the reverse
induction hypothesis gives `B(p,0)`, the retained Q major supplies
`B(p,Sz)`, and the forward induction hypothesis gives `B(q,Sz)`.
Eliminate the resulting D. Its opened Q resource is exactly `Q_y B(q,y)`
because u is unused, so a hypothesis step closes the desired result.

Thus every native formula template admits transport at every source. Every
old derivation can be translated by replacing its forbidden zero-source
transport nodes with these finite constructions. All other rules are copied.
The reverse proof translation is immediate because Tr+ is a restriction of
the original transport rule. Consequently the complete native consequence
relations agree, including open retained contexts, not just closed equations.

## 8. Audit of certified-zero computation normalization

The existing producer at
`baseline/Research/certified_zero/tests/producer.py`, function
`expand_computation`, replaces a literal-zero initializer or a literal-zero
successor predecessor by the nonempty term

    C_* := I(2,1;u.0).

Its equation `C_*=0` is a direct successor computation: its predecessor is
the truthy term `1`, its initializer is the truthy term `1`, and the update
is constant zero. The normalization uses exactly one transport with major
`C_*=0`. Its source is the nonempty iterator term C_*.

The modified computation leaf has C_* in each otherwise disallowed packet
position, so it is directly checkable. The same transport replaces the chosen
initializer/predecessor occurrences simultaneously, without changing passive
zero occurrences in the update. Therefore this existing normalization is
already a proof in the restricted calculus. It does not need the newly
derived zero-source transport theorem and introduces no circularity into the
implementation of the computation axioms used above.

## 9. Implementation and evidence boundary

The conditional source matcher

    m == ([s,u] if s else [t]*3)

implements Tr+ on canonical old-codec numerical syntax: zero is falsy, and
variables, successors, and iterators are truthy. Its falsy-source branch is
the unchanged Q elimination interface. The soundness of accepted noncanonical
raw aliases still belongs to the codec/instruction invariant; the mathematical
proof does not replace that task.

As an initial compatibility check, the three source-dispatch profiles were
run on the previously emitted 15 named local/global cases. They preserved
42 of 45 old raw-certificate outcomes; the three failures were the same
`contextual_induction_seed_congruence` certificate, once in each profile.
It contains an actual source-zero transport and needs the new proof
normalizer. This is expected, since preservation of the theorem relation
does not mean preservation of every old byte stream.

The universal proof above, not those finite executions, is the reason the
restriction preserves the theory. A complete zero-symmetry/transport
certificate and a proof-tree normalizer are particularly valuable further
implementation checks.

## 10. Review of the final mathematical module

I subsequently read `work_logic/zero_source_admissibility.tex` in full. Its
argument is valid. It improves the singleton construction above by first
proving `H(v)=S K(v)` with numerical cases, where its local notation is
`H(v)=C(v,1,2)` and `K(v)=C(v,0,1)`. Consequently `R(Sv)` is explicitly a
successor and `R(SSv)=2` follows directly, without the extra equation
induction used in this independent reconstruction.

That module's `K` denotes this positive-indicator term; the `K` in Sections
1 and 6 of this note denotes the I0 boxing term. These are separate local
notations, not conflicting definitions in one calculus.

The final module explicitly avoids unrestricted proof substitution until
full transport is recovered. Its common-zero joining proof, fixed-parameter
equation induction, unconditional filter case proof, full transitivity,
atomic transport, and Q/D binder cases all respect the restricted source
condition. I found no unproved zero-source transport, hidden use of the
binary formula selector, implicit successor injectivity, changed passive
parameter during induction, or circular computation-normalization step.
