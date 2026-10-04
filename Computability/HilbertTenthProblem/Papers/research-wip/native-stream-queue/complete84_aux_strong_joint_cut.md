# A five-gate bound for the joint auxiliary and scaled strong cut

The joint factor below needs exactly **five binary arithmetic gates** when
its four paid inputs are treated as algebraically independent. The displayed
schedule attains that bound with 2M+3A. The [helper](complete84_aux_strong_joint_cut.py)
and [receipt](complete84_aux_strong_joint_cut.json) also save an actual complete
regrouping of the current universal polynomial: **84=47M+37A**, 18 positive
witnesses, ordinary input and exact degree187. Its entire polynomial is unchanged.

This is a local negative result, not a new universal upper bound or an
84-gate lower bound. It does not cover using extra registers, modifying any
of the four producers, exploiting their source-specific relations, or
changing supplied coordinates. It complements the earlier
[single-producer scout](complete84_local_producer_scout.md) with a joint
factor result in a different, explicitly restricted model.

## 1. The actual paid ports and full regrouping

In [complete84](complete84_scaled_strong_output.md), let

    A0 = scaled_f_square = Delta*f²,
    Q  = R16 = (i*Delta*c²)²,
    V0 = H2 = V²,
    Y0 = aux_y2 = y_aux².

Here the source register `A` is Delta; it is not the formal cut variable A0.
All four producers remain in the complete saved source, including the
entire paid quotient V=c(Tf−1)−R*f². No square or variable coefficient is
silently made a free supplied coordinate. The two factors are

    Ns = A0−Q,
    Na = Q*(V0−Y0)+Y0.

Their product P has the five-gate schedule

    norm_strong    = A0−Q
    aux_square_gap = V0−Y0
    L17            = Q*aux_square_gap
    norm_aux       = L17+Y0
    joint_aux_strong = norm_aux*norm_strong.                 (1)

The first four rows are literal parent producers. The last multiplication
is obtained by reassociating the already paid complete finalizer. The
helper copies all77 parent producer rows unchanged and replaces only the
seven original finalizer rows by

    joint_aux_strong = norm_aux*norm_strong
    norm_pair    = norm_first*norm_main
    norm_triple  = norm_pair*norm_input
    norm_product = norm_triple*norm_index
    all_units    = norm_product*norm_transport
    seven_units  = all_units*joint_aux_strong
    polynomial   = seven_units−A.

These still cost6M+1A. Every gate and all25 supplied ports are live.
`norm_aux` and `norm_strong` have only the new joint multiplication as
consumer; its output is used by `seven_units`. The complete ledger is

| Part | M | A | Total |
|---|---:|---:|---:|
| Unchanged factor producers |41|36|77|
| Regrouped complete finalizer |6|1|7|
| Complete polynomial |47|37|84|

Associativity and commutativity give the identical complete polynomial
over every commutative ring, with no norm-one equation or positivity
assumption. Thus all zero tuples agree, including signed tuples. On the
inherited valid fixed-program slices, this preserves the ordinary-input
universality theorem with the identical witness interface and compiler
numeral recipe. Arbitrary diagnostic numeral assignments are not being
promoted to valid programs.

The parent exact factor degrees are22,18,32,60,7,2,46. Multiplication in the
polynomial integral domain makes the new joint factor's exact degree106,
and the regrouped degrees are22,18,32,7,2,106. The entire polynomial and
its uniform exact degree187 are inherited unchanged; no new degree
expansion or new degree theorem is needed.

## 2. The precise generic gate model

Let k be any field of characteristic zero. The only nonscalar inputs in
this section are four independent indeterminates A0,Q,V0,Y0. All elements
of k may be used as scalar constants. A gate performs one binary addition,
subtraction or multiplication on inputs or earlier registers. Registers
may be reused; multiplication by a constant is still a multiplication
gate. No division, comparisons, fused operations or precomputed extra
polynomials are supplied.

The target is the polynomial

    P=(A0−Q)*(Q*(V0−Y0)+Y0)
     =A0*Q*V0−A0*Q*Y0+A0*Y0−Q²*V0+Q²*Y0−Q*Y0.        (2)

It has degree3 and cubic homogeneous part

    P3=Q*(A0−Q)*(V0−Y0).                               (3)

The three linear factors in (3) are pairwise nonassociate. The last two
are distinct nonmonomial forms, neither proportional to an original input.
Equation(1) proves the five-gate upper bound. We exclude every circuit
with at most four gates next. This proof concerns formal polynomial
equality, not a finite sample of values or equality only on positive zeros.

## 3. Excluding the other operation budgets

At most one multiplication gives total degree at most2: before that gate
all registers are affine, and subsequent additions cannot increase degree.
This cannot produce(2).

With at most one addition or subtraction, all registers before that gate
are monomials, including scalars. If the gate produces a binomial B,
all later nonzero registers are a monomial times a nonnegative integral
power of B. Their Newton support lies on an affine line, even if some
coefficients cancel; if the sole addition instead produces a monomial or
zero, the claim is stronger. The support of(2) is not collinear: the
exponents of A0*Q*V0, A0*Q*Y0 and A0*Y0 have independent differences,
with determinant−1 on their Q,V0 coordinates. Hence one addition cannot
suffice, regardless of how the remaining multiplication gates are arranged.

The only remaining possible budget of at most four gates is exactly
two multiplications and two additions/subtractions.

## 4. Two-multiplication normal form

Call the first multiplication's output R1 and the second's output R2.
Before the first multiplication every computed register is affine. A
degree3 output requires R1 to have genuine degree2. Before R2, every
register of degree2 has a quadratic leading part proportional to the
leading part of R1: additions can only combine copies of that one
quadratic producer with affine registers. An addition may change its
lower-degree terms, or cancel that quadratic part entirely, but cannot
replace its nonzero quadratic leader by a different one.

Both operands of R2 cannot be genuinely quadratic. If they were, their
leading forms would be nonzero scalar multiples of the same quadratic
leader, so R2 would have degree4. No earlier register has degree4. Later
additions that use R2 would either retain its quartic leader or remove its
entire contribution; the latter leaves degree at most2. There is no
separate quartic producer with which to cancel just the top degree and
leave a cubic. Thus a cubic output forces R2 to multiply a genuinely
quadratic register by an affine register of degree1.

Consequently the cubic leader of the output is, up to a nonzero scalar,
the product of the linear leaders of the two operands of R1 and the
linear leader of the affine operand of R2. Later additions cannot change
this nonzero cubic factorization because there is only one cubic
producer. Unique factorization and(3) force these three leaders to be
proportional, in some order, to Q, A0−Q and V0−Y0.

**Why a nonlinear addition cannot supply the two needed linear factors.**
Neither A0−Q nor V0−Y0 is initially available. A new affine register with
one of these leaders needs an addition: neither of the two genuinely
degree-raising multiplication gates can produce an affine register.
One affine addition has one output and cannot supply both nonproportional
leaders. An addition whose result is genuinely quadratic merely retains
the first product's leader, so it cannot supply a missing linear factor
or an affine operand of R2. If an addition cancels that quadratic part,
its affine output can supply at most one new leader; producing such an
affine output does not also make its operands' canceled quadratic leader
into an available second affine output.

It follows that the two distinct required affine leaders consume both
addition gates. Neither gate is available for a nonlinear correction or
an addition after the final cubic product. More explicitly, a quadratic
cancellation cannot rescue the budget: canceling R1 against itself gives
zero; obtaining a nonzero affine residue by canceling R1 against a
quadratic register with different lower terms first requires an earlier
addition to make that different register. Those two additions then yield
at most one new affine leader, leaving the other missing.

Therefore both additions in a successful four-gate circuit would have
to act within the affine part of the circuit. The complete output, not
just its cubic leader, would be a scalar times a product of three affine
linear polynomials.

That is impossible. In k[Q,Y0][V0], the second factor

    Q*V0+(1−Q)*Y0                                    (4)

is primitive, because gcd(Q,(1−Q)*Y0)=1. It is a nonconstant linear
polynomial over the fraction field k(Q,Y0), hence irreducible there;
Gauss's lemma makes it irreducible in k[Q,V0,Y0], and adjoining A0
preserves irreducibility. Thus(2) has an irreducible quadratic factor
and cannot split into three affine linear factors. This excludes2M+2A
and completes the exact five-gate lower bound.

The proof permits arbitrary scalar constants and reuse, and covers
cancellation. It does not require that an optimal five-gate circuit
have the particular operation split2M+3A; that is simply the split of
the displayed optimal schedule.

## 5. Executable evidence and its limits

The new standard-library helper authenticates the three complete84 files
and the three single-producer scout files. All six are read as inert
bytes; only the complete84 JSON is parsed for arithmetic construction.
No predecessor source, archived Python, old builder or historical suite
executes. These are immediate dependency pins, not a fresh replay of
the parent's entire proof ancestry.

The helper independently checks literal preservation of all77 producers,
the complete old and new finalizers, topological closure, all paid gates,
all free ports and the private consumers of the joint block. Exact sparse
integer coefficients prove(2), the cubic leader(3), and the complete
seven-factor-minus-Delta identity at the unchanged producer ports.
The literal producer checks lift this last identity to the full circuit.
The six-term support and the stated nonzero minor are also checked.

The four-port lower bound and irreducibility argument are the proof in
Sections2–4, not a claim that the helper exhaustively enumerates circuits.
The numerical supplement has32 whole-source assignments, half signed
integers and half signed rationals, for5,376 row evaluations and2,464
retained-row comparisons. It materializes no complete native Pell zero
and needs no such witness to establish the all-value identities.

| Dependency | SHA256 |
|---|---|
| complete84_scaled_strong_output.py | `8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737` |
| complete84_scaled_strong_output.json | `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf` |
| complete84_scaled_strong_output.md | `01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade` |
| complete84_local_producer_scout.py | `472f6d1afba2cbc138d7be94dba1004031ac92b9af458ed1a3099d4393736194` |
| complete84_local_producer_scout.json | `a03d2a2704a937223836e12fd38c9d8516e92a845aeed70377cdacac58b7d4ca` |
| complete84_local_producer_scout.md | `7cfa58529ec02a6cf3df475e3d0feda6b4e5f4ad6b6c622e810907371b0aecad` |

From any working directory:

```sh
joint_wip=/absolute/path/native-stream-queue
python3 "$joint_wip/complete84_aux_strong_joint_cut.py" \
  --root "$joint_wip" --expect "$joint_wip/complete84_aux_strong_joint_cut.json"
python3 -O "$joint_wip/complete84_aux_strong_joint_cut.py" \
  --root "$joint_wip" --expect "$joint_wip/complete84_aux_strong_joint_cut.json"
```

`--output FILE` writes the deterministic receipt instead. All required
checks use explicit exceptions. JSON parsing rejects duplicate keys and
nonfinite values, and exact receipt comparison distinguishes numeric
types recursively. This is a bounded source/receipt CLI, not a general
compiler API. Writer and fresh normal/optimized exact replays from `/`
pass. No repository or frozen predecessor file was edited.
