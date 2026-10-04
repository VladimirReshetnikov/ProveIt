# Literal five-witness endpoint alternatives

## Result

The new sources implement the same endpoint relation as the audited
three-witness selector, using **five positive witnesses and five equations**.
The free-fixed-numeral source has **42 operations = 37M+5A**. The strict
literal-1/3 source has **101 operations = 94M+7A**. Their maximum expanded
endpoint-equation degree is **576001**, excluding fixed numeral ports.

All prior and folded sources, audits, notes, and receipts remain unchanged.
Only new files were added. The frozen 174-operation interface was untouched.

## Literal sources and semantics

New JSON DAGs:

- `endpoint_five_witness_fixed_numerals_source.json`
- `endpoint_five_witness_paid_numerals_source.json`

Both use existing ports W, FinalHead, FinalSignPlus and exactly the positive
witnesses U,V,Uq,Vq,BoundCol. Gate outputs are arithmetic expressions, **not
additional quantified variables**. Equalities themselves are free in this
component operation ledger. Combining them into one polynomial is outside
this component.

The fixed source has three prescribed numeral ports:

    K=3^481225262775,
    C=3^481238074400-1,
    D=3^481238074400-2=C-1.

These are exact fixed values, never freely guessed or existential inputs.
The paid source constructs their values from literal 3 with a shared
57-multiplication chain for 3^481225262775 and 3^481238074400, then computes
C and D with two subtractions. Its only literal ports are 1 and 3.

Let A=W^576000 and T=W^29948, both paid by the same shared 32M chain used
in the predecessors. The ten remaining operations are

    HorizontalLeft  = U+D                  [A]
    HorizontalRight = C*Uq                 [M]
    AMinusOne       = A-1                  [A]
    VMinusOne       = V-1                  [A]
    VerticalLeft    = VMinusOne+AMinusOne   [A]
    VerticalRight   = AMinusOne*Vq         [M]
    Acol            = K*U                  [M]
    ColumnBound     = Acol+BoundCol        [A]
    AT              = Acol*T               [M]
    EndpointHead    = AT*V                 [M]

The five asserted equalities are

    HorizontalLeft=HorizontalRight,
    VerticalLeft=VerticalRight,
    ColumnBound=W,
    EndpointHead=FinalHead,
    FinalSignPlus=1.

The vertical assertion is exactly V+A-2=(A-1)Vq. Its evaluation above
needs no free numeral 2 and shares A-1.

Thus the ledgers are

    fixed model: 32M + (5M+5A) = 37M+5A = 42;
    paid model: (57M+2A) + 32M + (5M+5A) = 94M+7A = 101.

## Equivalence, positivity, and zero quotients

The first two assertions force

    U=C*(Uq-1)+1,
    V=(A-1)*(Vq-1)+1.

Since Uq,Vq are positive, C>0, and A>1 under the 174 relation, both right
sides are at least 1. Zero underlying horizontal or vertical quotients
are permitted: Uq=1 gives U=1, and Vq=1 gives V=1.

There is a bijection between the positive witness solutions of the
three-witness and five-witness forms. Given HxPlus,HyPlus,BoundCol, set

    Uq=HxPlus,
    Vq=HyPlus,
    U=C*(HxPlus-1)+1,
    V=(A-1)*(HyPlus-1)+1,
    BoundCol unchanged.

Conversely, read HxPlus=Uq and HyPlus=Vq; the first two equations force the
same U,V. The three remaining equations are then exactly the earlier
selector equations. Hence their projection onto the existing 174 ports
has the same zero set, with no extra accepting endpoints.

In particular, the earlier soundness proof applies: positivity of the
head factors forces U,V to be powers of 3; the two divisor identities
recover the coordinate residues; BoundCol>0 prevents row carry; the 174
FinalHead<Q bound supplies the row bound; the selected site is white,
and FinalSignPlus=1 means east. No new geometry or divisor assumptions
are introduced.

## Exact endpoint-equation degrees

After expanding arithmetic expressions, with all prescribed numeral
ports treated as fixed coefficients, the five residual polynomials have
total degrees

    1, 576001, 1, 29950, 1.

The vertical residual has its highest-degree term W^576000*Vq. The head
residual has its highest-degree term K*U*W^29948*V. Thus the maximum is
576001, versus 605950 for the three-witness head residual. This is an
endpoint-only degree comparison. It makes no claim about the full 174
component or any final polynomial combination.

## Reproducible checks

New audit and receipt:

- `audit_five_witness_endpoint.py`
- `five_witness_endpoint_audit_receipt.json`

Run with bytecode writing disabled:

    PYTHONDONTWRITEBYTECODE=1 python -B audit_five_witness_endpoint.py

The audit checks all source inputs and references, exact shared-chain
exponents, acyclicity, opcode ledgers, five asserted equalities, and five
positive witnesses. It separately expands the outer source into sparse
formal polynomials and compares them to the five displayed equations,
then computes the degrees while excluding fixed numeral symbols.
It also checks 192 small witness-correspondence cases, including both
zero-quotient boundaries, and verifies hashes of every preserved prior
and folded artifact.

Only newly authored local audit helpers were executed. No upstream code
was run, and no giant power was materialized. This remains an endpoint
component; raw-input compilation, dilation/background, and final
single-polynomial construction remain separate.
