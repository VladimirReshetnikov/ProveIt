# Folded three-witness endpoint: independent audit addendum

## Verdict

**Pass.** The proposed horizontal positive-quotient fold reduces the
free-fixed-numeral endpoint source from 43 to **42 operations = 37M+5A**,
while preserving exactly the same three supplied positive witnesses and
exactly the same pointwise zero set. In the strict literal-1/3 source,
paying construction of the additional fixed value cancels this one-operation
saving: its cost remains **101 operations = 94M+7A**.

All predecessor files, including the 43-operation source and original
101-operation paid source, are preserved byte-for-byte. The frozen
174-operation interface and its surrounding project were not modified.

## Exact folded construction and positivity

Use the three **prescribed fixed numeral ports**

    K = 3^481225262775,
    C = 3^481238074400 - 1,
    D = 3^481238074400 - 2 = C-1.

These are fixed integer values, never freely guessed inputs or new
existential parameters. In the free-numeral model, the identity D=C-1 is
true by the specification of the numeral ports and needs no arithmetic
gate. In the paid model it is explicitly computed with one subtraction.

Retain the positive witnesses HxPlus, HyPlus, BoundCol. Replace only

    Hx = HxPlus-1; CxHx = C*Hx; U = 1+CxHx

by

    CHxPlus = C*HxPlus;
    U = CHxPlus-D.

Because HxPlus>=1 and D=C-1,

    U = C*HxPlus-(C-1) = C*(HxPlus-1)+1 >= 1.

Thus subtraction has not introduced a possibly negative or zero factor.
U=1 occurs exactly at HxPlus=1, corresponding to the valid zero horizontal
quotient. No new positivity slack or supplied U witness is required.

The vertical part stays

    Hy = HyPlus-1,
    V = 1+(W^576000-1)*Hy.

It is positive by the same argument as in the predecessor. Keep T=W^29948,
Acol=K*U, and the assertions

    Acol+BoundCol=W,
    FinalHead=(Acol*T)*V,
    FinalSignPlus=1.

For every assignment of the existing ports and the same three witnesses,
the old and new U agree identically. Therefore all three asserted
polynomials agree identically, not merely after projecting existential
witnesses. Soundness, necessity, canonical-coordinate uniqueness, the
strict row-carry bound, white-square/east-heading parity, and both zero
quotient cases are inherited without change from ENDPOINT_AUDIT.md.

## Exact ledgers

The existing joint W-chain still has 19 squarings and 9+4 product gates,
so it costs 32M. The folded non-power source is:

| Gate | Class |
|---|---:|
| Hy=HyPlus-1 | A |
| CHxPlus=C*HxPlus | M |
| U=CHxPlus-D | A |
| VPowerMinusOne=WToV-1 | A |
| VIncrement=VPowerMinusOne*Hy | M |
| V=1+VIncrement | A |
| Acol=K*U | M |
| ColumnBound=Acol+BoundCol | A |
| AT=Acol*T | M |
| EndpointHead=AT*V | M |

This is 5M+5A=10 non-power operations. The fixed-numeral source therefore
has 37M+5A=42 operations.

The fully paid source still uses the predecessor's shared 57M chain for
3^x0 and 3^u. It explicitly computes C=3^u-1 and then D=C-1, costing 2A.
Its complete endpoint ledger is

    numeral construction: 57M+2A = 59,
    variable W powers:    32M+0A = 32,
    folded non-power:      5M+5A = 10,
    total:                94M+7A = 101.

Only literal 1 and literal 3 are source constants in this strict model.
The 42-operation source is a genuine improvement in the free-numeral
model; it is not a one-operation strict-model improvement.

## Parent's five-witness formulation

The alternative uses five positive witnesses U,V,Uq,Vq,BoundCol and, with
A=W^v, asserts

    U+D=C*Uq,
    V+A-2=(A-1)*Vq,
    K*U+BoundCol=W,
    FinalHead=K*U*W^y0*V,
    FinalSignPlus=1.

It has the same endpoint relation after existential projection. The exact
witness correspondence is

    Uq=HxPlus,
    Vq=HyPlus,
    U=C*(HxPlus-1)+1,
    V=(A-1)*(HyPlus-1)+1,
    BoundCol unchanged.

The first two equalities force these values in the reverse direction.
In particular, Uq=1 or Vq=1 correctly handles a zero underlying quotient.
No unbounded extra solutions arise from the extra witnesses.

Its ten non-power gates can be counted as 2 for the horizontal equation,
4 for the vertical equation, 1 for shared K*U, 1 for the column sum, and
2 for the final product: 5M+5A. The vertical equation can use literal 1
only by writing (V-1)+(A-1)=(A-1)*Vq, reusing A-1. Thus its arithmetic
counts can also be 42 with free K,C,D, or 101 with the same fully paid
constant chain. The tradeoff is five witnesses and five equations instead
of three witnesses and three equations.

There is an endpoint-only degree advantage after expanding arithmetic
gates and treating the numeral ports as fixed constants. For the
three-witness form, the head polynomial has total degree

    v+y0+2 = 605950.

For the five-witness form, the head polynomial has degree y0+2=29950,
while the vertical relation has degree v+1=576001. Hence its maximum
expanded endpoint-polynomial degree is 576001. This is not a claim about
the degree of the 174 component, any final polynomial combination, or a
universal certificate.

## New artifacts and independent checks

- `endpoint_folded_fixed_numerals_source.json`: explicit 42-gate DAG
- `endpoint_folded_paid_numerals_source.json`: explicit 101-gate DAG
- `audit_folded_endpoint.py`: new independent folded audit
- `folded_endpoint_audit_receipt.json`: counts, exponents, polynomial checks,
  and predecessor/new-file hashes

The new audit checks acyclicity, input availability, all power exponents,
and exact ledgers; then independently expands the outer arithmetic into
sparse integer polynomials, substituting the prescribed D=C-1, and checks
that U,V,ColumnBound,EndpointHead equal the predecessor polynomials exactly.
This avoids evaluating any giant numeral. Eighty small arithmetic cases
also check horizontal positivity and the zero-quotient boundary directly.
The original 17,280-endpoint regression remains available and unchanged.

Only newly authored local audit code was run. No upstream code or giant
fixed powers were executed. These are endpoint-component results only;
raw-input compilation, dilation/background, and final polynomial
combination remain separate obligations.
