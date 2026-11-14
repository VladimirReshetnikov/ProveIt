# Direct arithmetic negation

## Exact native coding

The inherited native Cantor function is

    P(x,y) = tri(x+y)+y,    tri(k)=k(k+1)/2.

Implication is I(x,y)=4P(x,y), false is the fixed code1, and negation is
N(x)=I(x,1)=4P(x,1). The source's old negations push code1 on the encoded
formula stack and then invoke generic implication. Each costs47 primitive
occurrences. Four are literal m218 subtrees; two further occurrences cross
an association boundary but have the exact same primitive CFG.

The old occurrences are exactly [1070,1117), [2595,2642), [3555,3602), and
[3685,3732). All are after the startup bridge at source ordinal136.
The two additional intervals are [994,1041) and [2519,2566). These also
follow the startup bridge. They are closed sequences of literal-one push
and generic implication, even though they are not individual old subtrees.

## Retained arithmetic components

The counter registers used here are T=register1, X=register6, Y=register7.
All other registers, including encoded stack register2, are preserved.
The retained ProgLibPerm lemmas give, for all natural register values:

- m216: X:=X+T; T:=0 (3 source primitives).
- m162: Y:=Y+P(X,T); X:=T:=0 (10 source primitives).
- m117: T:=T+4Y; Y:=0 (6 source primitives).

In every constructor call X=Y=0. The proofs below are identities over all
natural values, not tests on bounded counter contents.

## Three replacement macros

The 20-primitive variant is

    m216; CI1; m162; m117.

After its first two commands X is the old T and T=1. Pairing and
quadrupling therefore leave T=4P(Told,1), X=Y=0, as required.

The 18-primitive variant is

    CI7; CI7; m162; m117.

It leaves T=4(P(0,Told)+2). The triangular-number identity

    P(n,1)=tri(n+1)+1=tri(n)+n+2=P(0,n)+2

proves exact equality with the old negation. This is the shortest of the
three constructed primitive words.

The 24-primitive variant is

    m162; m117; CI1; CI1; CI1; CI1; CI1; CI1; CI1; CI1.

It computes 4P(0,Told)+8, hence the same negation. The longer word is
included because its eight increments can share the existing four-increment
source subtree. Source primitive count and physical state count are
separate objectives.

All three preserve the entire encoded stack exactly; there is no list-shape
precondition beyond the inherited clean scratch registers. The constructor
proof is stronger than the original stack simulation contract.

## Source artifacts and audits

`build_direct_negation.py` enumerates all five binary associations of the
four closed components of each macro. It replaces all four occurrences
uniformly in the original U208 source. For every candidate it checks:

1. The first137 source rows are literally unchanged.
2. Independent arithmetic and interval-based primitive CFG resolvers agree.
3. Every primitive operation and successor outside the four replaced
   closed intervals agrees under the exact ordinal shift.
4. No external primitive edge enters the strict interior of an old macro.

The best candidates have198 distinct source nodes versus197 in the
baseline. `n18_0` and `n18_2` have3793 primitive occurrences (saving116),
maximum source depth41, and maximum zero run6. The n20 variants have3801
occurrences, and the n24 variants3817. These are source candidates; no
physical state saving is claimed by these metrics alone.

`finalize_negation_all6.py` additionally replaces all six occurrences by
closed-interval splicing. It verifies that all six old intervals have
exactly the inherited negation CFG, then checks every exterior effect and
successor under the six ordinal shifts. `n18_all6.sites.json` has3735
primitive occurrences, saving174, with198 DAG nodes, depth41 and maximum
zero run6. Its SHA256 is
`b897ed0c1c759484dc24c783db3a5422360dd8d5f8a7ffc16450e4ae14728003`.
It is byte-identical to the earlier screened `n18_all6_preview.sites.json`.

Because each replacement computes the *same native integer*, the logical
axiom family is completely unchanged. The new source's halting equivalence
with the old source follows by the usual closed-block simulation, and the
retained PA consistency calibration applies unchanged. The finite syntax
replacement and the displayed counter invariants are formalizable in PA.
There is no new kernel-checked proof claim.

## Related fixed-constant constructor arithmetic

The same components give stack-preserving unary operations:

| Desired result from T=x | Primitive word | Size |
| --- | --- | ---: |
| R(1,x) | CI6; m162; m117; CI1 |18|
| Q(1,x) | CI6; m162; m117; CI1; CI1 |19|
| R(0,x) | m162; m117; CI1 |17|
| Q(0,x) | m162; m117; CI1; CI1 |18|
| R(x,1) | N18; CI1 |19|
| R(x,0) | m216; m162; m117; CI1 |20|

These operations are used in additional fixed-role emitter experiments.
Their arithmetic correctness is exact, but their altered source grammar
has not yet improved the physical-state target.
