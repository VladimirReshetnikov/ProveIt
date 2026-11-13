# Current2011 adaptive graph: 13 positive inputs, 88 operations, degree 30

The [literal graph](graph.json) is obtained from the exact current-port
[13/87/51 adaptive factor graph](../adaptive-first-root-factor87/README.md)
by replacing its four-factor product finalizer with a sum of four squares.
It has the **same zeros at every integer valuation**, with the same
coordinates and arbitrary integer port values. For the actual current2011
tuple it uses thirteen strictly positive inputs, 88 live integer-leaf
operations, and has exact degree 30. This is an external mathematical
result with finite source/degree evidence, not a new checked Lean graph
client or an internal iPRA proof.

The current tuple consists of the four complete fixed integers associated
with `CurrentWindowCarry2011.ports`; the fourth is `highPort+beta` once.
The checker authenticates their complete raw and compressed payloads.
This construction is distinct from the similar
[compact44 88/30 graph](../ordinary13-four-square88-30/README.md); it does
not identify the two different fixed tuples or their graphs.

## Full zero equivalence

The parent 87 graph uses the factors

```
F0=1+A0,  F1=1+A1,  Fs=1+g72,
parent = F0*F1*Fa*Fs−1.
```

The child keeps the full first 80 live rows and uses

```
child = A0²+A1²+(Fa−1)²+g72².
```

For **any integer inputs and integer ports**, none of `F0,F1,Fa,Fs` can be
−1 modulo 4. Write `qm=beta*J`, `q=1+qm`, `M=q³*qm`,
`Delta=a²+4a+3`, and `Q=Delta*(f²−1)`:

1. `M` is even because one of q and q−1 is even, so
   `F0=1+Z²−M²*(1+ell*(ell+k))` is 1 or 2 modulo 4.
2. Delta is 0 or 3 modulo 4, hence `1+Delta*c²` is 0 or 1 modulo 4.
   Thus `F1=1+Dstar²−U²*(1+Delta*c²)` is 0, 1 or 2 modulo 4.
3. Both Delta and `f²−1` are 0 or 3 modulo 4, so Q is 0 or 1. Therefore
   `Fa=y²−Q*(y²−V²)` is congruent to either y² or V², hence is 0 or 1.
4. `Fs=1+I²−Q` is 0, 1 or 2 modulo 4.

These are the same four universal finite-residue identities recorded in
`ArithmeticAdaptiveFactorUnits2011.first_bad`, `main_bad`, `aux_bad`, and
`strong_bad`; the direct finite checker independently exhausts their
residue cases. If the parent is zero, the four integer factors multiply
to 1, so each is ±1. The exclusions make all four +1, making every child
square zero. Conversely, if the child is zero, its four integer squares
all vanish, so the four factors are +1 and the parent is zero. The identity
map is the complete two-way witness map; neither fixed-port positivity nor
any solver experiment is used.

## Paid graph and degree

The parent deletes the `Fs`, `F0`, `F1` and four product/final subtraction
rows. The child appends four squares, one `Fa−1` subtraction and three
additions. This gives 48 multiplications, 22 additions and 18 subtractions,
with all 88 gates, thirteen witnesses and four fixed ports live.

The pinned parent degree audit proves that the four factors have degrees
15, 13, 13 and 10 over the symbolic ports; subtracting 1 preserves the
degree of each nonconstant factor. Thus the child degree is at most 30.
Its actual-current-port diagonal at all witnesses equal to t has a
nonzero `t^30` coefficient `750827028` modulo `1000000007`, proving exact
specialized degree **30**. The other three squares have degree at most 26.
The finite degree audit is external, not a Lean `totalDegree` theorem.

## Proof and endpoint boundary

The 87 parent has a historical paired source-level literal identity with
the adaptive parent, and the source records a machine `PolynomialBridge`.
The historical paired `IPRA87TranslatedRefutation` replay gives derivability
against **negated Gödel–Gentzen-translated refutation**, with its inherited
provider/source-ancestry qualifications. The separate source
`IPRAAdaptiveNativeZFC.equivalence87` states a comparison against the
negated mapped native predicate, but the documented combined current-source
replay does not establish that endpoint. These statements must not be
conflated.

The present pointwise integer argument transports the parent's ordinary
zero-existence conclusion. Although its mod-4 reasoning has corresponding
model-level ingredients in the repository, no all-model literal bridge,
new iPRA theorem, coherent provider replay, or formal JSON/PDF binding for
this new graph is asserted here. The parent no-zero theorem does not prove
ZFC consistency, and no global size minimum is claimed.

## Reproduction

[`check.py`](check.py) pins the 87 graph and degree evidence, four formal
negative-unit source identities, 2011 port recipe and payload bytes. It
checks the complete exact graph cut, topology and liveness, exhausts all
mod-4 cases, and evaluates the full child diagonal over the actual port
residues. The [receipt](result.json) records the count, graph hash and
residue/degree checks. Finite checks supplement the proof above; they do
not run Lean, authenticate provider ancestry or evaluate PDF bytes.

```
python3 -I -S -B research/adaptive87-four-square-current88-30/check.py > /tmp/adaptive-current88.json
cmp /tmp/adaptive-current88.json research/adaptive87-four-square-current88-30/result.json
```
