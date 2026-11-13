# Thirteen-positive ordinary unit pair: 88/46 and 90/46

The primary [88-operation, degree-46 graph](freej88.json) has the same zero set **at every integer valuation** as package 115's recorded 87-operation, degree-51 free-`J` graph. It retains that graph's 13 positive witness coordinates and the same four compact44 fixed ports when used as a positive equation. A second [90-operation, degree-46 graph](p73_90.json) has the same integer zeros as the existing P73-parameterized **ordinary-unit 90/51** graph. The 88/46 graph has fewer operations at the same degree, but its first coordinate is free `J`; no same-valuation identity between these two differently encoded graphs is claimed.

The 88/46 point uses one more operation and five fewer degrees than its 87/51 parent, and improves the inspected 90/50 point in both metrics. These are comparisons with recorded 13-positive alternatives, not a global frontier or minimality claim. All binary additions, subtractions, multiplications and squares count once; fixed integer leaves are free, with no new leaf or witness.

The parent free-`J` graph's [author-side endpoint record](../ordinary13-freej87-endpoint/README.md) reports an all-model positive-zero/iPRA chain and its own serial Lean builds, but not a paired replay. The supplied P115 ordinary existence equivalence inherits the free-`J` compiler, calibration and Pell interfaces; the independent manuscript reconstruction specifically does not independently prove that whole chain. This packet supplies external finite graph/algebra checks and a mathematical integer-zero reduction, not a new Lean theorem, full foundational replay, internal JSON/PDF binding, or proof of either side of the consistency statement.

## A global four-factor unit lemma

The free-`J` parent defines integer expressions

```
q = qm+1,  M=q³*qm,  Delta=a²+4*a+3,
Q=Delta*(f²−1),  I=i*c²,  y=V+u,
A0=Z²−M²*(1+ell*(ell+k)),
A1=Dstar²−U²*(1+Delta*c²),
Fa=y²−Q*(y²−V²),  Fs=1+I²−Q,
F0=1+A0,  F1=1+A1,
Pold=F0*F1*Fa*Fs−1.
```

The new output is

```
Pnew=A0²+A1²+(Fa*Fs−1)².
```

For **all integer inputs and integer port values**, none of the four parent factors is −1:

1. `q` and `qm` are consecutive integers, so `M=q³*qm` is even. Hence `A0≡Z²` modulo 4 and `F0≡1+Z²` is 1 or 2 modulo 4.
2. `Delta≡0 or 3` modulo 4. Since `U²,c²,Dstar²` are 0 or 1 modulo 4, the term `U²*(1+Delta*c²)` is 0 or 1; thus `A1` is 0, 1 or 3 and `F1=1+A1` is never 3 modulo 4.
3. `f²−1≡0 or 3`, so `Q=Delta*(f²−1)≡0 or 1`. Therefore `Fa≡y²` or `V²`, and `Fs=1+I²−Q≡0,1 or 2`. Neither is −1 modulo 4.

If `Pold=0`, its four integer factors multiply to 1, hence each is an integer unit ±1. The exclusions force each to be +1, so `A0=A1=0` and `Fa*Fs=1`; hence `Pnew=0`. Conversely, if `Pnew=0`, its three integer squares vanish, giving `A0=A1=0` and `Fa*Fs=1`. The latter product has two unit factors; the same exclusions force both to +1, so `Pold=0`. This proof requires no assumption that `Fa` or `Fs` is nonzero before the product equation is known.

## Graph and degree checks

The [free-`J` literal graph](freej88.json) removes the parent's six-gate four-factor finalizer (`F0`, `F1`, three products and the final subtraction) and adds seven gates for two residual squares, `Fa*Fs−1` and its square, and two additions. Its 88 live gates are 48 multiplications, 23 additions and 17 subtractions. The existing two-gate difference of squares is factored as `u*(y+V)`, exactly `y²−V²` because `y=V+u`; this does not change the count and exposes the degree bound. The first carrier in the 87-gate parent already uses the folded form of the previously found `W*q³` sharing, so switching forms gives no further saving.

For the free-`J` graph, syntactic degree propagation through the factored gap gives `deg(Fa)≤13`, `deg(Fs)≤10`, and output degree at most 46. A full evaluation with all 13 witnesses set to `t` at the authenticated actual ports modulo 1,000,000,007 has degree 46 and nonzero leading coefficient **528057335**. These yield exact specialized integer degree 46. The 90/46 P73-parameterized ordinary comparison has the same syntactic upper bound and full-ray degree 46 with leader 832098066.

The 90/46 comparison changes the reviewed 90/54 normalized-pair strong factor to `Fs=1+I²−Q`; its `A0`, `A1`, `Fa` and `Fs` match the existing P73-parameterized ordinary-unit 90/51 graph by exact symbolic cuts. Its unit proof is the same as above. It is **not** asserted pointwise equivalent to the normalized P73 90/54 or 90/50 graphs: the ordinary and normalized strong equations are different witness conditions. The existence results for the separate encodings remain inherited from their respective sources.

## Reproduce

From the repository root run:

```
python3 -B Computability/DiophantineConsistency/research/ordinary13-ordinary-pair88-46/check.py
```

The deterministic output is [result.json](result.json). The checker pins and reconstructs the entire 87/51 graph delta and the 90/54-to-90/46 comparison delta, checks graph order and liveness, proves the needed difference-of-squares and ordinary-comparison cut identities in a small exact sparse polynomial ring, and checks finite modulo-4 controls. It authenticates all four compressed and raw little-endian P72 payload copies against the P115 binding, including the already-shifted MF port, then evaluates both entire graphs at those port values on the modular ray. The finite controls do not replace the global unit argument above. The fixed-byte graph/degree correspondence is external and is not a Lean `totalDegree` or file-semantics theorem.
