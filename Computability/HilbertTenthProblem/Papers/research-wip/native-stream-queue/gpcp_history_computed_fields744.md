# Compute three history fields: 744 operations in the complete GPCP compiler

The [guarded compiler](gpcp_history_computed_fields744.py) eliminates three
positive truth-field coordinates in the history AND of the
[754 parent](gpcp_coupled_index_units754.md). The default complete polynomial
costs **744=349M+395A**, with **721 certificate operations, eight comparisons,
122 positive witnesses**, three fixed positive program parameters and
ordinary positive input. Its exact formal degree is **187625**. Supplying
the initial-history coordinate gives **747=350M+397A**, nine comparisons,
123 witnesses and exact degree **8481**.

This saves **3M+7A and three witnesses** in the selected complete GPCP route.
It does not change the independent 75-certificate/87-polynomial universal
bound. All recoder truth fields remain supplied positive coordinates.

The new positive zero set is in bijection with the parent's
**history-checksum-positive slice**. Normalizing the history branch gives a
surjection from all parent positive zeros, with exactly two preimages for
each new positive zero. Every program parameter, ordinary input, external
history word and retained coordinate is preserved by restoration; projection
can change the private history native bound slack. This holds for every
positive choice of the program parameters, without asserting that every
ordinary input has a zero.

The [receipt](gpcp_history_computed_fields744.json) contains all eight complete
polynomial schedules, their literal counts, nonzero leading certificates,
and replay evidence. The eight configurations toggle the computed/supplied
initial interface and the AND/geometry bound conversions.

## 1. Exact field restoration and the seven-row packed index

Write `H,M,Z` for the actual joined history words and `N=P^69` for the
history scale. In the parent, the retained source computes

```text
q  = 16N
Ap = padded_A = 16H+13
C  = padded_B = 16M+10
F3 = 16Z+8.
```

The parent first-padding factor is `Ap−(F1+F3)`. Its positive-zero value
is +1, so the original first port is **A=Ap−1=16H+12**. Confusing Ap with
A would erase the wrong equation. Restore the removed coordinates by

```text
F0 = q−A−C+F3−1 = 16(N−H−M+Z)−15
F1 = A−F3       = 16(H−Z)+4
F2 = C−F3       = 16(M−Z)+2.
```

These formulas make the history checksum `q−ΣFi` and first-padding factor
identically one, and make the paid second-port residual `F2+F3−C`
identically zero. The parent's packed index satisfies the exact polynomial
identity

\[
 F0+qF1+q^2F2+q^3F3
   =(q-1)\bigl[Ap+(q+1)(C+(q-1)F3)\bigr].                 \tag{1}
\]

The emitted source evaluates its right side in seven charged operations:

```text
qm = q−1
qp = q+1
v  = qm*F3
u  = C+v
w  = qp*u
S  = Ap+w
r  = qm*S.
```

The fields are mathematical extension coordinates, not free arithmetic
gates hidden in the emitted program. Equation (1) is the complete surviving
dependence on them. Their restoration formulas do not need to be evaluated
by the new polynomial.

## 2. Positivity before any AND or history typing

It remains necessary to prove that the computed subtractions above are
positive at every new positive zero. A signed graph identity alone would
not establish the positive-domain equivalence.

Let `D=hist__height_sum__2`. The literal source gives

\[
 D=U_{final}+I_{bottom}+V_{final}+\text{height_slack},
 \qquad B=131072D,
 \qquad J=\sum_{i=0}^{56}(\widehat S_i-1),
 \qquad P=(B-1)J+1.
\]

For computed initial input, `I_bottom=input_bottom` is formed by positive
numeral products and additions of positive inputs and program parameters.
For supplied initial input it is the positive coordinate `Vinitial`.
Thus `D≥4`, `B≥524288`, and `J≥0`, independently of interpreting the
program or proving a native norm.

The finalizer is still `W(1+SOS)−1`, where SOS is the sum of squares of
every remaining ordinary residual and W is the product of every remaining
integer unit factor. At an integer zero, `SOS=0`, `W=1`, and each factor
is ±1. In particular the retained global history factor is

\[
 G=P-\Sigma-\beta\in\{-1,1\},\qquad \beta>0,
\]

where Σ sums the two positive history coordinates and eight positive
selected-product hats. Hence `10≤Σ≤P`; each of those ten coordinates is
at most `P−9` and therefore below P. The case J=0 would force P=1, so
`J≥1` and `P≥B`. This argument includes the weak boundary
`G=−1, β=1, Σ=P`, and the minimal selector case `J=1,P=B`.

Here are the actual source regions. Decode hats by subtracting one and put

\[
\begin{aligned}
 C_{ctrl}&=\sum_{i=0}^{56}(\widehat S_i-1)P^i,&
 R&=H_U+P H_V,\\
 H_{phys}&=(H_U+P^4H_V)(1+P+P^2+P^3),\\
 Z_{phys}&=\sum_{i=0}^{3}(\widehat Z_{Ui}-1)P^i
             +\sum_{i=0}^{3}(\widehat Z_{Vi}-1)P^{i+4},\\
 M_{phys}&=(B-1)\sum_{i=0}^{7}S_iP^i.
\end{aligned}
\]

The eight `S_i` use respectively the selector subsets `(0,1)`, `(4,5)`,
`6..20`, `21..28`, `(0,1)`, `(4,5)`, `6..20`, and
`(21,22,23,24,29)`. Each individual subset contains no repeated selector,
so `0≤S_i≤J`; different subsets need not be disjoint. Literal substitution
in the full source yields

\[
\begin{aligned}
 H&=H_{phys}+P^8C_{ctrl}+P^{65}R+B P^{67},\\
 M&=M_{phys}+P^8J(1+\cdots+P^{56})
       +P^{65}(D-1)J(1+P)+(B-1)P^{67},\\
 Z&=Z_{phys}+P^8C_{ctrl}+P^{65}R.
\end{aligned}                                                     \tag{2}
\]

Every physical/controller lane is nonnegative and at most P−1:
individual selectors and subset sums are bounded by J, and
`(B−1)J=P−1`. The two history coordinates are below P. The range mask
has `(D−1)J<(B−1)J=P−1`, so its two-lane word is below P².
These are ordinary integer positional bounds; a dyadic radix, Boolean
typing and carry-free interpretation have not been assumed.

Writing `T=P^67`, (2) therefore gives

\[
 H=BT+H_{body},\quad M=(B-1)T+M_{body},\quad
 0\le H_{body},M_{body},Z<T.
\]

Consequently `H−Z>0` and `M−Z>0`. Also

\[
 H+M-Z<(2B+1)T<P^2T=N,
\]

since P≥B≥524288. The three restored fields are all strictly positive;
in particular `F0≥1`. Together with F3 they have residues `(1,4,2,8)`
modulo16 and sum to q−1. Positivity is now established **before** invoking
the parent AND or history theorem, avoiding a circular transfer.

The recoder lacks these reserved top regions and is not covered by this
argument. Its supplied positive F0,F1,F2 and all their constraints remain
in the emitted source.

## 3. Full signed graph identity, including the finalizer

Let `iota(v)` restore only the three displayed fields from a complete
integer new assignment v. Formula (1) preserves the exact packed index;
all other surviving source definitions are unchanged. The two removed
factors are identically one and the removed ordinary residual is
identically zero. Thus, for every signed integer v, not just valid zeros,

\[
 W_{754}(\iota v)=W_{744}(v),\qquad
 SOS_{754}(\iota v)=SOS_{744}(v),\qquad
 F_{754}(\iota v)=F_{744}(v).                              \tag{3}
\]

The implementation checks every retained factor and residual as well as
both complete final polynomial outputs. The finalizer deletes the
multiplications by the two constant-one factors and the zero comparison;
it does not discard a bound factor, an index factor, or a native norm.

At a new positive zero, Section 2 makes iota positive, so (3) gives a
positive parent zero with history checksum +1. Conversely, at such a
parent zero, the established 754 theorem forces first-padding sign +1.
That sign, the paid second port and checksum +1 uniquely determine F0,F1,F2
by the restoration formulas. Erasing these fields and restoring returns
the same parent tuple. This proves the claimed slice bijection.

## 4. Normalize the other parent history branch

For any positive parent zero write C for its history checksum and E for
its history index unit. The [754 sign theorem](gpcp_coupled_index_units754.md#3-and-signs-including-subtraction-across-a-base-q-boundary)
gives `C=E=±1` and first-padding sign +1. Normalize only this history core:

\[
 F0'=F0+C-1,\qquad \beta'=\beta+1-C.                       \tag{4}
\]

Here β is `hist__and__bound_beta`, distinct from the unchanged global
history bound used in Section 2. For C=−1 the parent theorem gives
`F0≡3 mod16`, so F0−2 remains positive, while β increases by two.
The packed index changes by C−1; its sum with β is unchanged. Both the
ordinary-bound and bound-unit configurations therefore retain the same
bound value. All norms, coupled linear targets, external words and
ordinary residuals are unchanged. Checksum and index both become +1;
their old product was C²=1. Thus (4) maps every parent positive zero to
the history-checksum-positive slice. Erase the three fields afterward
to obtain the public projection to744.

There are exactly two parent positive preimages over each new positive
zero. The canonical restoration supplies one. In its history core the
parent theorem gives `X=2^(2r+1)`, `r≥9`, and β equals X−r for an ordinary
bound or X−r−H with H=±1 for a bound unit. Hence β>2. For δ=0 or 2,

\[
 F0_{parent}=F0_{restored}+\delta,\qquad
 \beta_{parent}=\beta_{restored}-\delta                  \tag{5}
\]

stays positive. Its checksum and index become `1−δ`, with product one;
all other factors and ordinary residuals are unchanged. These are two
parent zeros and both project back to the same new tuple. Conversely,
the sign theorem leaves only these two choices, and all other retained
coordinates are fixed by the projection. The recoder branch is retained
throughout; the parent's older four-to-one relation with757 is not
inherited as a four-to-one claim with744.

The normalization API also has a precise signed off-zero extension. For
arbitrary parent integers use its actual checksum C in (4), not merely
a sign. Then checksum becomes one and index becomes E−C+1. Let B0 be
the product of all other parent factors and S its ordinary residual SOS.
Every ordinary residual is unchanged, so

\[
 F_{754}(\operatorname{norm}v)-F_{754}(v)
   =B0\bigl[(E-C+1)-CE\bigr](1+S).                       \tag{6}
\]

`normalization_correction` executes both complete parent schedules and
checks (6). Positivity and preservation of zero are claimed on the stated
positive-zero domain, not for every off-zero tuple.

## 5. Literal arithmetic counts and exact formal degrees

The original checksum/port/packing block has eleven rows. Seven rows in
(1) replace it, saving four additions/subtractions. Removing the history
first-padding subtraction and its product multiplication saves 1A+1M;
removing the checksum product multiplication saves 1M. Thus the certificate
saves 2M+5A=7 operations. The finalizer's removed ordinary comparison
saves one residual subtraction, one square and one accumulation addition,
giving a further 1M+2A. The total is **3M+7A=10 operations**.

All additions, subtractions and multiplications, including products by
literal constants, are charged. No arithmetic optimality claim is made.

|Initial interface|AND bound units|Geometry bound units|Polynomial operations|Certificate operations|Comparisons|Witnesses|Exact degree|
|---|---|---|---:|---:|---:|---:|---:|
|Computed|No|No|748=349M+399A|713|12|122|205516|
|Computed|No|Yes|746=349M+397A|717|10|122|205582|
|Computed|Yes|No|746=349M+397A|717|10|122|187559|
|Computed|Yes|Yes|744=349M+395A|721|8|122|187625|
|Supplied|No|No|751=350M+401A|713|13|123|8631|
|Supplied|No|Yes|749=350M+399A|717|11|123|8697|
|Supplied|Yes|No|749=350M+399A|717|11|123|8415|
|Supplied|Yes|Yes|747=350M+397A|721|9|123|8481|

Degree propagation consumes the full emitted polynomial and the three
guarded expanded main norms inherited from the
[shared-selector degree checker](gpcp_shared_selectors774.py). Its expansion
removes the actual leading cancellation in each R15; the remaining highest
term is `2*cam2*gam`, strictly above every other expanded term. Each required
source row and strict inequality is checked. Every other gate uses ordinary
degree propagation.

To prove that the upper degree is attained, the receipt gives complete
input assignments where the final homogeneous leading form is nonzero
modulo both `1000000007` and `1000000009`. All factor leading evaluations
are also nonzero. For the default the final values are `12031295` and
`516593763`, with `187625=187489+2*68`. For the supplied default they are
`780831774` and `300576773`, with `8481=8349+2*66`. These are exact formal
degrees before specializing program parameters; degree preservation under
every specialization is not asserted.

## 6. Guarded interfaces, metadata and replay

The compiler pins the complete parent source SHA256 to
`80c5f06ef5ec43975369ed2f9737fdf0d75b44e5abba4c24e19a2bc4fba1f9e3`
and checks a complete exact-type canonical754 packet. It checks the changed
rows and actual consumer sets: the erased fields are private to the old
checksum/ports/packing, β occurs only in the native bound, and the packed
index feeds only that bound and its index factor. Actual history metadata
and region constants are checked and retained. Every emitted gate reaches
the final polynomial output.

Active metadata is rebuilt from the current parent interfaces. Removed
history first-padding factors/interfaces are removed from the active lists;
the current program, machine, loader, layout and history packet stay intact.
No old coupled-interface record or inherited four-fiber claim remains.
The historical parent source/comparison/factor lists are explicitly labeled
as parent data. Current active exports contain no erased field or register.

The main APIs are `build`, `canonical_parent`, `rewrite`, `checked`,
`polynomial_source`, `degree_audit`, `ledger` and `evaluate`. Assignment APIs
are `restore_assignment`, `normalize_parent_assignment`,
`project_assignment`, `lift_parent_assignment`, `offzero_identity` and
`normalization_correction`. Their docstrings distinguish formal signed
maps from positive-zero theorems. Assignments must contain exactly the
required child or parent parameter/auxiliary names and exact Python integers.
Booleans, floats, extra/missing keys and wrong coordinate interfaces are
rejected. Lift deltas must be exact integers 0 or 2. Public build and parent
accessors return defensive copies; private canonical caches cannot be
poisoned through them.

The author receipt records:

- 96 full signed restored-graph identities, including 48 signed assignments
  and 24 zero-decoded-selector contexts;
- 96 formal graph projection round trips and 192 two-lift projection
  round trips, plus 96 complete normalization corrections;
- 512 literal pretyping history cones, including 64 cases at
  `J=1,P=B,G=−1,Σ=P`, plus 93 positive native-slack components;
- 16 nonzero complete leading certificates across all eight schedules;
- 732 malformed caller rejections, including scalar type substitutions,
  400-digit input coefficient-mutation regressions, active metadata changes,
  wrong assignment interfaces, bad lift deltas and cold-cache poisoning.

These finite checks supplement the proof. They do not materialize an
enormous complete positive Pell witness or certify a new ordinary input
by merely satisfying a scalar-cone fixture.

Run from the repository root:

```sh
python Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/gpcp_history_computed_fields744.py
```

Default execution recomputes the receipt and compares it without writing;
`--write` regenerates it. No `/tmp` resource is needed for replay.

An independent mathematical review reconstructed all three exact region
identities, checked 228 selector-position/boundary cones and 64 additional
raw cones, 96 complete signed graph identities, 16 normalization maps,
and exact degrees with independent leading evaluations at two primes.
It found no mathematical gap. Its temporary review and evidence are
`/tmp/review_gpcp_history_computed744_math.{md,py,json}`.

Independent source/API review passed on frozen Python SHA256
`da3ec5d08068a9fcfa783f1ed0b0d97b2f2aa5b33cc63c218f003716b347f1ef`.
It rejected 1,400 malformed calls, checked eight cold parent copies and
eight nested build copies, all eight source/output closures and interface
privacy/fiber metadata, 16 independently expanded-norm leading
certificates, 48 complete signed graph identities, 96 formal lift/normalize
round trips and 16 independent normalization corrections. That reviewer
also read this complete note, verified its links and theorem anchor, and
replayed the default receipt successfully. The evidence is
`/tmp/review_gpcp_history744_api.{md,py,json}`. The author's separate fresh
read-only replay also passed; no source change followed the freeze.
