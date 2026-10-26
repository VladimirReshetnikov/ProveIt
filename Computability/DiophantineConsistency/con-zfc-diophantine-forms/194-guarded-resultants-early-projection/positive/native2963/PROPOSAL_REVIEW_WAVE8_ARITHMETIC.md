# Wave8 arithmetic and native-interface review

The reviewed proposal commit is
`beb0192cb8dc36f78c369c080f2adfbc1887a486`. This note records a read-only
mathematical/provenance review of packages 54, 55, and 58, the short-form comparison,
and the old-transport boundary relevant to 57/59. It supplements the overall
[wave8 review](PROPOSAL_REVIEW_WAVE8.md); it does not replace the historical
reviews or assert a global optimum.

The complete archive extractions used for the review are recorded in
`/tmp/proofs62ff-wave8-review/archives.json`. Repository research trees deduplicate
inherited files, so an inherited proof absent from a package's placed subtree
is not evidence that its raw archive omitted the proof. In particular, 54's
`native/INHERITED_SEPARATED_PROOF.md`, controller data, and payloads are present
in the complete raw archive. Full finite-replay results are recorded by the
other wave8 reviewers; the arguments below were inspected independently of
those replay successes.

## Whole coefficient bindings

| Package | Selected complete tuple | Native base exponent | Important convention |
|---|---|---:|---|
|54|complemented-factorized-receiver-89x4831|429959|MF_source already includes B−1|
|55|wang943-mixed-121x8801|1064921|All four package31 ports retained|
|56 short forms|wang943-mixed-121x8801|1064921|Same complete package31 tuple|
|58|wang943-complement67-shared-anchor-length8807-prime581197|590069|All four source44 ports retained|

These are deliberate different instances, rather than interchangeable
individual ports.54's four port bit lengths are 429959,434054,429959,429960;
55's are 1064921,1070004,1064921,1064922;58's are 590069,592884,590069,590070.
The aliases K0→K and MF→MF_source do not add another mask shift.

54 selects its whole tuple from the archive pinned to
`4b4349064a750ba6347293b55874a7f92abdd0db`, whose recorded Git blob is
`143a1487c8c28aac7e14c6e723a763040c508d0b`. Its smaller tuple uses 457
factorized selector modes, rather than simply keeping 943 independent selector
positions. The factorized language is decoded and then expanded to the original
marked Wang language.55 explicitly keeps the larger historical tuple, including
in the newly emitted circuits.58 uses the same compact tuple as report52;
its historical source-commit field does not claim that the new integral-root
reduction existed at that earlier commit.

##54: receiver decoding and squared-modulus quotients

The local complemented-receiver decoder is valid on the stated Boolean
supported digits. Selector extraction first forces n∈{0,1}, without assuming
that the higher payload fields are carry-free. The gate ranges then justify
the subsequent field separation. Writing the aggregate payload modulus as
M=4T, parity forces the copied west low bit y=n.

For n=0, the aggregate lies in[0,M), so its congruence to zero forces every
positive-coefficient receiver, label, and anchor contribution to vanish.
For n=1, it lies strictly between0 and2M and hence equalsM. The upper count
field is3, forcing y and both standalone anchors to be1; the lower field is
exactly the complement of the selected expanded label vector. The positive
receiver increments fit in their fields. This closes the formerly problematic
nonzero-payload empty-cell case. The two distinct temporal anchors remain
available even though a copied parity bit supplies the common source anchor.

The complete proof then invokes the inherited alignment, carry, language,
actual-rank padding, and K215/refutation interfaces. The supplied conservative
mass and the finite support identities are inputs to those arguments; checking
the large integer bytes alone would not prove their unbounded interpretation.

The canonical phase R≡3(mod4) needed by the new quotient survives this tuple:
q=B^N≡0, J=1+B+⋯+B^(N−1)≡1, and MC≡2(mod4). The native origin disjointness
forces C≡1(mod4). Therefore G=q(q−F)−C≡−C and
R=G(q²−1)+(MC+q MF_source)J≡C+2≡3(mod4).
This concerns authentic compiler witnesses, not arbitrary integer ports.

The short-form substitution

```
V_new = f²(cT−R)−c = c((fT)f−1)−Rf² = V_old(T_old=fT)
```

proves soundness directly. Completeness constructs fresh auxiliary witnesses;
it does not assert that every older positive quotient T_old is divisible by f.
With A=a+2, I²=(A²−1)(f²−1), and R=2r+1≡3(mod4), the odd Pell quotient
polynomial gives

```
V=chi_I(R)/I ≡ −c (mod f²),    V ≡ −R (mod c).
```

The canonical normalized strong witness gives f²≡1(mod c) and gcd(c,f)=1.
Thus T=(V+c+Rf²)/(cf²) is a positive integer. The auxiliary Pell norm gives
y>V>1, so the positive auxiliary gap is available. The same argument is used
correctly in 55's fourteen-variable construction, 56's short forms, and 58.

54's constant-cancelled minimum finalizer A²+B(B−2)+C² is also sound:
A is an unconditionally nonzero product of the first/main norms, so a zero
forces A²=1, B=1, C=0. Unit-sign recovery uses the consecutive negative-Pell
obstruction and modulo-four arguments in the stated order. Possible index and
transport signs are left to the inherited ordinary kernel; they are not assumed
positive before its boundary argument.

##55: congruence separation and its inherited inputs

55's ten-integer finalizer establishes distinct radicands on every signed
assignment: a/b is odd while d/b is even, with b≠0. Thus a≠d before any square
condition or positivity is recovered. The rational two-root identity then
forces integer roots, rather than relying on a conditional size comparison.
The coprime signed-square factors and residue1 modulo3 recover positive square
factors; the combined guard then forces Delta>0. Only afterward are the source
and Lucas-bridge positivity bounds invoked. The normalization restrictions on
h and k are justified using the constructive Lucas indices, not assumed for
arbitrary old solutions.

This ten-integer branch expressly retains Sun's 2026 modified-Lucas/residue
interpolation theorem as an external mathematical input. Its supplied finite
checks and bundled K215 source inventory are not a new Lean proof of that
input. The nine-positive branches instead use the Jones ratio theorem and do
not need the Sun interpolation theorem.

The common positive-word substitution is coherent: with g=Σ n_i B^w_i,
1+ell+g supplies the positive source tuple n_i+1 inside the square. It changes
the coefficient support relative to an all-coordinate affine shift, so the
retargeted rows13 and21 are necessary. The proof uses the stronger coefficient
and pre-decoding range bounds appropriate to this word; it does not silently
reuse the invalid earlier extraction targets. The canonical parity restrictions
on g and the Jones multiplier h are proved from the actual constructive Pell
recurrence.

##58: integral-root carriers and positive inverse maps

The degree 24/90 construction recovers the missing scales sequentially. Its
first monic square equation forces q³|Y by m²|n²⇒m|n. Only then does
H=4Y(X+1)+3 become3 modulo q. The actual odd base exponent 590069 gives
beta≡1(mod3), and the supplied J=3j+1 forces q≡2(mod3) at every positive
assignment. Consequently gcd(q,H)=gcd(q,3)=1, so the second square equation
forces q|X. These are established integrality arguments, not evaluation-time
divisions or extra quantified variables.

The inverse maps have the required strict positive margins. The authentic
compact controller supplies odd N=581197^n>1. Since B≡−1(mod3), its geometric
sum has J≡1(mod3) and J>1, giving j=(J−1)/3>0. Canonical first-Pell growth
makes tau−ell>k/3>s, so r=tau−ell−s>0. The displayed main-Pell growth bound
makes gamma_old>w, so gamma=gamma_old−w>0. Positivity of gamma_old alone
would not have justified this subtraction.

The squared-modulus quotient is reconstructed as above. A potentially signed
V+u is replaced by its absolute value in soundness; its nonvanishing follows
from the auxiliary norm and I>1. Completeness supplies the positive gap from
fresh canonical Pell values. Finally replacing R by k−hXY−1 inside the auxiliary
expression is justified by a retained separate index equation. The degree 26
variant keeps R when coupling index and transport, and the degree 30 variant
needs only the first scale carrier, as its proof states.

No defect was found in these local arguments. They remain ordinary mathematical
reductions using the inherited native/Pell compiler. They are not newly checked
full coefficient-specific Lean proofs or internal object-language ZFC derivations.

## Corrected fifteen-positive comparison

The following distinct degree/cost tradeoffs must be retained. The numbers are
live binary operation counts followed by exact reported degree. They agree
with the independent literal circuit ledger in
[wave8-circuits.json](reviews/wave8-circuits.json); degree and semantic proof
status remain separate from that ledger's topology/count checks.

| Source | Operations | Degree |
|---|---:|---:|
|51, inherited P66|66|157|
|59|67|125|
|54 and59|68|101|
|59|69|91|
|54|70|80|
|54|71|78|
|54|72|64|
|56, Q54|73|54|
|56, Q46|74|46|
|47, minimum-norm grouping|75|44|
|58|79|30|
|58|88|26|
|58|90|24|

In particular, 51's66/157 point survives;58's lower degree does not erase its
operation advantage. 54's73/62 point is dominated by 56's73/54, and 54's
70/84 and73/68 comparisons are dominated. The older 72/80 and74/68 entries
must not be presented as the current frontier. These are bounded comparisons
within the inspected catalogue, not global minimality claims.

## Exact old-z versus report52 boundary

For C=q−F−alpha and q−1=beta J, define the two transport residuals

```
r52(z)   = (K0+w)C − F − z*beta*J,
r_old(z) = (K0+w)C + (q−F) − z*(q−1) − 1.
```

Then r_old(z)=r52(z)+beta J, and r_old(z+1)=r52(z). This is the difference
between the authoritative old-transport parents used by 57/59 and the frozen
report52 source. An auxiliary copied source_system60.json that matches 52 does
not override a circuit's authoritative parent_source.json.

The map z_old=z52+1 sends every positive shifted source zero to a positive
old source zero. Its inverse maps all old tuples with z_old≥2 to positive
shifted tuples. At z_old=1 it gives z52=0, outside the shifted positive domain.
Therefore the residual identity alone does not prove an unrestricted positive
zero-set bijection at arbitrary ports.

Authentic canonical completeness supplies the missing boundary restriction:
after the native/Pell recovery, C>0 and w>q>F give

```
(z_old−1)(q−1) = (K0+w)C−F > 0,
```

hence z_old≥2. This is already the explicit transport-shift argument in the
inherited ordinary proof and the report 31 QUARTIC60 proof. Old-z 57/59 are
compatible with the original native interface; report52 uses its justified
shifted presentation. They must not be conflated in a generic Lean theorem.
The checked
[NativeArithmetic52](Lean/DiophantineConsistency/NativeArithmetic52.lean)
source elimination applies to its exact shifted source; applying it to an old
parent requires this explicit transport map and its positive-domain handling.

The remaining formal obligations are unchanged in kind: authenticate and
formalize the selected whole tuple's native arithmetic-to-blank-K215 equivalence,
then compose with the already checked K215/refutation endpoint. An internal
ZFC proof of the consistency/unsolvability biconditional is a further distinct
obligation, described in [OBJECT_ZFC.md](OBJECT_ZFC.md).
