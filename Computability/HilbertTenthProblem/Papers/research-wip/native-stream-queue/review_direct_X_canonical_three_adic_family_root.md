# Root review: exact canonical three-adic depth and the radix obstruction

PASS for the exact valuation theorem, the infinite scalar cubic-scale
family, and its exclusion by every inherited original compiler radix.
Root independently reviewed the valuation and scalar-family arguments;
the radix obstruction is root's own contribution, independently checked
by Pascal. These results do not supply a direct-X83 zero or change the
universal84 bound. Exact final author and evidence bindings accompany
this note.

## 1. Independent valuation review

For H_r(X)=sum(j=0..r) binom(2r,r+j)X^j, the coefficient of X^j in
X(1+X)H'_r+r(1-X)H_r is

    (r+j)binom(2r,r+j)-(r-j+1)binom(2r,r+j-1)=0

for j>=1; the constant is r*binom(2r,r). Changing variable to t=X+1
therefore gives

    A0=binom(2r,r)/2,
    (2r-j)Aj=(r-j+1)A(j-1).

The integer solution Aj=binom(2r-j-1,r-1) has the required initial
value and recurrence. Thus the author's expansion at -1 is an all-size
integer polynomial identity. No source-array expansion is involved.

Put P=3^e,r=P-2. The central binomial floor sum has contribution0 at
3 and1 at every power9 through3^e, giving v3(A0)=e-1. In the recurrence,
numerator factors P-d have2<=d<P and denominator factors2P-d have
5<=d<=P+2<2P. Their valuations equal those of d; the only possible
exception d=P gives valuation e on both sides. Consequently

    v3(Aj)=e-v3((j+2)(j+3)(j+4)).

I checked the endpoint e=1 separately: r=1 and both A0,A1 equal1.
The same formula holds. For R=2*3^e-3 one has v3(R)=1. Hence
v3(2^R+1)=2. This can also be seen directly by writing R=3m with m
odd and coprime to3 and expanding8^m=(-1+9)^m: the first nonconstant
term has valuation2 and all subsequent terms have larger valuation.

For j>=1 the product(j+2)(j+3)(j+4) has just one factor divisible by3.
Since j+4<3^(2j+1), its valuation is at most2j. Thus every nonconstant
term Aj(2^R+1)^j has valuation at least e, whereas the constant has
valuation e-1. There is no cancellation of that unique minimum.
Division by2 is a3-adic unit, proving v3(Y_R)=e-1 exactly.

## 2. The cubic-scale family is valid at its stated scalar interface

For even k>=2 take q=2*3^k, e=3k+2 and R=2*3^e-3. The exact theorem
gives v3(Y_R)=3k+1. For every odd R>=3, all noncentral terms in Y_R
have binary valuation at leastR-1, strictly above the central term's
pc((R-1)/2)-1=pc(R)-2. Therefore this central population gives the
exact binary valuation, not just a lower bound on one summand.

Here e is even, so R=15 modulo16, with R>15. Its population is at
least5 and v2(Y_R)>=3. Hence q^3 divides Y_R and q does not divide2^R.
The two numerical outer margins are exactly

    R-(2q-1)(q^2-1)=q^3/4+q^2+2q-4>0,
    q^3(q-1)-R=q^3*(q-13/4)+3>0.

This is an infinite family satisfying the strengthened numerical size
window as well as the canonical cubic scale. It does not specify the
literal outer packed-index, field, transport or positive input witnesses.

## 3. The missing repunit has an all-compiler obstruction

Root's fresh scalar order certificates give

    ord_31(3)=30, 3^6=16=1/2 modulo31,
    ord_601(3)=75, 3^42=301=1/2 modulo601.

The full orders follow from the power1 tests and residues different from1 at
30/2,30/3,30/5 and75/3,75/5, respectively. Primality of these moduli
is not needed. Both divide2^25-1=31*601*1801. If25 divides d, then
2^d-1 dividing2*3^k-1 would force k=6 modulo30 and k=42 modulo75.
Their residues6 and12 modulo15 are incompatible.

The inherited modified75 recipe requires b to be a power of5 with
2^b>=16, hence5 divides b. It keeps the complete76 choice of L, a
power of5 with L>T2+2Emax+1. Since Start0 and End1 are native positions,
Emax>=1 and T2>=0; thus L>3 and5 divides L. Consequently25 divides
d=bL on every original compiler slice. Its literal q=(2^d-1)J+1
cannot hold at any q=2*3^k, regardless of ordinary input or Pell data.

Author Review Remark1 correctly retains the refuted inference from the
successful scalar family to a full compiler zero. The small width d=5,
k=6 example has q=1458 and J=47, but that width is outside the actual
inherited compiler recipe. It is not a counterexample to this obstruction.

**Review remark 1 (retained order-test terminology correction).** The draft
called the proper-divisor test residues "nonunit residues". That wording
was wrong: every power of3 here is a unit, and30^2=1 modulo31 explicitly
exhibits an inverse for one displayed residue. The order test needs these
residues to differ from1, as corrected above; it does not require them to
be noninvertible.

## 4. Evidence and scope

Root read the complete author proof and helper inertly, the full prior
Lucas note and its mandatory scope correction, the full canonical
resonance-repair and authentic-outer notes, modified75 lines1--190, and
complete76 lines1--165. Older compiler and native soundness/completeness
theorems are inherited, not independently recertified in their entirety.

The author's prefreeze checks cover350 coefficient comparisons,3272
coefficient-depth controls, seven directly evaluated scalar canonical
residues and six larger scalar-family controls. These were read without
replay. The larger family controls use the proved valuation formula;
they do not evaluate their enormous full sums. Root separately checked
the small modular orders and source-span bindings with fresh scalar
arithmetic, saved in direct_X_single_prime_radix_root.json.

No saved source array was evaluated or propagated, no native tuple was
materialized, and no supplied, frozen, archived or predecessor scientific
program was run or imported. General canonical no-wrap soundness,
other radix families and higher valuations outside this family remain
open at the credited scopes in the author note.

## Frozen author and scalar bindings

| Artifact | SHA256 |
|---|---|
| Author proof | c18f09aa7fd0b4eb89bbdbbca2a5b5ad3aed3f5d559e6afb02034cb9bb62f7cc |
| Author helper, read inertly | f3fcc83f78ad0aaad9bcfdbb6367780372abef510a7ecd574206b85984b1bcaf |
| Author receipt | 5c45f321f76a6eabac810291ab6059ff963cff3d7670f373adc05714c85883db |
| Root fresh scalar/order evidence | 2caf1521fa8c13d5204c9c8ed951a529e37b3166d8057af0fbfb5b580c344378 |
