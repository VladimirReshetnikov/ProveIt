# Recovering a positive horizon from a signed power

Prepared with AI assistance for the ProveIt research iteration, 25 October 2026.

## Scope and two complete choices

The source has the inherited signed Pell frame, squared anchor, complete
coordinate-orientation pool, and eighteen power requests. Compose the
independently proved replacements R=F, q=4z+1, and y=F(2v+1). The literal
stored horizon is t0=t-16; no sign is imposed on t0.

Either of the following two schemes is valid:

1. t=16h, d=t+2, F=d^t;
2. t=8h, d=2(t+1), F=d^t.

Every h, z and v is an unrestricted integer. The displayed variable power
means the existing ordinary polynomial Pell certificate at index t; no new
power primitive is added. Thus the two source rows that define t0 and d are
affine. Relative to the former square horizon t0=h^2, the t0 coordinate can
be eliminated by integral affine substitution, preserving quadratic
residual degree.

The first scheme gives t>=16 at every zero. The second gives t>=8, and the
few inherited estimates that had previously cited 16 are checked below.
Both schemes admit arbitrarily large horizons in completeness.

## 1. The frame bound before any sign is known

The actual frame is W=2+sum(atom^2), where the list includes the actual
affine exponents, outputs and bases of every request, and includes q,
q+1, the semantic anchor index H, and each principal requested index k_i.
In particular

    H^2 < W,       k_i^2 < W.

Since q=4z+1, one has q^2+(q+1)^2>=5 for every integer z. Hence W>=7.
No positivity of t, F, y, B, q, the CRT representatives or any power output
has been used.

The odd frame norm is

    A^2 - W^3(W+2)(2a+1)^2 = 1.

At center W+1 this is a Pell norm with nonzero ordinate W(2a+1).
Classification and Y_j(W+1)=j modulo W give a positive index j divisible
by W. Consequently |A|>=X_W(W+1)>W^W. For W>=7,

    |A-1| >= |A|-1 > 4W^3.

This is the same frame argument as in the inherited proof; only the
unnecessarily strong preliminary lower bound W>=258 is replaced.

## 2. A sharper orientation estimate

The squared cap gives C!=0 and |C|>|H|, where C is the anchor ordinate.
First exclude the potentially exceptional branch |C|=1 without invoking
the comparison-index theorem there. In that branch the cap forces H=0 and
every other principal ordinate to be zero. The classified anchor index is
one and all other classified indices are zero. In particular all j_i^2<W.
The anchor's ordinate error is nonzero modulo A-1: its small residue is
either 1 or -1 whereas H=0. The full orientation pool explicitly retains
this anchor term, so its reduced nonnegative error sum E is positive.
The bound below shows E<|A-1|, contradicting divisibility. Thus |C|>1.

Now the inherited signed-anchor comparison implies H!=0, the classified
anchor index equals |H|, and every other classified index j_i satisfies
j_i<|H|. The anchor itself has j_i=|H|. These conclusions do not use H>0
or any arithmetic sign.

For each of at most fifteen principal pairs, reduction modulo A-1 has an
abscissa residue s_i in {-1,1} and an ordinate residue r_i with
|r_i|=j_i. (At j_i=0, r_i=0.) Therefore

    (s_i-1)^2 <= 4,
    (r_i-k_i)^2 <= 2j_i^2+2k_i^2 < 4W.

The retained pooled congruence makes A-1 divide their nonnegative total E.
But

    0 <= E < 4m(W+1) <= 60(W+1) < 4W^3 < |A-1|

for m<=15 and W>=7. Thus E=0. Both coordinates of every principal pair
are exactly the signed Pell polynomials X_(k_i)(A),Y_(k_i)(A).

This closes the only bootstrap issue introduced by removing the square
horizon. The old proof used the coarser j_i<W bound, which demanded a
larger W; the already present square H^2<W supplies the stronger estimate.

## 3. The existing growth request forces t>=0

In the first scheme, d=16h+2, so |d|>=2 for every integer h. In the
second scheme, d=16h+2 again, so the same conclusion holds. The source's
canonical signed-base power lemma applies to the now oriented request
at this base and index t.

If t=-j<0, its congruence implies F*d^j=1 modulo
T=2Ad-d^2-1. The frame bounds |F|,|d|,j<W and the magnitude of T force
the exact equality F*d^j=1. This is impossible for |d|>=2 and j>=1.
Hence t>=0, and the nonnegative-index case gives the exact equality
F=d^t.

The argument does not require d>0 in advance. The signed-base lemma
uses the ordinary polynomial power congruence and T=-1 modulo d, and
absolute-value bounds. Once t is nonnegative, the stated affine formula
for d will of course make d positive.

## 4. Parity excludes the zero horizon

Suppose t=0. The authenticated growth output is F=d^0=1. The affine
beta multiplier gives y=F(2v+1)=2v+1, an odd integer, of either sign.
The two retained beta endpoints become

    x=2+(y+1)u_0,
    x=1+(y+1)u_t.

Subtracting yields

    1=(y+1)(u_t-u_0).

The right side is even, a contradiction. This proof requires neither
y>=0 nor q>1. It also covers y=-1, when both moduli are zero.

Thus t>0. Its congruence class now gives t>=16 in the first scheme and
t>=8 in the second. The growth value F is positive. All subsequent
signed-radix, digit-recovery and beta-sign arguments may therefore use
these conclusions without a circular dependency.

## 5. Required growth estimates, including the t>=8 scheme

In the first scheme t>=16 and F=(t+2)^t. Therefore F>(t+1)^t and
F>=18^16>2^32. The coefficient-separation and large-evaluation estimates
of the factorial-free front are unchanged.

In the second scheme t>=8 and F=[2(t+1)]^t. Thus

    F >= 18^8 = 11,019,960,576 > 2^32,
    F > (t+1)^t.

The selector argument requires F>L_t^2, for L_t=lcm(1,...,t). Its
elementary bound L_t<=4^(t-1) gives L_t^2<=16^(t-1). In the first
scheme, t+2>=18>16. In the second, 2(t+1)>=18>16. Thus both schemes
satisfy F>L_t^2.

The remaining numerical inequalities used in the inherited proof are:

- F>=7, needed for F^2+F<=2^(F-1);
- F>ell=2^22, so x>=2+(t+1)y with y>=F gives x>ell(t+1);
- x>=F+1>2^32, used in (2x)^(2^23)<2^x;
- t>=2, used in binomial lower bounds and the index-zero exclusion;
- (t-1)F>t, used to deduce 2+t+x+y+F<2x;
- all lower binomial indices t,t+1,y+1,x are at most x, from the same
  two endpoint inequalities once y>=F.

Each follows for both schemes. The label-product coefficient bound is
F>(t+1)^t, not a factorial identity. The isolated-prime-power selector
bound is F>L_t^2, not the older stronger R>(t!)^2 premise. The new
proof must be composed with that independently proved selector theorem.

## 6. Completeness

Start from an arbitrary finite C222 refutation. Pad by the inherited
truth rule to a sufficiently large positive multiple of 16 or of 8,
according to the chosen scheme. This only restricts the freely chosen
horizon to a cofinal arithmetic progression.

The growth base d is even, so v_2(F)>=t>v_2(t!). Choose the odd multiplier
2v+1 sufficiently large and divisible by the odd part of t!. Then
y=F(2v+1) is a positive multiple of t!, exceeds every actual accumulator,
and can be made arbitrarily large. It therefore supplies the same pairwise
coprime beta moduli as the predecessor construction.

The parity arguments for R=F remain valid: v_2(F)>=t implies
v_2(F+i)=v_2(i) for 1<=i<=t, hence B=binom(F+t,t) is odd. Choose an even
beta code x in its CRT class, and choose the CRT representatives with
the inherited parity pattern that makes their actual radix multiplier
H_0 odd and the dominant semantic anchor even. Then q=(BH_0)^x is 1
modulo 4, so the new affine radix parameter z=(q-1)/4 is an integer.

The true growth power, all other powers, normalized remainders, anchor,
Pell frame and remaining certificates are constructed in the same order
as in the independently proved R=F/affine-radix/affine-beta composition.
The new horizon parameter is h=t/16 or t/8 respectively. Thus every finite
refutation extends to a zero of the new ordinary polynomial source.

## Conclusion and claim boundary

The horizon square guard is unnecessary after these replacements. Its
role is recovered from the signed power and endpoint parity. Each choice
has a zero exactly when a finite C222 refutation exists, and hence, through
the retained named logical calibration, exactly when a finite ZFC
refutation exists. The resulting equivalence of integer unsolvability and
Con(ZFC) is formalizable and provable in ZFC.

This is an ordinary mathematical proof. It is not a newly checked
end-to-end Lean/Rocq proof or an object-language ZFC derivation. Literal
endpoint counts require the separately emitted residual lists and exact
finite checks; no count is inferred merely from this proof note.
