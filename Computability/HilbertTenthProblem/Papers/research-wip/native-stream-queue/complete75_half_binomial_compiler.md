# Modified compiler masks for the half-binomial75

This note proves the compiler interface needed by the half-binomial
75-operation construction. It is not a separate complete certificate. The
half-binomial kernel, input bridge, exact source, and pre-kernel outer bounds
are audited separately. Their complete composition has passed independent review; see
[the universal75 theorem](../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md).

The change allows one ignored native digit to range from0 through3, adds a
low field-mask bit, and shifts the inverse-packed word by1. A stronger
radix bound preserves synchronization even when the new upper dummy bit
spills into the next radix digit during an unaligned rotation.

## 1. Fixed layout and modified masks

Use the fixed machine, native window compiler, Start selector0, End
selector1, duplicated center-clause bands and four anchors from the
[complete76 proof](../../1980/FIXED_RAW_UNIVERSAL_76_PROOF.md). Retain its
notation R=2^b, B=R^L=2^d, native positions E, K=|E|, center coefficients
c_e, clause mask mu, bands T1,T2 and anchor positions

    u1=M0, u2=3M0, v1=9M0, v2=27M0=Emax.

Retain its optional high monomial in DC, which ensures

    2DC-DR != 0 modulo5.                                  (1)

Choose an existing ignored dummy exponent e_* with e_*+1<Emax. Every
dummy in the current layout has this property. It has center-clause
coefficient zero, is not a selector or anchor, and is not any old tested
field position. The exponent e_*+1 may already be another native position.
No new radix position is added to the word.

Let MC0,MF0 be the complete76 masks. Define the fixed numerals

    MC=MC0-2R^e_*, MF=MF0+4, MF_source=MF+B-1.              (2)

The R-digit of MC0 at e_* is R-2, so subtracting2 clears precisely its
bit1. The new native mask permits digit0,1,2 or3 at e_*, and digits0/1
at every other permitted position. End is still forbidden everywhere
in the remainder. The low bits0,1,2 of MF0 are zero; hence adding4
changes precisely bit2 and gives v2(MF)=2. Thus

    MC even, 0<MC,MF<B-1,
    pc(MC)=pc(MC0)-1, pc(MF)=pc(MF0)+1,
    pc(MC)+pc(MF)=d.                                      (3)

Here pc denotes binary population. The numeral MF_source can exceed B;
it is a source coefficient, not a one-cell native mask. In particular
the old proof's mask range must not be applied directly to MF_source.

Keep b,L,d powers of5. Increase the fixed choice of b until

    R >= max(4(K+2)(2 sum_e c_e+6)+8, 2mu+4, 16).          (4)

The same L chosen in76 already separates all supports; changing b leaves
that geometry unchanged. Since2^b=2 modulo5 for powers-of-five b, the
optional high-monomial choice and(1) remain valid. All choices depend
only on the fixed compiler, never on the varying input.

The executable interface is `new_constants(compile_windows(windows,a))`.
It lazily materializes and returns the NEW MC and native MF together
with the other fixed numerals. The root source applies MF_source=MF+B-1
to that native MF. The sparse layout object's inherited cached MC/MF
retain their baseline meaning for old-layout checks; its `constants()`
method alone must not be used as the new source's compiler export.

## 2. Shifted packing and the exact two-bit population surplus

Suppose q=B^N and J=(q-1)/(B-1), and put

    S'=(Z-1)+qF,
    T_C=MC J+1, T_F=MF J-1, T'=T_C+qT_F.

Then0<T_C<q, 0<T_F<q, and0<T'<q^2-1. Repeated-cell multiplication has
no carries. Since MC is even and v2(MF J)=2,

    pc(T_C)=N pc(MC)+1,
    pc(T_F)=N pc(MF)+1,
    pc(T')=dN+2.                                         (5)

The source's packed index is exactly

    Ridx=(q^2-Z-qF)(q^2-1)+(MC+q MF_source)J
        =(q^2-S')(q^2-1)+T'.                             (6)

The difference of the two expressions before the repunit equation is
q((B-1)J-(q-1)), so this uses no extra arithmetic instruction.

For completeness, the inverse-population fact used here is as follows.
If Lambda=2^n, 1<=S<=Lambda and0<T<Lambda-1, then

    pc((Lambda-S)(Lambda-1)+T) <= n+pc(T),

with equality exactly when S<Lambda and S AND T=0. If S+T<Lambda,
the two blocks are Lambda-S-1 and S+T, and equality is exactly absence
of binary addition carries. If S+T>=Lambda, their populations are
pc(Lambda-S) and pc(S+T-Lambda). The carry out of the n-bit block loses
at least one population unit, and discarding that leading bit loses a
second. Using pc(Lambda-S)=n-pc(S-1) gives an upper bound
n+pc(T)-1-v2(S), strictly below the threshold. The boundary S=Lambda
has index T and is also strictly below it.

Consequently, once the outer bounds and half-binomial kernel supply
1<=S'<=q^2 and pc(Ridx)>=3dN+2, equations(5),(6) give precisely

    S'<q^2, (Z-1) AND T_C=0, F AND T_F=0.                  (7)

There is a real outer boundary absent from76: Z=1,F=q makes S'=q^2.
It is excluded by the recovered population threshold, not by reducing
S' modulo q. Its index is T' and has population only dN+2. Before that
threshold is proved, positivity alone must not be claimed to give F<q.

Conversely any words satisfying(7) have

    pc(Ridx)=3dN+2.                                       (8)

This exact equality holds even when the newly permitted upper dummy
bit is unused by the canonical completeness construction.

## 3. Origin and native words recovered from the shifted masks

The low mask T_C is MC J with the origin unit bit added. Thus(7) makes
Z-1 even, and adding1 to it creates precisely the origin Start bit with
no carries. Every other permitted bit is unchanged. In particular Z
is odd, and Z is native typed in the enlarged sense of Section1.

The End bit remains absent in every Z cell. Once the separately audited
bridge recovers W=R B^(2x), 2x<N, the equality C=Z+W inserts exactly one
End bit with no carry. C is therefore native typed, with Start at the
origin, one End at2x, and a0..3 ignored digit at e_* in each cell.

The high mask T_F contains every bit of MF0 J. At the origin cell its
low three bits are011; at every other cell they are100. All old field
tests therefore still hold. Their soundness does not require the new
low tests to have any semantic interpretation before synchronization.

## 4. Exact field bound and synchronization with the extra bit

The total native coefficient weight per cell is at most K+2. All
unshifted raw coefficients of DC*C+DR*Rword are consequently at most

    (K+2)(2 sum c_e+6) <= R/4-2.                          (9)

The6 allows the four old DC shifts, the optional high monomial, and DR.
All degrees are still below L. The extra dummy bit contributes zero
to every old tested coefficient: doubling an ignored basis contribution
does not change this fact.

For an arbitrary cyclic binary rotation by2^p, write p=b*t+ell,
0<=ell<b, reducing the exponent modulo bLN if necessary. Every original
low native bit has R-residue ell and support E+t modulo L. The added
upper dummy bit has residue ell+1 at e_*+t when ell<b-1. When ell=b-1,
it has residue0 at e_*+t+1. Thus the possible R-digit support lies in

    E*+t modulo L, E*=E union {e_*+1}, E* subset[0,Emax].   (10)

For ell<=b-2 every rotated digit is at most3*2^ell<=3R/4.
For ell=b-1 it is at most R/2+1: one low native bit and one incoming
upper dummy bit. Combining either bound with(9) gives at most R-2.
There are no radix carries in the actual field, and every B-cell is at
most B-2. This replaces the old false claim that every rotated digit is
always0 or2^ell after allowing the extra dummy bit.

Therefore the usual transport congruence identifies supplied0<F<q
with the actual field DC*C+DR*Rword+Yword, strictly between0 and q-1.
The doubled center bands remain separated: T2-T1>2Emax and
L-(T2-T1)>Emax imply that (10) cannot meet both T1 and T2. A uniformly
clean band decodes every selector, copy and anchor exactly as in76.
The digit0..3 at e_* is ignored by all these clauses.

At the origin Start, both unshifted anchor coefficients are1. The old
anchor parity masks still apply in T_F, so both rotated anchor digits
must be odd. For1<=ell<=b-2 every rotated digit is even, impossible.
For ell=b-1 the only possible odd digits lie at the single within-cell
position e_*+t+1; it cannot equal both distinct v1 and v2. Hence ell=0.
At ell=0 the extra upper dummy bit is even and does not affect parity.
Both anchor targets must be populated by original low bits from E+t.
The old unique18M0 difference argument now forces t=0 modulo L.

Thus the temporal multiplier is an actual whole-cell rotation B^h
modulo q-1. Start's top/middle mismatch excludes h=0; the old copy tests,
occupancy propagation and marker-bijection theorem then recover the
same genuine helical computation and unique Start as in76. No Boolean
test has been weakened at a selector, copy or anchor. The new dummy's
four-valued digit is irrelevant to the decoded computation.

## 5. Canonical low field bits and strict raw slack

In a genuine whole-cell-aligned word, the unit R-digit of the actual
field comes only from the temporal predecessor's Start selector.
Indeed DC and DR have strictly positive minimum degree, and the added
dummy exponent is greater than1. This unit digit is therefore0 or1.
Its binary bits1 and2 are zero in every cell. At the origin it is0:
the unique Start is at0 and the genuine temporal stride satisfies
0<h<N, so the predecessor at -h is not Start.

Thus the new first-cell tests at bits0,1 hold; the new bit2 tests in all
other cells hold; and all old tests hold. This establishes the entire
high mask in(7), including its exceptional first cell. It uses the
canonical genuine word's unique Start, not an unproved pre-decoding
uniqueness assumption in soundness.

Canonical extra upper dummy bits may all be0. Even with arbitrary
allowed dummy digits, every native cell lies below B-1 since its support
ends strictly below the unused top radix positions. In particular
C<=(B-2)J and q-C>=J+1. With canonical padding N>2x,

    J>=B^(N-1)>=B^(2x)>2d*x.

Hence the retained raw-bound witness alpha=q-C-2d*x is strictly
positive. Start and its copies make Z=C-W positive. These are the same
strict inequalities used by76; no new input-dependent numeral appears.

## 6. Five-adic control of the actual index

Use the complete76 independent width/height padding: choose h,Htime,N
as sufficiently large powers of5 with Htime>=25, N=hHtime>25d. Encode
the genuine word with every dummy0. For an existing dummy exponent e,
turning on its ordinary LOW bit in cell i changes

    delta C=delta Z=R^e B^i,
    delta F=(DC+B DR+B^h)R^e B^i.

For the complete76 control slots i=4j (0<=j<N/5), and i=1, both shifted
contributions have no cyclic wrap. Subtracting(6) at the two actual word
tuples gives exactly

    delta Ridx=-Gamma B^i,
    Gamma=R^e(q^2-1)[1+q(DC+B DR+B^h)].                   (11)

This may use e=e_*: its low bit still ranges independently over0/1,
and its new upper bit remains0. A second dummy is not required.
All selected bits are ignored by every genuine clause, and the actual
field's low origin digit remains unchanged.

Modulo5, R,B,q,B^h all equal2. The bracket in(11) is2DC-DR, nonzero
by(1). Thus Gamma is a unit modulo dN. The independently proved
[five-adic subset theorem](../../1980/EXPLORATION_FIVE_ADIC_DUMMY_CONTROL.md)
supplies a Boolean subset of these slots with weight sum

    (Ridx_initial-d*h)*Gamma^(-1) modulo dN.

The final, actually packed index therefore satisfies

    Ridx=d*h modulo dN.                                  (12)

There is no factor2 in this target: the new kernel's recovered
main power is2^Ridx. If that separate kernel theorem applies, (12)
makes this exact power the intended temporal shift modulo q-1. The
usual positive transport-quotient lift then applies unchanged.

## 7. Checker and scope

The [checker](complete75_half_binomial_compiler.py) reuses all five
existing complete76 compiler layouts, including both branches of the
fixed high-monomial correction and the layout with only one dummy.
It independently checks the enlarged support, all inner shifts, all bit
residues, the exact R/4 margin, and zero dummy coefficients at every old
test. Small materialized masks check the shifted population identity,
origin recovery and the F=q boundary. A separate exhaustive check covers
the general inverse-population identity through8-bit Lambda. Symbolic
identities verify the source coefficient rewrite and actual-index dummy
change; the existing five-adic selector is replayed on all small targets.

Actual compiler B,q, padded computation words and Pell witnesses are not
materialized. The proof above supplies the parametric compiler argument;
the finite checks corroborate it. No operation ledger or full75 soundness
claim follows from this packet alone.

Review status: author and independent full proof/source/default checks pass.
The independent review covers the spill case, shifted masks, origin and
low field bits, strict mass margin and actual-index five-adic selection.
