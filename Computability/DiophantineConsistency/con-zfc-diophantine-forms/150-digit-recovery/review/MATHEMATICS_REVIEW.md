# Mathematical review of the final digit-first construction

Review date: 25 October 2026.

**Conclusion:** the new weak-product digit-first argument is mathematically
sound, relative to the explicitly retained arithmetic and logical calibration
dependencies. Its completeness restriction on the radix is compatible with
the cofinal CRT construction and the even semantic anchor. The deterministic
Pell comparison center and the all-fourteen linear orientation pool are
compatible with the revised sign-recovery order. No mathematical correction
to the final weak-product source or equation was found in this review.

This is a separate mathematical review pass within the AI-assisted workflow,
independent of the producing compiler. It is not outside human peer review.
The reviewer also participated in developing and writing the new arithmetic
argument. No fresh Lean, Rocq, Isabelle, or encoded object-ZFC kernel proof
has been produced or checked here. The finite artifact verification and the
ordinary unbounded argument have different roles.

## 1. Exact reviewed objects and scope

The principal text reviewed is `proofs/NEW_ARGUMENT.md`, SHA256
`6bd08c8143ff690350509d8530323e628c827a3d6c4bd039f7d7e47a7af4d02f`.
The deterministic-center argument is `proofs/PELL_CENTER_PRIOR.md`, SHA256
`1b5d55a3f5ad1cf8fc5a988d5ae28442abd47fb17bd66eac343e4d619749fec8`.

The inspected literal raw source is
`source/equation247_weak/source.json`, SHA256
`0272cc2d24bc6da6765f830d0a8ce22c96ba2915cd8bd53bf60855f0b67aad59`.
Its final equation file has SHA256
`14b814894521add09fb6847e59de2d802f2e466f6f9fc724f346a21461125a6b`;
the collected polynomial file has SHA256
`394d3cad2834fa94b573c8497ef302053f277478c522e9ec0f14fc55699fc9a6`.

The source was inspected for the actual weak product row, the nontrivial
square-radix row, the reciprocal-index identity, the last endpoint, the
normalized ratio and factorial rows, and the two comparison-center edits.
The complete coefficient expansion, integral projection and translation
checks are documented by the separate finite verifier, not replaced by
this mathematical review.

The actual new guard is

    r*s = a^2+b^2+c*(c+1),

with no added constant one. The raw radix row is

    q - 36*z^2 - 36*z - 9 = 0,

which is exactly `q=(6z+3)^2`. The optional strict-product discussion in
the proof is a separate valid companion; it is not the delivered guard.

## 2. Canonicality and the deterministic center do not use the new signs

The signed frame bounds actual bases, requested indices and outputs in
absolute value, and makes the Pell center larger than `W^W`. Thus it
does not require positive F, B, q or representative coordinates.

The center replacement uses

    J=C^2(2e+1),
    H^2-(A^2-1)J^2=1,
    f=(1-A)H,
    D=A+Hf=A+(1-A)H^2,
    R=h+C*q_c.

It gives `D=A (mod H)`, `D=1 (mod C)` and `|D|>1` without any
arithmetic-front sign assumption. The retained squared cap gives
`C!=0` and `|h|<|C|`. For a classified anchor index i>=2,
squared-ordinate divisibility yields `|C|` dividing the auxiliary index.
The comparison congruences yield `i=+/-h (mod |C|)`. Pell growth gives
`i+|h|<|C|`, so i=|h|. The exceptional case i=1 is addressed separately:
then |C|=1, the cap forces h=0 and every nonanchor ordinate to vanish,
and the anchor contributes a nonzero small error to the orientation
pool. Divisibility by the much larger |A-1| is impossible. This excludes
the exceptional case without presuming that h is already positive.

**Essential composition clarification:** the final source uses all fourteen
linear abscissa errors `1-X_i`, together with the fourteen squared
ordinate errors. This is enough for full canonical orientation before
any sign bootstrap. Modulo A-1, each classified abscissa has a small
residue `s_i in {-1,1}` and each ordinate has its corresponding signed
small-index residue r_i. The pooled congruence therefore makes A-1 divide

    E=sum_i [(r_i-k_i)^2+(1-s_i)].

Every summand is nonnegative, since `1-s_i` is zero or two. The frame
and the just-proved index bounds give

    0<=E<4*14*W^2+28<4*W^3<|A-1|.

Hence E=0 and every pair is canonical. The same inequality excludes
the exceptional anchor case described above. This all-fourteen proof
is independent of the old ceiling signs. The nine-term selective
orientation schedule in the predecessor must not be substituted for it:
that schedule uses arithmetic signs recovered in a different order.

For a canonical power request at base n with |n|>=2, the standard modulus
`T=2An-n^2-1` has magnitude greater than `W^W+W`. Both the usual
nonnegative-index congruence and the inverse congruence for a negative
index have differences smaller than |T|. Therefore they imply exact
integer equalities. The latter would say `m*n^j=1`, excluding negative
indices. The argument works at negative bases as well as positive ones.
The cases n=1 and n=-1 give the exact outputs 1 and (-1)^k. Base zero is
excluded explicitly before using the self-radix request.

## 3. The new sign-recovery order is acyclic

The following order was checked without invoking the weak product early.

1. The square radix gives q>=9. The genuine q^x request forces x>=0
   and yields M=q^x. The canonical t and t+1 powers are already available
   because t=16+h0^2>=16.
2. The retained row `q^(t+1)*v_tp=q^x`, with integer v_tp, forces
   x>=t+1>=17. This is divisibility of positive powers, not a sign
   assumption on a quotient. If x<t+1, cancellation would make an
   integer multiple of q equal to one.
3. The numerator requests at base q+1>=10 force every actual CRT
   representative to be nonnegative. In particular C0>=0 and H0>=1.
   The literal identity `B*mu=F^2+C0+1>0` excludes B=0 even though
   mu is unrestricted.
4. The self-radix base BH0 is nonzero. Bases of absolute value one
   would give an output of absolute value one and contradict q>=9.
   Otherwise canonicality gives `q=(BH0)^x=|BH0|^x>=2^x`.
   Since x>=2, it also gives `B^2<=q`, hence `|B|<q/2`.
5. Let m=F^2 and n=m+t. Canonicality gives V0=(m+1)^t and
   y=V0(V0-1)>=0. The last endpoint, together with x>=17, forces its
   integer quotient to be at least one and gives x>=2+(t+1)y.

For m=0, n=t<=x-1. For m>=1,

    (m+1)^t>=1+mt>=m+t=n,

because (m-1)(t-1)>=0. Also V0>=2, so y>=V0>=n. Thus again n<=x-1.
Consequently `2^n<=2^(x-1)<=q/2`, uniformly for F=0 and either sign
of F. No case was discarded by assuming the desired positivity.

## 4. The binomial digit determines B, then the weak guard suffices

The exact numerator is `(q+1)^n`, with n=F^2+t>=t. Its canonical low
part below q^t is

    rho=sum_{j<t} binom(n,j)*q^j.

The entire binomial row sums to 2^n, so

    0<=rho<q^t/2,
    0<d=binom(n,t)<q/2.

The normalized factor v_t=M/q^t is positive. Its canonical normalized
remainder v_t*rho is less than M/2, while the common norm gives
`|R_f|<M/2`. They are congruent modulo M. The difference has absolute
value smaller than M, so they coincide exactly. After division of the
factorial row, `B=d (mod q)`. Because `|B|<q/2` and `0<d<q/2`,
`|B-d|<q`; therefore B=d>0.

Only at this point is the weak product row interpreted. It gives rs>=0,
and the retained identity gives r+s=B-1>=0. These force r,s>=0,
including the cases where either is zero. The ceiling then gives
BF=V0+s>0 and hence F>=1. Since V0>F^2, B>F and B>=2. The exact
self-radix gives q>B, restoring o=q-B-1>=0.

Thus all three old scalar guards admit fresh ternary witnesses. The
original factorial fixed-point theorem, range-remainder recovery and
Horn-flow interpretation now apply. The proof does not replace a weak
guard by a strict inequality, and it does not need the optional strict
completeness estimates to validate the delivered equation.

## 5. Cofinal completeness and parity compatibility

The new radix restriction is a restriction on admissible witnesses, so
it needs more than a soundness argument. The stated reconstruction
supplies the required completeness.

For canonical F=t!, every i<=t divides F, and 6 divides F. Thus
`F^2/i=F(F/i)` is divisible by six. Each factor `1+F^2/i` is 1 modulo
six, giving B,N,N^2 all congruent to 1 modulo six. Since y is even,
the beta-CRT moduli are odd; x can be chosen even and arbitrarily large
in its beta residue class.

Each independent representative may be shifted by multiples of N^2.
Because N^2=1 modulo six, one nondominant representative can prescribe
H0=3 modulo six, while remaining positive and at most 6N^2. Choosing
the dominant a between 8N^2 and 10N^2 with parity opposite to b keeps
the semantic index h even and gives h>=128N^4. This dominates every
modified ordinary representative and every retained fixed front index.
It therefore preserves the squared-cap and odd-auxiliary completeness
construction. The self-sized radix is chosen after these representatives,
so the increased constants do not invalidate an earlier fixed radix bound.

Now BH0 is an odd multiple of three. Its positive power
`(BH0)^(x/2)` is again an odd multiple of three, hence equals 6z+3
for an integer z. This proves the new square row without requiring an
exact 3-adic valuation. Canonical r,s are nonnegative, so their product
has the required ternary representation. The parent's stronger normalized
remainder margins supply the common norm. The deterministic comparison
center uses the same newly chosen even semantic anchor and fresh auxiliary
Pell witnesses, so it adds no incompatible CRT constraint.

## 6. Inherited dependencies and limits of the conclusion

The ordinary argument depends on these exact included interfaces:

- `source/inherited_common/upstream/round17/direct/PROOF_315.md`:
  signed frame, squared semantic cap, Pell divisibility and cofinal
  even-anchor witness construction.
- `source/inherited_common/upstream/round17/direct/ORIENTATION_FIRST_PROOF.md`:
  bounded-error canonical orientation and the power-congruence argument.
- `source/inherited_common/upstream/round17/direct/STRICT_BUDGET_PROOF.md`:
  K=x amplification, strict beta quotient ranges and the retained decoding
  majorants.
- `source/inherited_common/proofs/NORMALIZED_REMAINDERS_PROOF.md`:
  the normalized numerator and ratio equations, centered-norm recognition,
  the canonical 1/32 completeness margin and recovery of the ten range
  digits.
- `proofs/PELL_CENTER_PRIOR.md`: deterministic comparison-center
  construction, weaker ordinate modulus and exceptional-index exclusion.
- The retained architecture proof chain, including
  `INHERITED_FACTORIAL_CARRIER_PROOF.md`,
  `INHERITED_SELF_RADIX_PROOF.md`,
  `INHERITED_DERIVED_LABEL_RANGE_PROOF.md` and
  `INHERITED_ROUND15_UNIFIED_PRODUCT_PROOF.md`, under
  `source/inherited_common/upstream/round17/architecture/proofs/`:
  factorial fixed point, CRT arithmetic, range extraction and their
  connection to the numerical calculus.
- The retained calibration sources under that directory's
  `inherited/calibration/`, particularly `KEndpoint.lean` and
  `ConstructibleChoice.lean`, for the named interfaces
  `KEndpoint.c222_iff_zf_refutation` and
  `ConstructibleChoice.zf_refutation_iff_zfc_refutation`.

These inherited statements were not all rederived from axioms or rebuilt
through their complete transitive proof-assistant imports during this review.
The new result is an ordinary mathematical proof formalizable in ZFC,
composed with the named inherited calibration. The included Lean sources
are provenance and dependency evidence, not a newly checked full kernel
certificate for the final 247-variable polynomial.

The all-fourteen linear orientation clarification in Section 2 is essential
when presenting the complete composition. Apart from making that interface
explicit, no correction to the new mathematical argument is requested.
