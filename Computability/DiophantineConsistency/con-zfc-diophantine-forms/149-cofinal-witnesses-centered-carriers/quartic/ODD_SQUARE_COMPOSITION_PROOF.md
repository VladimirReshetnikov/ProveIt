# Odd-square radix composed with the common-remainder system

## Exact scope

The authenticated starting point is the 252-variable, 182-row integer quartic
in the incoming Common Remainders and Radix 47 archive. Its full ordinary
arithmetic proof, constructor, independent checker, and exact source data are
retained under `source_closure/common_remainders/`. The optional odd-square
radix lemma is credited to section 7 of the incoming Shared Certificates
Round 18 signed proof, copied as `source_closure/ODD_SQUARE_PARENT_PROOF.md`.
The present step composes these two previously separate improvements. No
new end-to-end Lean verification or consistency proof is asserted.

Write q for the actual radix, B for the exact-binomial output, F for the
factorial output, t for the horizon, V=(F^2+1)^t, H for one plus the sum of
the nine actual CRT representatives, and x for the beta code. These are
semantic quantities, not necessarily the identically named shifted final
coordinates. In the published 252-variable source q=x107-1, B=x5,
t=x0, V=x6, and the actual beta base y=x2-1.

## 1. The literal change

Replace only row 179, whose label is `domain_guard.2`:

    -2 - x5 + x107 - x243^2 - x244^2 - x245 - x245^2 = 0.

The three private coordinates x243,x244,x245 occur nowhere else. Remove
them, add one unrestricted integer z, and replace that row by

    x107 - 2 - 4z - 4z^2 = 0.

This is exactly q=(2z+1)^2. All other 181 rows, including both retained
ceiling guards, all power requests, the frame, pooled orientation constraints,
the endpoint equations, all normalized digits, the three ratio equations,
and the common remainder norm, are unchanged apart from injective renumbering.
The new source has 250 variables and 182 quadratic rows.

This edit is NOT an affine bijection of all old and new solution tuples:
it imposes an odd-square choice of radix, and it deletes three nonunique
ternary witnesses. Its proof is a soundness restoration and a cofinal
completeness construction. Subsequent row operations and affine coordinate
projections are genuine universal integer-zero-set bijections.

## 2. Soundness: recover q>B without the deleted guard

The signed-frame, squared-anchor, and pooled-orientation arguments are
unchanged and precede any use of the deleted guard. They yield canonical
principal Pell pairs. Since t>=16 and F^2+1>=1, the designated t-index power
request gives V=(F^2+1)^t, including the base-one case. The two retained
ceiling guards give the old ceiling interface. Exactly as in the parent
proof, this implies F>=1, B>=2, V<B^2, and y=V(V-1)>F+2. The last identity
is an actual residual, not merely a choice in the completeness proof:
the unshifted `cofinal.beta_base` row is y+V-V^2=0.

The new odd-square row gives q>=1 and hence q+1>=2. The existing numerator
requests at base q+1 force the nine actual representatives to be
nonnegative, by the parent's negative-index power lemma. Hence H>=1.
The existing x-index request at base BH>=2 now yields x>=0 and
q=(BH)^x. The first endpoint rules out its quotient u0<=-1, since then
x<=F-y<0. Thus x>=F+1>=2. The last endpoint gives the same inherited bound
x>=2+(t+1)y. It follows that q>=B^x>=B^2>B. This recovers the missing
strict output-slack bound before exact-binomial interpretation.

Consequently every hypothesis needed by the Common Remainders proof has
been restored in an acyclic order. In particular the existing output powers
N=B^x and q^k are exact positive integers; the four relevant denominators
are positive divisors of M=q^x. The normalized digit equations and the
single norm guard then reconstruct the ordinary remainders exactly.
The original q-B-1 ternary guard can be restored because q-B-1>=0 and
a^2+b^2+c(c+1) represents every nonnegative integer. No discarded remainder
sign or deleted output-slack sign was used to justify its own recovery.

## 3. Completeness: parity choices preserve the common norm argument

Start with a finite C222 refutation and the common-remainder parent's
cofinal witness construction. Here y=V(V-1) is even. Therefore the beta
moduli 1+(i+1)y are odd. Adding a sufficiently large odd common CRT modulus
allows x to be even while preserving all beta values and nonnegative
endpoint quotients.

After F=t!, the factors of B are odd, so N^2 is odd. Actual encoded CRT
representatives may be varied by multiples of N^2 without changing their
required residue classes. Choose the prescribed opposite parities of a,b
used by the signed semantic anchor. Independently set the parity of one of
the other seven representatives so that their total sum is even. Thus
H is odd. The dominant representative can still be selected between 2N^2
and 4N^2 with its required parity, while each other representative is at
most 2N^2; the parent's dominance and amplification bounds survive.

Now BH is odd and x is even. Define R=(BH)^(x/2), an odd positive integer,
and z=(R-1)/2. Then q=(BH)^x=(2z+1)^2. These choices do not alter the
common-remainder proof's coefficient estimates: all eleven genuine low
remainders still satisfy 0<=r_i<L_i/32; with v_i=M/L_i, the normalized
remainders R_i=v_i r_i satisfy

    4 sum_i R_i^2 < (11/256) M^2 < M^2.

Hence M^2-1-4 sum_i R_i^2 is nonnegative and has its retained ternary
representation. All normalized digit and ratio rows remain satisfied.
This gives an integer zero of the 250-variable source.

## 4. Calibration and finite checks

The two directions compose with the inherited C222/ZF/ZFC-refutation
calibration. Thus ZFC proves that the new source has an integer zero iff
there is a finite ZFC refutation; negating gives unsolvability iff Con(ZFC).
The argument does not decide either side.

`check_source.py` independently checks the old guard's exact shape,
privacy of all three discarded variables, the new odd-square identity,
all 181 untouched rows after exact renumbering, domain preservation, and
coordinate liveness. It imports no builder. Two deliberate corruptions
must be rejected. `build_source.py --check` replays the frozen edit
byte-for-byte. These finite checks establish the literal edit, not the
unbounded arithmetic lemmas in sections 2 and 3.
