# Bounded compatibility check: odd affine horizon in incoming Pell-growth210

Status: rejected as stated. No sealed212 artifact was changed and no new
endpoint is claimed. The source is the Pell-growth210 archive inspected at
late snapshot c8187221a60df5baa0047c254a592a014491b60c.

The replacement t=2h+1 permits t=-1. In the signed bootstrap, x=0 can no longer
be excluded by the last endpoint: its multiplier 1+(t+1)y is then exactly1.
Consequently the self-radix power gives q=1, and the q-pool is a unit-base
pool. It does not force its t index to be nonnegative.

There is a concrete semantic degenerate witness pattern. Put delta=2^19,
F=Y_delta(3), X=X_delta(3), Z=-F, and
u_growth=(-F/delta-1)/2. The standard odd-center valuation gives
v2(F)=19, so u_growth is integral. With t=-1 these satisfy

    Z=tF,
    X^2-16Z^2-8ZF=1,
    F=delta*t*(2u_growth+1).

Now set

    y=F, x=0, q=1, B=N=1, C=F+2,
    u0=ut=-1, beta_odd_multiplier_half=0,
    eta=C+F+1, D_radix=2(C+F+1).

Both endpoint equations hold exactly. C is positive even and the selector
B*eta=C+F+1 holds. The retained true powers N=B^x and q=D_radix^x are both1.
Every q-power output is1, including its signed index t=-1. Every q+1 power
has nonnegative index: F+t=F-1, C=F+2, y+1=F+1, x=0, and all ordinary
representative indices below.

Take all eight ordinary actual representatives a,b,c,d,S,S',u,vq to be0
(the stored shifted a coordinate is1). Both local beta errors are0, and
the truth factor S-S'=0 makes the local Horn product vanish. Thus its
nonnegative-quotient equation has quotient0. N=1 makes all required
local congruences automatic. Every q-denominator is1. All normalized
remainder coordinates may be0; their ratio coordinates are1, their range
quotients absorb the corresponding powers of2, and the first high quotient
is 2^(F-1)-1. The common remainder norm has M=1 and zero guard slack.

C=F+2 exceeds all other absolute nominal main-Pell indices, including
|t|=1, F+t=F-1 and y+1=F+1. The standard positive shared-frame and even-C
private-anchor completeness construction therefore supplies the remaining
Pell witnesses. The negative t pair is simply its canonical signed index-1
pair; its norm, cap magnitude and orientation divisibility are valid.
All ordinary circuit wires are evaluated from these values. This argument
uses exact gadget completeness, not a numerical search or a constructed
expanded209 polynomial.

Hence the proposed horizon substitution introduces an unconditionally
constructible degenerate branch. Any safe dimension reduction must exclude
it by an additional argument or change; the suggested bootstrap alone does
not do so. This bounded test ends here rather than starting a new search.
