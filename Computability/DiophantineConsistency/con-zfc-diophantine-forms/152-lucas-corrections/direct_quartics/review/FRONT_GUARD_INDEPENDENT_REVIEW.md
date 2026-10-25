# Independent review of the fused front-sign bootstrap

Verdict: PASS for the ordinary mathematical reduction in
`direct_quartic/BOOTSTRAP_PROOF.md`, as inspected on 25 October 2026.
This review checks the new unbounded argument and its dependency order. It
does not independently certify every emitted projection coefficient and does
not re-prove the inherited C222/ZF/ZFC logical calibration.

The reviewer inspected the new proof and builder, the common-remainder
proof, and its retained `ORIENTATION_FIRST_PROOF.md`,
`STRICT_BUDGET_PROOF.md` and `PROOF_315.md` dependencies.

## Signed powers

The extension to negative bases is valid for either sign of the Pell center.
From W>=258, |A|>W^W and 2<=|n|<W,

    |2An-n^2-1| >= 2|A||n|-n^2-1
                    > 4 W^W-W^2-1 > W^W+W.

The canonical signed-index congruence at n holds because substitution
`s=n-A` gives `s^2=A^2-1` modulo T. The norm of the Pell unit is one,
and T=-1 modulo n, so the inverse at negative index is legitimate.
For k=-j<0, the claimed bound

    |m*n^j-1| <= (W-1)^W+1 < |T|

forces an impossible integer equality whenever |n|>=2. No sign assumption
on n, m or A is hidden here. The base-one case uses the known positive
t-index and gives V=1 if F=0. The fused guard then fails because s=-1.

The inherited frame and anchor orientation really do precede the removed
sign guards: W is a sum of signed squares, the odd frame gives |A|>W^W,
and the squared semantic anchor plus bounded pooled errors fixes both
coordinates at their signed nominal indices. Those steps do not require
B, F, q or the independent representatives to have their final signs.

## Negative front branch

The positive right side of `(r+1)(s+1)=1+G` leaves exactly the two integral
branches r,s>=0 and r,s<=-2. In the latter, B=-b<=-3. The ceiling identities
exclude F>=0. Writing F=-f<0 gives

    bf+2 <= V < (f+1)b,
    V=(f^2+1)^t > (f+1)^2.

Consequently b>f+1 and V<b^2. This is the required early size bound;
neither factoriality nor binomial interpretation was used to obtain it.

The odd-square radix gives q>=1, enough to authenticate the independent
representatives at base q+1 and hence H0>=1. The B^x request, with |B|>=2,
forces x>=0 even if q initially equals one. The endpoint equations then
exclude x=0 and x=1, using 0<|F|<y+1, and force

    x>=2+(t+1)y>=8.

The (BH0)^x request gives q=(BH0)^x. Its positive output makes x even in
the negative-B branch. Thus in both branches q=b^x H0^x and N=b^x>0.
All required common denominators are now genuinely positive powers of q.

The factorial binomial low remainder is strictly below D0/32 by V<b^2
and q>=b^x. The common norm therefore recovers it exactly, even before
B's sign has been settled. This gives B congruent modulo q to the positive
binomial C. Since

    |B-C| <= b+C <= b+V < b+b^2 < q,

the congruence forces B=C>0. The negative branch is impossible. This also
recovers q-B-1>=0, allowing restoration of all three deleted old guards.

## Completeness and parity

The odd-square restriction has a constructive cofinal solution family.
After the original factorial construction, F is even and i divides F for
1<=i<=t. Hence each `1+F^2/i` is odd and B is odd. The beta moduli are
odd because y=V(V-1) is even; an odd CRT period permits choosing x even.
Then N and N^2 are odd. Adding N^2 to a representative changes its parity
without changing its CRT class. A representative other than the two that
determine the dominant-anchor parity can therefore be chosen to make H0
odd. The original choice of the dominant a, with parity opposite b, still
makes the anchor even and preserves its size margin. Thus `(BH0)^x` is an
odd square, and its square-root coordinate exists integrally.

Finally old r,s>=0 give `rs+r+s>=0`, so the ternary representation fills
the new fused guard. Completeness does not require the old private witness
tuples to survive unchanged; it constructs another valid cofinal tuple.

## Conditions that must stay explicit

1. The sign-fusion row alone does not imply r,s>=0. The negative branch is
   excluded by the retained signed-power and exact-binomial architecture.
2. The B^x request is needed before using q>1; using a base-q negative-index
   argument while q might equal one would be circular.
3. The strict, K=x endpoint version is essential for the stated x-bound.
4. The signed-center proof needs |A|, not an unstated assumption A>0.
5. The denominator signs and low-digit bound must precede the binomial sign
   conclusion, as they do in the inspected proof.
6. The semantic transformation proves equivalence of existence, not a
   bijection of all old private witnesses.
7. The directory name `bootstrap247` is not a verified variable count. The
   author reports the current emitted projection has 248 variables; final
   labels and counts must come from the independently checked artifact.

No mathematical defect was found in this scoped proof review. The new step
can be composed with the identified inherited ordinary calibration, subject
to binding the final emitted equation to the inspected raw transformation.
