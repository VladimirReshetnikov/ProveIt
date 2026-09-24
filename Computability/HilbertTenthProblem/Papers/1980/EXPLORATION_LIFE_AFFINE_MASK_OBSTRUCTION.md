# Life cannot be recognized by auxiliary-free affine binary masks

The compact Rule 110 relation tests a fixed bit of an affine combination
of its local input and output bits. That exact strategy cannot express
Life using only its neighbor count, center bit and output bit. In fact,
no finite conjunction of fixed binary bit tests on affine forms in those
three quantities works. This is a restriction on a representation class,
not a lower bound for arbitrary Life arithmetic or universal certificates.

## 1. A seven-point lemma for a binary digit

For any integer z and h=2^k, define its kth binary digit by reducing z
modulo 2h: the digit is zero on [0,h-1] and one on [h,2h-1]. This
definition also covers negative integers without a sign convention for
their written expansion.

**Lemma.** The kth binary digits of any seven-term integer arithmetic
progression cannot be 0001000.

Suppose the middle value has residue h+t, with 0<=t<h. Write the step,
reduced modulo 2h, as h+e with -h<=e<h. The immediately preceding and
following values both have digit zero. Their residues are t-e and t+e,
respectively, so both must lie in [0,h-1]. Consequently

    |e| <= min(t,h-1-t).                             (1)

If e=0, either value two steps from the center has the same residue h+t
as the center, a contradiction. If e>0, the value two steps before the
center has unreduced residue h+t-2e, which lies strictly between zero
and 2h by (1). Its zero digit implies 2e>t. The value three steps before
the center has residue t-3e modulo 2h. We have

    -h <= t-3e < 0,                                 (2)

because 2e>t gives the strict upper bound, and
3 min(t,h-1-t)<=h+t gives the lower bound. The latter inequality follows
by using t when t<=h/2 and h-1-t when t>=h/2. Equation (2) puts the
normalized residue in [h,2h-1], a contradiction. If e<0, reverse the
progression and use the same argument. This proves the lemma.

Complementing a digit is the same as applying that digit test to -z-1.
Thus the pattern 1110111 is impossible as well. Equivalently, if an
affine integer expression has one prescribed binary digit at positions
0,1,2,4,5,6, it has that same digit at position 3.

## 2. Apply the lemma to Life

Let n in {0,...,8} be the number of live neighbors, b in {0,1} the
center cell, and y in {0,1} the claimed output. Life requires

    y = 1 iff n=3 or (n=2 and b=1).                 (3)

Consider any proposed local condition consisting of finitely many tests

    digit_(k_j)(a_j + d_j n + e_j b + f_j y)=epsilon_j,
    epsilon_j in {0,1},                             (4)

where every coefficient, digit index and prescribed digit is a fixed
integer. Different tests may use different affine forms and different
binary digit positions. A usual zero-mask condition L & M=0, or an
equality L & M=V with fixed M,V, is a conjunction of such tests.

For b=y=0, the six counts n=0,1,2,4,5,6 are valid Life transitions.
Each test in (4) must accept them all. The seven-point lemma forces
that test to accept n=3 as well. Hence their entire conjunction accepts
(n,b,y)=(3,0,0), contrary to (3). This proves the claimed impossibility.

Ordinary interval bounds on any of these affine forms do not repair
the problem: the value at count 3 lies between its values at counts 2
and 4. Bounds satisfied at both endpoints also hold in the middle.
The same observation covers affine equalities and inequalities added
to the conjunction. It does not cover arbitrary nonconvex membership
tests, disjunctions, auxiliary choices or nonlinear forms.

The theorem concerns forms in the aggregate count n. It does not analyze
affine forms with independent coefficients for the eight named neighbors,
or a representation that exploits constraints between adjacent cells.
Nor does it establish an optimal number of auxiliary planes. The existing
five-plane Life relation remains a valid component; this result only
rules out replacing all its auxiliary choices by the specified mask class.

## 3. Finite checks and scope

The companion checker exhausts all progression origins and steps modulo
2h for h=1,2,4,8,16,32,64,128. It checks both excluded patterns and the
closure formulation. The proof above covers every k, not merely those
finite moduli. A short progression at modulus 16 has digits 00100,
so an analogous five-point claim would be false.

The checker also evaluates the exact Life truth table, exhibits the six
valid and one invalid transition used by the argument, and checks the
affine interval identity. No mask operation is being treated as a free
arithmetic primitive: these tests describe the logical representation
whose eventual arithmetic implementation was under consideration.

Review status: author and two independent complete scoped proof/source
reviews and fresh receipt checks PASS.
