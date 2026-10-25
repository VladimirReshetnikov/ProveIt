# Independent review of the changed arithmetic source

## Decision and exact object

Accepted as an ordinary mathematical, existence-preserving source change,
subject to the same explicitly inherited Pell/index and C222/refutation
calibration interfaces as its parent. No new defect was found in the
sign order, boundary cases, or constructive witness choice.

Reviewed child: `research/minimal_all/raw_source.json`, SHA-256
`0b977e5a6e5b0a7dfb9b9a05da14810e3746826d417e25a83c25e0fc11ae469a`.

Reviewed parent: the incoming factorial-free source
`direct/factorial_free_affine/raw_source.json`, SHA-256
`7b2d75791f10c717bbadca278e78e9f315508d56acdc8ad3eb82b63ddbb2e855`.

The child has 381 residual rows in its unprojected 560-slot source table;
some slots are deliberately unused and removed by the later projection.
The review below is not a separate certification of the final projection
metrics or expanded quartic. Those require their own complete coefficient
and restoration checks.

## Mathematical changes checked

The actual revised meanings are

    t=16+4h^2,             F=t^t,
    R=F,                  C=2c,
    H=2+4(C+A_1+...+A_8),
    y=F(2v+1).

The private condition q=(2z+1)^2 is deleted. These are five coordinated
changes rather than identities on all old assignments. Soundness and
completeness use the new proof, not a false all-zero bijection to the
old odd-square source.

The sharpened multiplicity lemma is valid at F=t^t. First, equal products
must contain the same m<=t nonunit factors because otherwise their sizes
force F+1<=t^t=F. Every coefficient of a product of m factors 1+jZ, with
1<=j<=t, is a positive integer at most t^m. Thus the difference of two
matched coefficients has absolute value at most t^m-1<F. The lowest
nonzero coefficient cannot vanish modulo F. Polynomial identity and
unique factorization then give exactly the label balance required by
the inherited Horn-flow argument.

The linear radius is justified by the proved elementary bound
lcm(1,...,t)<=4^(t-1). Consequently R=F=t^t>=16^t>lcm(1,...,t)^2.
This is precisely the hypothesis of the inherited prime-power CRT
compiler. Its full-support completeness, as well as row-selector
soundness, survives without any square-radius premise.

## Ordered sign recovery

The potentially circular part was checked in the following order.

1. The growth request has base and index t>=16. It authenticates positive
   even F=t^t. Since t is divisible by four, v_2(F)>=2t.
2. C=2c and the literal raw row B*h_B=C+F+1 make B odd and nonzero,
   independently of the sign of C or the intended binomial meaning.
3. H is 2 modulo 4 at every integer assignment, so |H|>=2. The existing
   request at base BH therefore gives x>=0 and q=(BH)^x.
4. The affine beta row gives |y|>=F. Thus |1+(t+1)y|>1, and the last
   endpoint rules out x=0 even when y is still signed. Hence |q|>=2.
5. The already present request q^(y+1) forces y+1>=0. Combined with
   |y|>=F>1, this proves y>=F>0. The first and last endpoints then give
   x>=F+1 and x>=2+(t+1)y, respectively.
6. Now |q|>=2^x>=4, so |q+1|>=2. The requests at q+1 force all actual
   CRT representatives nonnegative. This is where their signs are used
   for the first time; H is consequently a positive majorant.
7. The signed-binomial low-polynomial estimate, using Q=|q|, gives the
   true first remainder below Q^t/32. The shared norm bounds its proposed
   remainder below Q^t/2. Integer congruence and strict separation make
   them equal. Reducing the resulting digit equality modulo q and using
   |B|<Q/2 forces B=binom(F+t,t)>0, then q>0.

The q=-2 possibility is harmless because step 5 precedes any attempt to
use the q+1 requests. After step 5 the much stronger endpoint lower bound
rules out every small or unit radix. The cases x=0, y<0, B=0 and negative
q are all explicitly covered; they have not been silently discarded.

## Constructive completeness and anchor compatibility

Choose a cofinal t=16+4h^2 after the finite proof data. Let F=t^t. A
positive odd multiplier w can be chosen arbitrarily large and divisible
by the odd part of t!, so y=Fw is an even multiple of t! and exceeds all
finite pending accumulators. This gives pairwise coprime odd beta moduli
and permits a sufficiently large even beta code x.

For B=binom(F+t,t), the identity v_2(F+i)=v_2(i), 1<=i<=t, proves B odd.
Thus the representative modulus N^2=B^(2x) is odd, and every independent
representative has freely adjustable parity. Choose C even; the parent's
actual completeness construction already did so. Choose the dominant
schema representative a odd and large, with b and the other seven
representatives even. The unchanged identity h_*=1+a+b modulo 2 makes
the semantic anchor even, while h_*>=2a^2 supplies its dominance. The
changed binomial upper index obeys F+t<=B<N^2, so it fits the same bound.

The new H is positive and even, so the chosen q=(BH)^x is positive and
even. The retained exact-power certificates allow this. The removed
odd-square row was the only condition in this changed source that would
require odd q. All requests, scaled digit equations, common norm gap and
private Pell witnesses can then be filled in the inherited order.

The boundary y=F remains excluded after row decoding by the same exact
zero-accumulator argument: the initial accumulator would be zero, all
positive-weight updates would preserve zero, and the final endpoint
would require one. Thus the target weight F+1 is correctly represented.

## Literal occurrence coverage

The independent `audit_changed_source.py` uses a separately written
sparse-polynomial implementation and imports no producer module. It
reconstructs the complete child from the parent using only the stated
semantic substitutions and three named row deletions. It checks all
381 surviving rows, all coordinate-name changes, all three retired
coordinate occurrence lists, and that every residual remains quadratic.
Eleven surviving rows change; all other rows are identical.

It also rebuilds the eighteen actual power requests and all 37 frame
atoms independently. The retained raw slot d has an explicit affine row
d=t. Its square and the t square both remain in the common frame. This
duplicate is legitimate and only strengthens the old absolute bound;
no power request atom is omitted. The checks pass in normal and optimized
Python; both receipts bind the exact child hash above.

The separate arithmetic diagnostic script checks the lcm recurrences,
coefficient bounds, small-label multiset injectivity, full prime-power
coverage, affine-beta edge cases and two deliberately invalid shortcuts.
These finite diagnostics support transcription and boundary handling.
They do not prove the unbounded arithmetic theorems or consistency.

## Scope of acceptance

The new proof establishes equivalence between integer zeros of this
revised arithmetic source and finite refutations of its calibrated
numerical calculus. Composing the inherited ordinary C222/ZF/ZFC
calibration yields the intended consistency equivalence in the same
sense as the parent. This review neither supplies a new complete Lean
or Rocq build nor proves the consistency of ZFC. Novelty is relative to
the inspected source lineage; no literature-wide priority or global
optimality claim is made.
