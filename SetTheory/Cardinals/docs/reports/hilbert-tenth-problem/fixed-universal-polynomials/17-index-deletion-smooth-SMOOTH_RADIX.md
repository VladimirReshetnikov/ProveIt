# A smaller radix for the full first-index-deletion counterfamily

This is an optional constructive refinement of the frozen factorial proof
FULL_COUNTERFAMILY.md, whose SHA256 is
dc886e8991e32c331b9135b4ea6b3f73733656be3df6c2aa01576e1732fb83e1.
It changes no candidate source, fixed numeral, input convention, witness
count or arithmetic operation count. The full positive counterfamily and
nonintegral h conclusion are unchanged. This addendum does not mutate the
frozen factorial packet, and does not inherit a claim of independent
review of these newly written bytes.

## 1. Use the actual power-of-five recipe

The genuine compiler has d=5^r (and b an odd power of5), as explicitly
stated in the pinned FIXED_RAW_UNIVERSAL_76_PROOF.md and retained by
complete75_half_binomial_compiler.md. Thus B=2^d; its required B>=16
in particular makes r>=1. This stronger genuine recipe was not needed
by the original factorial proof's number-theoretic step.

For a fixed genuine compiler and any positive ordinary input x, put

    ell=2d, I=ell*x+b, W=2^I,
    hK=ceil(log2(K+1)), H0=max(I,hK).

Choose the least k>=0 for which

    t=4400d*2^k>=4H0.                              (1)

The symbol k here selects the radix height; it is not the first-Pell
coefficient called k in the main proof. To avoid that collision in an
implementation, call it radix_doublings. No extra supplied source
coordinate is introduced.

Then t>=22000>64 and

    t=2^(k+4)*5^(r+2)*11,
    v2(t)=k+4, m=oddpart(t)=275d,
    N=t/d=4400*2^k is a multiple of1100.

The two required Euler periods divide t:

    phi(5^(r+2))=4*5^(r+1),
    phi(11)=10.

Indeed t divided by the first is220*2^k, and divisibility by10 is
immediate. Therefore, with q=2^t=B^N,

    q=1 modulo m.                                 (2)

This replaces the factorial argument completely. It uses the genuine
fixed d and does not select a different radix base B or compiler.

## 2. The same exact CRT and packing construction

Use the unchanged definitions from the main proof:

    J=(q-1)/(B-1), Q=q^2-1,
    M=(MC+q*MF)J, with the literal shifted MF,
    e=M modulo m, e=3 modulo4, 0<=e<4m,
    Z=least positive residue of e-M modulo2^(k+4),
    C=W+Z, F=(K+2^e)C,
    alpha=q-F-2Z-W-ell*x,
    R=(q^2-Z-qF)Q+M.

The exponent representative obeys the stronger uniform bound

    3<=e<4m=1100d<=t/4.                            (3)

The same two reductions as before give R=e modulo t. The1100-block
argument still gives55|J,Q,M,R. The same actual mask residues give
R=3 modulo4. These arguments require neither a factorial nor any new
constraint on the fixed program constants.

## 3. Logarithmic input/constant thresholds suffice for positivity

The original factorial proof used K,W,ell*x<=t as a convenient bound.
That stronger bound is unnecessary. From(1),

    I<=t/4, K<2^hK<=2^(t/4), W<=2^(t/4).

Also Z<=2^(k+4)<=t, and t<=2^(t/4) for t>=64. Combining with(3)
gives

    F=(K+2^e)(W+Z)<2^(t/2+2).                     (4)

Since ell*x<I<=t/4,

    2Z+W+ell*x<=3t+2^(t/4)<=2^(t/4+1).            (5)

For the final inequality use3t<=2^(t/4) for t>=64. Equations(4)–(5)
imply

    F+2Z+W+ell*x<2^(t/2+2)+2^(t/4+1)<2^t=q.

Both exponents on the preceding sum are strictly smaller than t-1
for t>=64. Therefore alpha>0. All genuine pretyping packed-index
bounds remain valid, in particular p=R>5t+5.

We also have I<=t/4<t<p. Consequently the actual input norm and the
shared rho/sigma positivity argument from the main proof remain valid.
No later part of that proof requires the discarded inequalities K<=t
or W<=t: they were used only for the former outer-margin estimate and
to infer I<t, both now supplied directly.

## 4. Full conclusion inherited with the new witnesses

Set u=R/55, which is a positive integer congruent1 modulo4, and use
the main proof's remaining definitions without change:

    p=55u, n=40u, X=2^p, Y=2^(33u-1),
    w=X/q, s=Y/q^3,
    eta=c-kPell*Y, zeta=kPell-eta,
    input delta,rho,sigma at the exact odd index I,
    transport_quotient=1+C(w-2^e)/(q-1),
    the normalized or ordinary positive canonical auxiliary quotient.

Each of the six actual retained factors is still+1 with the same fixed
program numerals and ordinary input. The missing h still has exact
nonzero remainder25u-1 modulo E=XY. Thus the candidates' ordinary
positive input projections still collapse to all positive inputs.

Only the witness-height selection is simplified. Because k was least,

    t=4400d if k=0;
    4H0<=t<8H0 if k>0.

In particular t<=max(4400d,8H0). For fixed compiler constants,
I=2dx+b is linear in x and hK is fixed. Therefore the radix q=2^t
is at most singly exponential in x, up to constants depending on the
fixed compiler. This is a bound on this construction's radix only;
it is not a small bound on all downstream Pell witnesses.

## Primary provenance and evidence boundary

- Original full factorial proof: separate frozen packet
  first-index-attack-20261003, manifest SHA256
  94f45847037067162dd21e77f19e8edc2cc53cb0aa9ca6642e335c5d7c21cbb4
- [Original fixed76 recipe](https://github.com/VladimirReshetnikov/ProveIt/blob/3f4a974a5ddf12c46302fc5d2edafc3730277923/Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_76_PROOF.md)
- [Retained modified75 recipe](https://github.com/VladimirReshetnikov/ProveIt/blob/3f4a974a5ddf12c46302fc5d2edafc3730277923/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.md)

The addendum's new checker tests only exact modular/CRT identities and
finite margin cases. No saved circuit or upstream code is evaluated,
and no giant full candidate tuple is materialized. The mathematical
implication is the uniform argument above and the already frozen full
construction, not the finite tests.
