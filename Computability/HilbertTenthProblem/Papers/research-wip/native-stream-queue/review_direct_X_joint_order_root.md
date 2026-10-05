# Independent review of joint three-adic parity and the full125 order

PASS, with no correction requested. The uniform parity theorem gives
k even and e odd from the exact repunit/index divisibility interface at
odd d>=3. The new finite order certificate excludes the specified
q=2^d*3^k, R=2*3^e-3 family for authentic d=5^n, 2<=n<=34.
Neither argument settles all exponents or the whole direct-X83 proposal.

## 1. Uniform character argument

The repunit identity with B=2^d gives J=1 modulo8 and J=2 modulo3,
so J=17 modulo24. In particular J is positive, odd and coprime to6.
The supplementary law gives Jacobi(2,J)=1. Quadratic reciprocity,
since J=1 modulo4, gives Jacobi(3,J)=Jacobi(J,3)=-1. These laws
apply to odd composite denominators; J need not be prime or squarefree.

Taking this character in 2^d*3^k=1 moduloJ gives k even. Taking it
in 2*3^(e-1)=1 moduloJ gives e odd. The latter congruence follows by
cancelling3 from J|(2*3^e-3), justified by gcd(J,3)=1. Therefore
e-3k is odd. Its positivity is an additional inherited consequence of
the numerical window, not a consequence of the character alone.

The earlier progression with even c=2^(3d+1), k a multiple of c,
and e=3k+c has even e. It therefore cannot also satisfy J|R under
these hypotheses. This is an additional obstruction to that progression;
it does not revoke its correctly proved canonical and repunit properties.

## 2. Exact full-modulus order and range

The modulus is M=2^125-1, and

    O=2576525686996852656333000
     =2^3*3^2*5^3*41^2*107*10223*184711*842887.

My original fresh scalar checker independently reconstructs this product,
verifies all eight prime factors using a sieve of possible divisors through
918, and computes modular powers by a left-to-right binary recurrence.
This differs from the author's right-to-left loop. It reads neither the
author's source nor any predecessor source or receipt.

Its result is 3^O=1 moduloM, and its eight 3^(O/p) residues agree exactly
with the displayed author table and are all different from1. The order
therefore equalsO: a proper divisor would divide O/p for one of these
primes. No primality or factorization of M is required. The modulus is
125 bits; no giant native exponentiation, binomial witness or compiler
instance is constructed.

For125|d, divisibility M|(2^d-1) and the repunit imply O|k. The inherited
strict size inequality 11k<11+28d contradicts 11O>=11+28d. The exact
threshold is1012206519891620686416535; at d=5^34 the positive margin is
12043637501194505196225489. This covers n=3 through34. The unchanged
previous d=25/order450 certificate supplies n=2, as the author states.

At n=35, k=O is even and satisfies 2k<3d. Hence
3^k<2^(2k)<2^(3d)<3B^3(B-1), verifying the author's partial-test example.
It does not satisfy the full repunit merely by passing this fixed-modulus
test, and no e or source zero has been provided. The author correctly
retains that finite-method boundary and the open uniform odd-offset task.
The LTE example for31 is also correct: the multiplier5^(n-1) has no
factor31, so v31(2^(5^n)-1)=v31(2^5-1)=1.

## 3. Evidence and inherited scope

I read the complete new author proof and helper inertly. The four pinned
predecessor notes supply the already reviewed divisor, window and size
interfaces; their byte and author-declared span authentication does not
claim a new full audit of the ancestral native construction. The prior
order, varying-offset and fixed-offset proofs were read in earlier work;
the authentic-outer source interface was read through line49. The new
proof does not widen those scopes or change a source array.

The root helper is fresh standalone scalar arithmetic. Its normal and
optimized runs passed with byte-identical output before freeze. The
companion receipt binds both frozen author and reviewer evidence. The
author helper was read but never executed or imported by root. No supplied,
archived, committed, predecessor or frozen scientific code was run; no
saved source array was evaluated or used for degree propagation.

The two author remarks retain the even-offset failure and the n35
partial-test boundary. OpenQuestion1 retains the missing all-n argument.
No additional wrong or unproved reviewer claim arose, and no correction
was requested. No new universal operation count is asserted.
