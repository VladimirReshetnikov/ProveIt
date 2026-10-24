# Ordinary peer: the shorter positive projection numerator

**PASS.** I independently read the complete ordinary proof at
`candidates/ten-positive-short-projection/PROOF.md`, SHA256
`b07dde3b74d9862dc5387bd7a8941a01f928dd1778e78731d08d620c980a8117`.
Its copied weighted parent proof is byte-identical to the accepted final
`92d260efefbda2fd5a0fceda7a093b6175c6876ef9385afc74a5484e335123d1`.
No gap was found in the positivity chronology, composite-modulus argument
or positive completeness map. The literal101-operation count and complete
fixed coefficient payloads remain separate author/root verification scope.

Use the full Pell parameter A, H=4A-5, and write
Kold=X*(X+2*(A-2)*c)-1. The new numerator satisfies the exact identity
Kpos=X*(3*c-2*X)+2=H*X*c-2*Kold. H is positive and odd at every positive
input. Therefore H dividing P*Kpos is equivalent to H dividing P*Kold:
the only cancellation is2 modulo the odd H. P may share factors with H.
For example H=15,P=3,Kold=5 shows why cancelling P would be invalid;
the actual argument never does so.

The new term need not be positive at arbitrary positive inputs, and the
proof correctly waits. Rational-root extraction and the all-index folding
use unchanged radicands and the weighted noncancellation lemma, without a
sign premise on Kpos. First-index exclusion gives
c>8*X*mu^2*Y^2>2*X before the transport argument. Now 3*c-2*X>c>0, so
Kpos/H is positive exactly when the bad-Bt argument drops its negative
contribution. The remaining rational rho and weighted root bounds are
unchanged. Thus positive transport, mask/rank recovery and odd p precede
q parity and all denominator coprimality uses as in the parent.

After parity the integral center supplies H dividing P*Kpos. The exact
identity above supplies H dividing P*Kold without assuming P a unit.
The old whole-product bound applies to the same front data and the same
old projector; it forces X=2^R rather than choosing a factor separately
modulo each prime of H. This gives H dividing Kold, hence H dividing Kpos,
and the remaining partial fractions and fresh positive source restoration
follow. The proof does not assume that arbitrary new zeros have a
pointwise positive old n coordinate.

For completeness, every old positive zero has the positive integer
kappa=Kold/H. The exact identity

    3*Kold-H*X*c=3*(X^2-1)+(2*A-7)*X*c>0

uses only X>=32,A>4,c>0. Hence n_new=n_old+3*kappa-X*c is a positive
integer and is strictly larger than n_old. All other inputs, all radicands
and all transport data remain fixed. The complete center numerator obeys
H*n_new+Kpos=H*n_old+Kold, so the two Z values and final norm outputs are
identical. This applies to every old zero, with any signed conjugate factor.
The reverse existential direction uses the soundness/source theorem and
fresh old canonical witnesses; it claims no positive inverse input map.

I also independently derived a quantitative leading-component check for
the two stated scalar recipes. At equal input tuples the center correction
Delta Z0 has degree at most17. The parent bounds are deg(Z0)<=25,
deg(M)=13,deg(V)=24,deg(delta)=30. Thus the correction to
omega=delta*Z0^2+2*delta*Z0*M*V-M^2*(V^2-1) has degree at most84, below
the parent's unique degree92 term. In the centered octic, put
u=9*delta*M^2*Dtau,v=delta*M^2*Df,w=M^2*Dnum. Their degrees are74,76,104.
The inner square expression is
(omega-u-v)^2-4*w*(u+v)-4*u*v, of degree184, and its correction has degree
at most176. Its squared correction to the final polynomial has degree
at most360. The correction in the last product64*(w+omega)*w*u*v has
degree at most338. Therefore the whole old/new polynomial difference has
degree at most360<368: the entire degree368 component, not just a sampled
coefficient, is unchanged. This checks the scalar algebra; the author's
literal row map binds that algebra to the counted graph separately.

The separate JSON pins the proof and parent. Independent exact polynomial
collection verifies the three displayed universal identities. Finite
controls include composite H with nonunit P and positive integral
completeness maps; they are diagnostics, not the unbounded proof. No author
candidate, common document, page or Lean file was changed. No Lean build or
historical emitter was invoked.
