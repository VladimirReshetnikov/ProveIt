# Mathematical and software review

Date: 2 October 2026 UTC. Scope: the fixed-radius forward theorem, all finite polynomial corrections, fixed integer depth shifts, coarse certified amplitude, the specified smooth-model inverses, and the qualified discrete threshold enclosure.

## Verdict

PASS. Independent mathematical and software review found no unresolved blocker in the original sources identified by original-frozen-sources.json. The production 2048-panel interval certificate and the exact order-3 coefficient/remainder generator were independently replayed. This is mathematical review and executable interval verification, not proof-assistant formalization. Visual layout and exhaustive bibliographic priority are outside this mathematical review; visual checks are summarized in VERIFICATION.md.

The result is restricted to the certified radius 1/2, fixed depth shifts, and arbitrary but finite expansion order. The logarithmic remainder degree is a finite effective degree, not a claimed sharp bound. A concrete numerical sequence threshold still requires instantiated validity ranges and error bounds or neighboring exact counts.

The attribution-corrected revision preserves the reviewed theorem, proof, inverse section, and executable mathematics. Its source-specific attribution review and revised identities are recorded separately in attribution-review.md and frozen-sources.json.

## Exact residue and slit domain

Lagrange inversion gives [z^n]f^m(z)=(1/n)Res(h^m(u))^(-n), so the factorial and 2^(-n) factors are correct. The principal logarithm maps each open half-plane into itself. Consequently, no off-axis point can map to the negative-real logarithmic cut at any intermediate iterate. On the real axis, the first singular endpoint is f^(m-1)(-1). Within a finite radius the boundary has only finitely many branch points for each finite m.

At a branch point, one intermediate logarithm tends to infinity in modulus, and each of the finitely many subsequent logarithms also tends to infinity in modulus. Thus its final reciprocal tends to zero and is bounded in the relevant slit-side sectors. The tiny indentation integrals vanish. The cut's upper lip runs from -r toward zero; combining the conjugate lower lip indeed gives PLUS (1/pi) integral Im(t_m^n) ds. The large negative real reciprocal before any crossing contributes zero imaginary part exactly, so its large modulus near zero is harmless in this identity.

## Fatou coordinate and entrance

The Stieltjes representation has the correct sign and mass. Its moments agree with the reciprocal-log Laurent coefficients. The estimates for a=T(w)-w and for the logarithmic and reciprocal Taylor remainders are valid at Re w>=4. Cancellation gives defect at most 35/(24 x^3), hence certainly 2/x^3. Summing along Re T^j(w)>=x+11j/12 gives 2/x^3+12/(11x^2)<2/x^2. The normalization lim[T^j(w)-j+(log j)/3] follows from T^j(w)=j+w+O(log j), so no unidentified additive constant remains.

After a negative-cut crossing h=a+i*pi, |2/h|<=2/pi. One additional logarithm has real part at least log(pi) and imaginary part in (0,pi), placing its reciprocal in a fixed right-half-plane cone. The logarithmic-mean representation preserves that cone and proves |T(w)|<=T(|w|)<=|w|+1. The Stieltjes representation gives Re T(w)>=T(Re w)>Re w. If the real part stayed bounded, the positive continuous increment T(x)-x would have a positive minimum on its resulting compact positive interval, a contradiction. Thus the radius-16 stopping time is finite. Its entry set has 16<=|w|<=17 and Re w>=16 log(pi)/sqrt(log(pi)^2+pi^2)>4. Delays need not be uniformly bounded.

## Domination and all-orders transfer

The positive comparison orbit obeys R_j<=j-(log(j+1))/3+C. For j=n-tau>=n/2 this gives n^(1/3)|t_n/n|^n<=C exp(-tau). For j<n/2 the modulus is at most n/2+17, yielding an exponentially small bound for large n. Before entrance but after crossing the modulus is bounded by 16; before crossing the imaginary part is identically zero. Thus the claimed global bound with exp(-c min(tau,n)) follows. Limiting coefficient functions satisfy exp(Re Psi)|P(Psi)|<=C exp(-tau)(1+tau)^degree because the entry set is compact.

For any prescribed J, expand the convergent Laurent series of T on |w|>=4 to sufficiently many terms, bound its remaining geometric series using mu_k<=2^k/3, and expand the logarithm using |(T(w)-w)/w|<=13/48. Successive coefficients d_l cancel the w^(-l-1) term with nonzero multiplier -l. This constructs a finite constant C_J for |V_J(T(w))-V_J(w)-1|<=C_J|w|^(-J-2). Telescoping gives Phi(w)=V_J(w)+O_J((Re w)^(-J-1)).

For compact initial values, the actual iterate is m+O(log m). The formal candidate obtained by coefficient cancellation is also m+O(log m). On the disk containing both, |V_J'-1|<=C/m. Integration on their connecting segment shows |V_J(v)-V_J(w)|>=(1-C/m)|v-w|. The residual of the finite candidate therefore bounds the actual inversion error, proving the displayed orbit expansion with its uniform finite-order remainder. This explicitly justifies the formal inversion step.

For tau<=A log n, substitution m=n-tau has uniformly controlled ordinary Taylor remainders and produces only finite powers of log n at any fixed order. For tau>A log n, choose A with cA larger than the desired inverse-power order plus margin. The true tail and each proposed coefficient tail are then smaller than the target remainder uniformly, including tau>n. Integration over a finite-length cut preserves the error. The certified outer contour has uniform finite entry, so it requires no delay split. This proves all finite orders with some finite effective logarithmic remainder degree; the exact proposed degree 2M+2 is not asserted here.

## First correction and fixed shifts

Writing a=Psi-L/3 and b=L/9-Psi/3-1/18, exponentiation gives the correction b-a^2/2. Stirling for (n-1)! adds 1/12, producing exactly -L^2/18+(1/9+mu_1/3)L+1/36-mu_1/3-mu_2/2. The normalization C=sqrt(2*pi)I_0/2 and leading power n^(2n-5/6)/(2^(n-1)e^n) are correct. Iteration n+s replaces Psi by Psi+s, including its occurrence in the orbit's 1/n coefficient, so the stated moment substitution and e^s factor are correct.

## Positivity and code review

The cut bound uses the correct crossing-delay direction: before crossing the negative reciprocal magnitude drops by between one and two per iteration, hence crossing cannot occur before 1/s-1. The real comparison Fatou constant at r0=2/pi is <=r0+(1/3)log(r0+2)<2. Therefore Re Psi<=3-1/s. On 0<s<=1/2, exp(3-1/s)<=e, yielding absolute cut contribution <=e/(2*pi)<1/2.

The interval code uses complete parameter panels, not numerical quadrature samples. Its first twelve principal logs have interval domain assertions. The clipping of the initial imaginary lower endpoint to zero is justified by the exact upper semicircle. Reciprocal series coefficients are exact Fractions converted outward to intervals. Horner indices c[2] through c[K+1] represent exactly K moments; the omitted remainder 2^K/(3 r^K(r-2)) is correct. The |w|>2 tests validate each series step, and final real-part tests validate the Fatou tail. exp(Psi) is enclosed using |exp(B)|(exp(eta)-1), followed by multiplication by exact modulus 1/2. The sum divided by Q is the correct normalized integral enclosure. Float conversion appears only in the printed diagnostic minimum and cannot affect bounds.

Independent Q=2048 replay returned [2.148710226926796756397661371493759, 2.423911766794793944536818666505863], with rational assertions 214/100<J<243/100 passing. Its runtime was approximately 30 seconds. Combined with the cut estimate, I_0>1.64. Consequently positivity and the coarse interval 2<C<4 follow. The certificate assumes correct mpmath.iv elementary-function enclosures; it is not an independent transcendental-arithmetic implementation.

## Explicit Abel remainder generator

Let z=1/w and q(z)=z g(1/z), with the removable value q(0)=1. On |z|<=1/3, the Stieltjes representation gives |q-1|<=|z|+(1/3)|z|^2/(1-2|z|)<=4/9 and |q|>=5/9. The logarithm of q is consequently analytic on this disk. The finite Abel defect

D_J(z)=(q-1-z)/z+(log q)/3+sum_(l=1)^J d_l z^l(q^(-l)-1)

is analytic, including its removable value at zero, and cancellation makes it vanish to order at least J+2. On the boundary |z|=1/3:

- |(q-1-z)/z|<=1/3
- |log q|/3<=log(9/5)/3<1/5
- |z^l(q^(-l)-1)|<=(3/5)^l+3^(-l)

Thus its modulus is bounded by B_J=8/15+sum |d_l|((3/5)^l+3^(-l)). Applying maximum modulus to D_J(z)/z^(J+2) proves the stated C_J=3^(J+2)B_J. Summing |w_j|^(-J-2) using Re w_j>=x+11j/12 gives

|Phi(w)-V_J(w)|<=C_J[1/4+12/(11(J+1))] x^(-J-1), x>=4.

All constants generated are rational and rigorous. Their conservatism does not weaken validity. These bounds are separate from the sharper J=1 tail 2/x^2 used for the amplitude certificate.

## Exact generator review and replay

The symbolic generator retains sufficiently many powers of q for the selected cancellation coefficient after division by z. The d_l recurrence cancels the correct power and is linear with nonzero coefficient. The W(n+1,y-log(1+1/n)/3)-g(W(n,y)) recursion includes the correct change of inverse variable x to x/(1+x), and its unknown polynomial has multiplier -j-d/dy/3. Terms retained from g suffice to determine the requested coefficient. The logarithmic normalization and Bernoulli terms are appropriate to Gamma(n)=(n-1)!, not n!; in particular the +1/(12n) correction gives the stated first forward polynomial.

An independent order-3 replay passed and yielded d_1=1/18, d_2=-1/135, d_3=-1/972. The exact defect constants are 79/5, 17881/375, 966001/6750. The Fatou-remainder constants are 553/44, 160929/5500, 22218023/297000. The generated reciprocal and forward polynomials match the integrated formulas. The package records the generated coefficients in results/coefficients.json and an executable replay in verification/replay.py.

The all-order degree claims are analytically supported: the recurrence residual determining v_j has degree at most j; the invertible operator preserves that finite polynomial space. The exponent's coefficient at inverse order j has degree at most j+1<=2j. Products contributing to R_j therefore have degree at most 2j. This supports deg P_(j,k)<=2j. It does not by itself prove a sharp remainder degree; the report correctly retains an unspecified finite effective D_M.

## Inverse and integer enclosure

The Lambert-W scale solves exactly the stated factorial-square logarithmic core. Taylor cancellation gives U_0=[(5/6)L-log(2C)-k]/S and U_1=[(5/6)U_0-U_0^2-A_(1,k)(L)]/S. The higher-order recursion has the correct new multiplier S. Uniform Taylor remainders and the eventual lower derivative bound validate the claimed inverse-index errors for each chosen finite smooth model.

The exact inequality H(n+1,n+1+k)>=S(n+1,n)H(n,n+k)=binomial(n+1,2)H(n,n+k) follows directly from the nonnegative recurrence at depth m=n+k. For fixed k and sufficiently large n the terms are positive and binomial(n+1,2)>1, proving the needed strict monotonicity. If all integers below t-eta have count below Y and all integers above t+eta have count above Y, then ceil(t-eta)<=nu_k(Y)<=floor(t+eta)+1. The endpoint inequalities and possible integer equality are handled safely. The report correctly requires explicit uniform error constants and validity ranges before this becomes a numerical certificate for a particular Y.


## Final scope

- The interval 2 < C < 4 is certified; the finer estimate approximately 2.86540798 is explicitly exploratory
- The coefficient and Abel-remainder constants are constructive; those Abel constants alone are not a numerical sequence-threshold certificate
- No global half-plane continuation or arbitrary-radius invariance is required by the theorem
- No resurgent or exponentially improved expansion is claimed
- The smooth inverse depends on the chosen real model; automatic integer rounding is not asserted
- The interval proof relies on correct outward enclosures from the documented Python and mpmath runtime

The accompanying frozen-source receipt records artifact identity. Its hashes are integrity checks, not a digital signature or a substitute for the mathematical arguments above.
