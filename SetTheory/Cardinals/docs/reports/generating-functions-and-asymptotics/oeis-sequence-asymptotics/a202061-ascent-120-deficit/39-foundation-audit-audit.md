# Independent adversarial audit of the A202061 deficit proofs

Audit date: 2 October 2026 (UTC).

## Verdict

**No mathematical defect found in the six frozen proof notes.** The exact
positive height-walk reduction supports the lower and upper bounds, including
the logarithmic refinement. The inverse-order and non-D-finiteness corollaries
follow. No repair to an author file was needed or made.

The audited main conclusion is

\[
 n\log\mu-\log a_n
 =\Theta\!\bigl(n^{1/3}(\log n)^{2/3}\bigr),
 \qquad \mu=7.295896943239772\ldots,
\]

where \(\mu\) is the largest root of \(\mu^3-8\mu^2+5\mu+1=0\).
This is a two-sided order theorem. It is **not** a leading equivalent, a
computed stretch constant, an all-orders asymptotic expansion, or an explicit
finite-size error certificate. It excludes a fixed negative \(n^{3/8}\) stretch
and a fixed negative pure \(n^{1/3}\) stretch, even with a fixed polynomial
prefactor. The ordinary generating function is not D-finite.

This audit is mathematical review with independently reproduced exact
diagnostics; it is not formal verification or conventional journal peer review.
It does not establish priority or novelty of the reduction or theorem.

## Frozen inputs and reproducibility

The source files were read from `/workspace/shared/oeis-a202061-research`:

- `operator_proof.md`
- `stretch_bound_proof.md`
- `upper_scale_proof.md`
- `log_scale_refinement.md`
- `inverse_order_corollary.md`
- `non_dfinite_corollary.md`

Their SHA-256 hashes are in `source-sha256.txt`. All six were checked unchanged
after the analysis and test runs. The relative paths in that manifest are
relative to the author's research directory.

The following diagnostics are separate from the author's files:

- `independent_checks.py`: signed quadratic recurrence versus the positive
  coefficient formula, exact critical-field and rational interval checks,
  independent Narayana coefficients, exact finite first-hit decomposition,
  and explicitly labeled numerical tail/tilt diagnostics
- `independent-check-output.txt`: all checks passed
- `staircase_checks.py`: independent integer boundary and length-repair checks
- `independent-staircase-output.txt`: all checks passed
- `author-replay.txt`: fresh successful replay of the author's critical
  certificate, Narayana, staircase, operator, height-walk, literal-word, and
  binomial-formula checks

Independent checks compared 1,690 jump coefficients through x-degree 12 and
gap parameter 10, and 1,785 Narayana coefficients for j through 35 and k through
50. The finite first-hit identity was checked at 36 height/length pairs. The
independent staircase check covered every up/down level from 20 through 1000,
every loop length from 1000 through 20000, all 85,204 residual lengths at levels
20 through 35, and additional samples through level 1,000,000. These are
diagnostics; the uniform arguments below are what prove the infinite claims.

Commands, from this audit directory:

```
python independent_checks.py
python staircase_checks.py
```

These scripts use Python, SymPy, and mpmath. The author's `block_formula.py`
also uses SciPy for a nonessential numerical stationary-point diagnostic.

## 1. Exact normalized state and operator reduction

The threshold is the largest lower endpoint of a previously occurring strict
increasing pair. A future letter smaller than that threshold creates a 120
pattern; all other restrictions are encoded by the translated ascent budget,
the surviving seen values, and the last letter. On appending i, the new
threshold rises to the largest old seen value p below i, or stays at zero.
The update must insert i-p in the surviving set; the audited formula does.

The claim that the last letter is zero or the least positive surviving value
is preserved by every transition. The height is at least one: after a positive
new maximum is introduced, the ascent count has increased, and subsequent
transitions do not violate max(S) <= a. This also holds for the initial state.

I rederived the E/G equations. The first gap is the only place where a
positive-last-letter state and a zero-last-letter state differ in whether the
next letter is an ascent. Their difference is exactly x(1-T)D. Combining with
the E-tail difference gives the positive operator

\[
 A=x+\frac{x^2T}{1-x}.
\]

The q=d term in D is present and generates the factor 1-A in the induction.
For q<d, both gap sizes are smaller, so using their previously proved operator
identities is legitimate. There is no circular assumption that gap operators
already commute: the induction first makes each one a formal function of T.
They then commute.

The boundary equation has drop q-1, rise r, and exact legality q<=h. Its
resulting height h+1-q+r is automatically positive. Each macro-step carries at
least one x, and only finitely many height shifts occur at a fixed x-degree.
This proves x-adic uniqueness of the walk solution and legitimizes all finite
coefficient decompositions used later.

A literal word-level bijection for every macro-decoration is unnecessary.
Nonnegative formal coefficients and equality to the word generating function
suffice. For full precision, the bounded-height and first-hit pieces should be
understood as classes of the positive formal height walks; their coefficients
partition a_n, whether or not a canonical macro-decomposition has separately
been assigned to each individual word. This is an expository clarification,
not a missing hypothesis.

## 2. Positive coefficient identity and uniform entropy lower bound

The W substitution gives the audited quadratic, and formal Lagrange inversion
gives the stated C(j,k). Extracting t^r forces r-k selections from
(1+xt/(1-x))^j. Extracting the remaining x-degree yields exactly

\[
 \binom{j+\ell-2}{\ell-r-k-1}.
\]

Thus no power of 1-x, x, or t is missing in the binomial formula. The exceptional
constant coefficient ell=r=0 is accounted for separately. The independent
script recovered Q directly from its quadratic by a signed recurrence, without
importing the author's positive-operator implementation, and obtained the same
coefficients.

The entropy is the sum of the four ordinary binomial entropies. Its first
derivatives at the critical point satisfy

\[
 S_k=0,\qquad S_a+S_d=0,\qquad
 e^{S_d}=\frac{\kappa(1-\alpha-\kappa)}
 {(\alpha-\kappa)(2\alpha+\kappa)}=z_*.
\]

Euler's homogeneous entropy identity gives S=log(mu). No global maximization
claim is needed. The exact prefactor identity for C(q,k), plus the shifted last
binomial, leaves a factor of order ell^(-3), as asserted.

Rounding q and k causes bounded errors. With r-q=O(sqrt(ell)), the Taylor
remainder in ell*S is O(1). With r-q=O(sqrt(ell log ell)), it is O(log ell).
All normalized factorial arguments stay in a fixed strictly positive compact
set in both cases. Uniform two-sided Stirling bounds therefore prove (14) and
(24), with constants independent of the block index. There is no unstated
local limit theorem or saddle-point asymptotic in this step.

## 3. Boundary conditions and every-length repair

For the square staircase, the ascent and descent increments are exactly
2j+1 and -2j+1. The supplied choices r=q+2j and r=q-2j implement them. For the
logarithmic staircase, r=q-1+(h_next-h) likewise gives the exact desired
increment, including the floor errors. For a sufficiently large fixed J,
all r, k, r-k, and ell-r-k-1 remain admissible. Both staircases have q<=h at
every step, including the descending steps.

The seed from height 1 to h_J has length 2h_J-1; the return has length 1;
the initial word letter has length 1. Thus their combined contribution is
2h_J+1, exactly as used in L_K. The up/down staircase has zero total height
increment, so

\[
 \sum(r-q)=-\text{number of its blocks}.
\]

The tilt therefore costs or gains only a fixed factor per block. Comparing
mu^ell in a block bound with its full length ell+1 also loses only a fixed
factor per block. Neither issue creates an overlooked exponential-in-n loss.

For the accelerated heights h_j=floor(j^2 log j),
ell_j=Theta(j^2 log j) and |h_(j+1)-h_j|=O(j log j), which is
O(sqrt(ell_j log ell_j)). Summing the lengths gives

\[
 L_K=\frac{K^3\log K}{3\alpha}+O(K^3),\qquad
 L_{K+1}-L_K=\ell_K+\ell_{K+1}+2.
\]

For any residual R below this gap, fixed bounded R can be placed in the final
geometric factor. Otherwise two almost-equal loop lengths m_1+m_2=R are
each above a fixed threshold where the uniform bound holds. A loop has
ell=m-1, r=q-1, so its increment is zero. Its legality follows from

\[
 q\le \frac{\alpha R}{2}+O(1)
 \le\frac{h_K+h_{K+1}}4+O(1)<h_K
\]

for every sufficiently large K. The same argument with h_K=K^2 proves the
original square repair. The strict final inequality has a linear-in-h_K
margin, so neither integer rounding nor residual parity causes an exception
at arbitrarily large lengths.

There are O(K) blocks, all of polynomial size in K. Their multiplicities give
the loss O(K log K), including the at most two repair blocks. Since
K=Theta((n/log n)^(1/3)), this is exactly
O(n^(1/3)(log n)^(2/3)). This establishes the lower bound for every sufficiently
large integer n, not merely a subsequence.

## 4. Critical finite norm and moving-tilt perturbation

The fixed-point supersolution has a strictly positive denominator. Iteration
from zero is monotone and bounded by W_*, so it selects the least nonnegative
formal branch and establishes convergence at the critical parameters. Its
unrestricted weighted row mass is at most

\[
 m_* =\frac{\rho}{(1-\rho)z_*+\rho}
 =0.445041867912628\ldots <1.
\]

The legal row sum is smaller. The terminal factor is dominated by a constant
times t_*^h. Consequently e_h(rho)<=C t_*^h holds uniformly for all h, and
A(rho)<infinity. This argument does not infer a spectral radius from a kernel
discriminant.

For the moving tilt, write u_0=eta_*(1+W_*). The exact identities imply

\[
 -\frac1{1+\beta_*}+\frac{u_0}{1-u_0}=0.
\]

This is the derivative of log F with respect to theta when z is multiplied by
exp(-theta) and t by exp(theta). The x derivative is strictly positive. The
Taylor expansion with x_theta=rho exp(-D theta^2) therefore has a negative
quadratic term for sufficiently large fixed D, uniformly in a small compact
theta interval. Positivity of the denominator and a row mass below one persist
by continuity of the explicit supersolution bound, even though Q itself lies
at an algebraic singularity at theta=0. No analytic continuation of Q through
that singularity is being assumed.

The independent exact interval check finds that even D=1 has a normalized
quadratic coefficient in

\[
 [-1.405813207414549,-1.405813207414480].
\]

Only local existence is needed in the proof. This check does not claim an
effective universal theta interval for the final coefficient bounds.

## 5. First-hit prefixes and suffix cancellation

The sum over all finite prefixes with endpoint weight t_theta^h is bounded
by t_theta/(1-m_bar): after k macro-steps the tilted mass is at most
t_theta*m_bar^k. Every step has positive length, so the first-hit prefix is
well defined, and the first-hit prefixes form a subcollection of these
prefixes. Overshoots above H are fully included.

After a first hit at h>H and length m, the complete remaining suffix has
critical weight at most C t_*^h. Coefficient extraction at total length n,
including the original leading factor rho, consequently gives the stated
upper bound by a sum of p_(m,h) rho^m t_*^h. The two changes of measure are

\[
 \rho^m\le x_\theta^m e^{D\theta^2 n},\qquad
 t_*^h\le t_\theta^h e^{-\theta H}.
\]

These inequalities have the correct signs and do not impose a final-height
restriction on the complete walk. The suffix's critical tilt is exactly what
removes the otherwise problematic endpoint-height factor. Optimizing at
theta=H/(2Dn) yields exp(-H^2/(4Dn)) whenever this theta is small enough.
In both applications H=o(n), so the required interval condition holds.

The independent finite integer check also verifies the exact decomposition
into confined paths and first-hit-prefix times unrestricted suffix, including
geometric-factor length contributions.

## 6. Fixed-tilt tail and logarithmic cutoff perturbation

At x=rho, t=t_*, the discriminant has leading coefficient (b+rho*t_*)^2 and
constant coefficient s^2, with s=b^2-rho^2*t_*>0. Its roots are z_* and z_2,
where exact rational intervals independently give

\[
 0.1980622641951613<z_*<0.1980622641951623,
\]
\[
 0.8817230195038748<z_2<0.8817230195038841<1.
\]

Thus the claimed factorization and the branch in (20) are correct: the square
root equals s at z=0, making the numerator vanish there. Choosing the other
branch would fail Q(0)=0.

After scaling w=z/z_*, the singular part is sqrt(1-w) times a function analytic
in a disk of radius greater than one. Its coefficient convolution is
O(q^(-3/2)); the nonsingular part is exponentially smaller. This proves the
upper tail bound without cancellation or an assumption about the sign of the
analytic multiplier's coefficients. The coefficients Q_q themselves are
nonnegative by the operator/formula construction. Numerical diagnostics of
q^(3/2)Q_q z_*^q approach a positive constant, consistent with, but not used to
prove, the tail estimate.

For fixed q, the Narayana identity makes Q_q(x,t_*) a rational expression with
positive polynomial numerator and denominator bounded away from zero on a
fixed x interval past rho. The numerator degree is at most q. Logarithmic
differentiation therefore gives the uniform exp(C(q+1)(x-rho)) comparison.
This comparison remains valid when x exceeds the unrestricted walk radius,
since q is fixed and eta(x)<1.

For delta_H=epsilon*log(H+1)/(H+1), the extra weighted mass in the truncated
row is bounded by

\[
 O\!\left(\sqrt{\delta_H}
       +e^{C H\delta_H}\sqrt{\delta_H}\right)=o(1)
\]

if C*epsilon<1/2. The split at q=1/delta_H gives this bound exactly. Because
the original mass has a strict gap below one, the confined-walk generating
function remains bounded at rho+delta_H, uniformly in sufficiently large H.
The coefficient cost is exp[-c*n*log(H+1)/(H+1)].

Balancing that cost with exp(-c*H^2/n) at
H=floor(n^(2/3)(log n)^(1/3)) proves the desired upper logarithmic deficit.
All constants can be reduced or enlarged to handle the floors and the finite
small-H exceptions. There is no missing uniformity at criticality.

## 7. Inverse-order corollary

Appending the last letter is an injective operation preserving ascent-sequence
validity and 120 avoidance. A new pattern using the repeated last letter as
its smallest value would already use the preceding copy; the strict
inequalities exclude the preceding copy from acting as the larger middle
index. Monotonicity follows.

With L=log Y and N=min{n:a_n>=Y}, the upper coefficient bound implies
lambda*N-L>=c*Phi(N)-O(1), with N>=L/lambda-O(1). This gives the positive
lower correction of order Phi(L). Choosing
n=ceil(L/lambda+K*Phi(L)) with fixed sufficiently large K gives the reverse
bound by the lower coefficient estimate. The ceiling is negligible. Thus the
claimed positive Theta((log Y)^(1/3)(log log Y)^(2/3)) correction is valid.

## 8. Non-D-finiteness and the external regularity theorem

The two-sided exponential rate makes the radius exactly rho. The stretched
upper estimate implies sum n^k*a_n*rho^n<infinity for every fixed k. Uniform
convergence of all differentiated series gives finite, continuous one-sided
derivatives of every order at rho.

If A were D-finite over Q(z), its integer coefficients, exponential growth
bound, and trivial denominators would make it a Siegel G-function. I directly
checked Definition 2.2 and Theorem 2.1(c) on printed page 4 of
[Garoufalidis and Bellissard, *Algebraic G-functions associated to matrices
over a group-ring*](https://people.mpim-bonn.mpg.de/stavros/publications/algebraicGfunctions.pdf).
The stated consequence of the Andre–Chudnovsky–Katz theory is precisely the
finite convergent local rational-power/logarithm expansion used in the note.

For clarity, put s=rho-z>0 along the incoming real radius. Group the local
terms by exponent modulo integers, absorb integer shifts into analytic
factors, and combine equal log powers. If any nonanalytic term remains, the
convergent expansion has a least surviving noninteger power, negative integer
power, or log-bearing power. A finite derivative order then fails to have a
finite continuous limit at s=0. Such a term cannot survive the proved
C-infinity regularity. The remaining ordinary Taylor series is convergent,
so A would be analytic at rho, contrary to Pringsheim's theorem.

This is the correct arithmetic-regularity argument. **Do not replace it with
the assertion that every D-finite function has only power/logarithmic local
behavior, or that rational stretched exponents alone prohibit
P-recursiveness.** Those assertions are false in general. In particular, the
nearby broad coefficient-expansion lemma in the cited article is not needed
or invoked here; Theorem 2.1(c) is the relevant result.

The optional extension from Q(z) to C(z) is also correct: for fixed order and
degree, a complex differential relation gives a nonzero solution of a rational
linear system with finitely many unknowns. A finite subset of its rows attains
the full rank. The resulting nonzero kernel has a rational basis, giving a
rational differential relation and the same contradiction.

## Release scope

All six claims are mathematically approved by this audit, subject to the
explicit scope above. Retain the distinction between the exact height-walk
representation and a finite algebraic equation for A. Retain the distinction
between a Theta logarithmic deficit and an asymptotic equivalent. No
all-orders expansion or leading stretch constant has been established.
