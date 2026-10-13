# Colored-tail classification and character-valued Stieltjes moments

12 October 2026 (Pacific). This research continues publication
`b913e506885a1d9d4c6d41d2f726171b833d560d`. It appends two classification
results to the colored section and derives the character-valued ordinary
integral identities in the following section. ProveIt Contributors remains
the collective author. Original report files and recorded evidence are unchanged.

## Sources and mathematical scope

The preserved gamma-normalizations-colored-moments report, especially
`sections/06_audit_research.tex`, asks for simultaneous-tail classification
and a character-theoretic exceptional-moment dictionary. Its earlier
colored Mellin transform and alternating beta example remain attributed
foundations, not new results of this milestone.

The all-order alternating classification uses a classical external theorem:
Brillhart proved that E5 is the only Euler polynomial with multiple roots.
Its bibliographic source is J. Reine Angew. Math. 234 (1969), 45--64,
DOI 10.1515/crll.1969.234.45. The publisher's full original proof was not
accessible in this audit. The precise complete statement was verified in
F. T. Howard, *Roots of the Euler polynomials*, Pacific J. Math. 64 (1976),
printed page 181, at
<https://msp.org/pjm/1976/64-1/pjm-v64-n1-p17-s.pdf>, and in
<https://dlmf.nist.gov/24.12.iv>. The derivation for Stieltjes balancing
uses E_q'=q E_(q-1); the positive golden root is the only alternating
exception, at order five. No new proof or priority for Brillhart's theorem
is claimed. Its consequence for extra moments is complete at every order:
only the order-four golden kernel has two extra integer Mellin moments;
no alternating kernel has three.

The independent unit-circle theorem has the explicit bound 1<=q<=8.
It excludes every nonalternating simultaneous zero by polynomial
certificates, and independently checks the Euler gcds in that finite range.
The proof treats b*t nonzero, b=0 with t nonzero, and t=0 separately.
The case distinction is essential: dividing by b without the central
certificate would omit a=1/2. Neither this theorem nor its certificate
asserts an unrestricted unit-circle classification or the absence of
single-tail zeros at higher order.

At the central shift a=1/2 a separate all-order induction is available.
The Cayley recurrence gives B_k=(i/2)^k P_k(t), with
P_(k+1)=t P_k+(1+t^2) P_k'. These are the secant derivative polynomials;
their alternating parity and strictly positive coefficients imply that
no tail vanishes at any real t other than zero. This self-contained
central result neither depends on the bounded certificates nor enlarges
their noncentral scope.

The new character dictionary covers every nonprincipal Dirichlet character,
primitive or imprimitive. It uses the classical functional equation,
Gauss sum convention, Euler product, trivial zeros and nonvanishing at one
recorded in <https://dlmf.nist.gov/25.15>. For a primitive character of
conductor f and parity epsilon, q=epsilon+2n gives

    integral x^q K_(q,chi)(x) dx
      = (-1)^n i^epsilon tau(chi) q! f^q / (2 (2*pi)^q)
        * L(q+1,conjugate(chi)).

The nonprincipal restriction is material: the primitive inducing conductor
is greater than one, so the scalar order-one pole is absent. Principal
characters require a different subtraction and are excluded explicitly.
No historical priority claim follows from these targeted source checks.

## Proof audit

* The finite Stieltjes kernel has the factor 1/d, shift (x+r)/d, and
  logarithm log(x/d). The character sum zero cancels both the Laurent
  pole and the extra uncolored logarithmic term.
* The periodic Laplace density is analytic at zero and exponentially
  decreasing at infinity. Absolute Fubini on 0<Re(u)<1 and normal
  differentiation in the order variable give the scalar transform.
  The differentiated density expansion provides the larger ordinary
  Mellin strip and the exact necessary-and-sufficient consecutive-zero
  criterion. No conditionally rearranged Dirichlet series is used there.
* The primitive functional equation uses tau(chi), not its conjugate,
  and gives the phase i^epsilon after multiplication by (-1)^q.
  The gamma residue accounts for the factorial and conductor power.
* For an imprimitive character, each omitted Euler factor is nonzero
  at negative integers -q with q>=1. At zero, every omitted prime with
  chi_*(p)=1 contributes one additional zero. This yields the complete
  exceptional order-zero classification, including the two-tail block
  for odd inducing characters with at least one such prime.
* Inclusion--exclusion gives the exact finite dilation identity at every
  Stieltjes order, with coefficient mu(h) chi_*(h)/h. The logarithmic
  differentiation introduces no extra log(h) terms because x^z h^-z
  equals (x/h)^z before differentiation.
* The modulus-21 and modulus-273 digamma combinations have first tails
  (L(0),L(-1),L(-2))=(0,0,32/3) and (0,0,-1792). Their O(x^-3) decay
  proves absolute convergence of both unweighted and x-weighted integrals.
  The individual H integrals diverge and are never split into separate
  improper integrals in the proof. One removed prime gives log(7)/3;
  two give zero. Both have explicit first moments in L(2,chi_3).

The root researcher and an independent proof reviewer checked these
normalizations, bounds, algebraic cases and constants. The result is a
written mathematical proof with exact finite certificates where stated;
it is not a Lean formalization.

## Reproducible exact certificate

Run `py verification/check_stieltjes_unit_circle.py --extra-identities`
from the manuscript directory. The result records 41 base identities,
16 additional derivative/recurrence identities, and nine rejected
corruptions. The generator and verifier use different coordinate
recurrences. Verification performs rational polynomial expansion only,
not a Groebner-basis call or numerical root search. It enforces all order
indices and multiplier arities; certificate polynomials are parsed with
a restricted arithmetic parser. The independent regeneration is also
reproducible with `generate_stieltjes_unit_circle.py` and its output option.

The character checker separately records finite exact Bernoulli tail
values, direct-modulus versus Euler-factor identities, and precision-
refined ordinary quadratures. The quadrature uses Euler--Maclaurin
Stieltjes kernels and exact-rational asymptotic coefficients for the tail;
it does not use the claimed Mellin value for the integrand. Fixed-point
evaluations from generalized Stieltjes constants independently check the
kernel dictionary and dilation scaling. These finite precision checks are
diagnostics, not interval certificates or substitutes for the proof.

The successful character record has 36 exact rational tail/zero-pattern
checks, 36 direct-modulus/Euler-factor comparisons and 16 finite Euler gcd
checks. The latter are diagnostics through order 16, not proof of the
external all-order theorem. Two runs at 50 and 65 digits independently
integrate seven moments, test one vanishing combination, and compare five
fixed-point Stieltjes definitions. Their worst ordinary residuals are
6.84e-31 and 3.06e-39, respectively, below the declared 1e-30 tolerance.
Three wrong-formula controls at each precision reject missing odd phase,
conductor power and Euler factor. Four further comparisons use the
nonreal quartic character modulo five at q=1,3, and distinguish the
conjugate-character functional equation from the incorrect unconjugated
version; the wrong version has residuals above 0.25. These four checks
are functional-equation diagnostics, not ordinary quadratures.

Build, visual-review and receipt evidence is recorded in VALIDATION.md.
The continuing research goal remains active, including the unrestricted
nonalternating simultaneous-tail problem and further exact identities.
