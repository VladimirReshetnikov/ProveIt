# Integer-population positivity certificates

Let n=(n_1,...,n_d) range over nonnegative integer clone populations, and write
B_a(n)=∏_i binom(n_i,a_i). All coefficient identities below are identities of
rational polynomials, but their nonnegativity is asserted only on integer n≥0.
In particular B_2(n) need not be nonnegative between 0 and 1.

## Final certificate and elementary verification

For a template symmetry group G acting by coordinate permutations, the exported
certificate has the form

P(n)=Σ_j w_j |G|^{-1} Σ_{g∈G} B_{m_j}(g n)
                    [Σ_a c_{j,a} B_a(g n)]²
     + Σ_e r_e B_e(n),

where w_j,r_e are nonnegative rational numbers and c_{j,a} are rational.
Every summand is nonnegative on integer n≥0, so an exact coefficient identity
proves P(n)≥0 for every allowed population, with no finite population bound.
This applies to P=4γ₂²−9γ₁γ₃ or P=3γ₃²−8γ₂γ₄.

The certificate schema records each square as [w,[m,[[a,c],...]]], with packed
base-eight multi-index codes, and records the remainder as [[e,r],...]. It is
unscaled: the target is exactly the displayed Newton gap. The group average
includes all listed actions, even when two actions produce the same monomial.
The verifier expands every action, rather than trusting orbit-aggregated rows.

In one variable the multiplication rule is

binom(n,a)binom(n,b)
 = Σ_{h=0}^{min(a,b)} (a+b−h)!/[h!(a−h)!(b−h)!] binom(n,a+b−h).

This follows by counting pairs of subsets with intersection size h. Taking
products gives the multivariate rule. Thus a verifier needs only exact integer
arithmetic for polynomial multiplication, rational arithmetic for weights, the
action list, and the already audited gamma coefficients.

## Shifted basis used only to discover certificates

For a multiplier B_m, write a square root in the basis B_q(n−m). If n is an
integer outside n≥m coordinatewise, B_m(n)=0. Within n≥m, the change of basis
is useful for zeros near the boundary. The exact multiplication identity is

B_m(n) B_q(n−m)B_r(n−m)
 = Σ_s C(q,r;s) [∏_i binom(m_i+s_i,m_i)] B_{m+s}(n),

where C(q,r;s) is the ordinary binomial-product coefficient above. The shift
is removed from every final certificate via

binom(n−m,q)=Σ_{a=0}^q binom(−m,q−a)binom(n,a).

The producer checks that the shifted and unshifted expansions coincide, then
checks the final unshifted identity. The independent auditor uses only the
unshifted certificate. Discovery heuristics, floating-point LP output, nullspace
constraints, and the rational reconstruction algorithm are not trusted inputs
to the mathematical conclusion.

## Justification of the boundary-zero reduction

Suppose a candidate nonnegative certificate has P(m+s)=0 for every integer
0≤s≤q coordinatewise. Because B_m(m+s)>0, every square root accompanying this
multiplier vanishes on that lower box. Expanding f(s)=Σ_a c_a B_a(s), triangular
Newton interpolation forces c_a=0 for every a≤q. Hence such basis terms may be
removed before solving. An isolated zero at m+q does not on its own force c_q=0;
it contributes the linear evaluation constraint Σ_a c_a B_a(q)=0 instead.

Leading homogeneous zeros provide further necessary linear conditions, but
checking only some zeros can never create an invalid final proof: the full exact
identity and positivity of its weights are sufficient independently of search
completeness or the chosen candidate cone.

## Optional lower-degree core correction

For a four-attachment template, every matching of size four uses four exterior
vertices: using an internal core edge would require at least five core endpoints.
Similarly a size-three support either uses three exterior vertices and no core
edge, or exactly two exterior vertices and one core edge. Therefore, extracting
terms by total population quota degree gives

γ₄=F₄,   γ₃=F₃+C,   γ₂=F₂+B,

where F is the exterior-only support polynomial, C has binomial quota degree2,
and B has quota degree at most1. The exact identity is

3γ₃²−8γ₂γ₄ = (3F₃²−8F₂F₄) + E,
E=6F₃C+3C²−8BF₄.

The first term is nonnegative by the separately proved order-four exterior
Lorentzian theorem, even when the exterior polynomial has actual degree below
four. The correction E has population degree at most5. In some templates an
integer-binomial square certificate for E is substantially smaller than one for
the whole sextic. Such a certificate is explicitly tagged core_correction_E;
an independent checker reconstructs F,B,C from the audited gamma quotas and
checks the displayed decomposition before checking E's exact square identity.

This is a template-specific sufficient method. E can be negative in legitimate
integer populations of other templates, so the core-correction argument is never
invoked without an exact nonnegativity certificate for that template's E.
