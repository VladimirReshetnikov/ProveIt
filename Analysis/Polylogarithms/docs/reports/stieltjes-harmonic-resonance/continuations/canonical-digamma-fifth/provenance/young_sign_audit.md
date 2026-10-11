# Young 2024 sign audit

Primary source: Paul Thomas Young, *Series of Height One Multiple Zeta
Functions*, Integers 24 (2024), #A43, published 20 May 2024.
URL: https://math.colgate.edu/~integers/y43/y43.pdf
DOI printed in PDF: 10.5281/zenodo.11221606.

The inspected PDF, pages 11--12, uses the conventional first Stieltjes
constant in (4.1) and Example 5 (4.4), but its descriptions around
(4.1), (4.2), and Corollary 3 identify that constant with the literal
linear coefficient. Under zeta(1+u)=1/u+gamma-gamma_1*u+..., it is the
negative of that coefficient. This is a definition/sign-description
correction, not evidence against the numerical identity for gamma_1.

Let lambda_j=[u]zeta(1+u,{1}^{j-1}) and
c_k=[u^k]1/Gamma(1+u). In this explicit coefficient notation, the
correct translation of (4.2) is

    nu_(0,j)-nu_(-1,j-1) = -lambda_j+c_(j+1).

Consequently Corollary 3 translates to lambda_j=c_(j+1) minus the
displayed multiple-Hurwitz integral. It does not translate to that
integral minus c_(j+1). The Cauchy-number coefficient series is existing
literature, and must not be presented as a new formula here.

## Independent d=1 numerical control

At 100 decimal working digits and with 180 terms, independently evaluate

    nu01=sum_(n>=2) (-1)^n zeta(n,1)/n,
    nu_minus1_0=log(2)+sum_(n>=2) (-1)^n (zeta(n)-1)/(n-1),

where zeta(n,1) is evaluated from Euler's finite formula

    zeta(n,1)=n*zeta(n+1)/2
              -sum_(j=1)^(n-2) zeta(n-j)zeta(j+1)/2.

The subtracted second series is absolutely convergent; the log(2) term
is the exact alternating harmonic sum. This computation is independent
of the multiple-Hurwitz integral in Corollary 3.

Results:

    nu01 = 0.5290529699404390240722939394755897280940381716959625690873757506297183124114692381606
    nu_minus1_0 = 1.257746886944369630009899830495881528511540890508884868978751456830773734763018849369
    nu01-nu_minus1_0-c2 = -0.0728158454836767248605863758749013191377363383343379525990132605171845839978275091217
    conventional gamma1 = -0.07281584548367672486058637587490131913773633833433795259900655974140143357151148487809

The discrepancy is about -6.700775783e-60. These are noninterval
diagnostics. The conceptual correction comes from the explicit Laurent
definition and the independently proved coefficient identity, rather than
from the decimal agreement.

The literal linear coefficient is the positive number -gamma1. Suggested
editorial correction: specify the minus sign in the verbal coefficient
description, while retaining the equations for conventional gamma1.

## Primary lecture confirms the convention

Paul Thomas Young, *Global series for height 1 multiple zeta functions*,
lecture dated 4 July 2023, College of Charleston; hosted by the Institut
Elie Cartan de Lorraine:

https://iecl.univ-lorraine.fr/wp-content/uploads/2023/07/tuesday-12-young-p.pdf

The public PDF downloaded with an ordinary urllib request (HTTP 200) and
was inspected in full. It contains 17 numbered slides, spread over 55 PDF
pages because of presentation overlays. A local research copy and text
extraction are `young_2023_lecture.pdf` and `young_2023_lecture.txt`.

Numbered slide 3 explicitly defines the regular Laurent terms as

    sum_(i>=0) (-1)^i gamma_i^[j](k) (s-k)^i / i!.

Numbered slide 6 explicitly identifies the linear coefficient as
`-gamma_1^[j](1)` and states

    lambda_j = c_(j+1) + sum_(n>=1) |b_n| H_(n-1)^(j+1),

with the same strict depth j convention as above. Thus the proposed 2024
correction is corroborated directly by the author's earlier explicit
definition and equation; it is not a guess about his normalization.

The lecture itself does not display the normalized gamma quotient
Gamma(1+t)Gamma(x)/Gamma(x+t) or its all-depth polygamma realization.
Slides 15--16 nevertheless give Ramanujan sums of complete harmonic star
sums in terms of these strict-depth constants. Slide 17 explicitly asks
for a better explanation of that star/strict connection. Consequently,
that connection in general must be credited as existing work.

## Equivalence of the Cauchy coefficient series

Let b_n be defined by t/log(1+t)=sum b_n t^n. For n>=1, b_n has sign
(-1)^(n-1). Set

    A_n = integral_0^1 (r)_n dr / n!,
    a_n = n A_n = integral_0^1 (r)_n dr / (n-1)!.

Generating functions give

    sum_(n>=0) A_n z^n
      = -z / ((1-z)log(1-z))
      = (1-sum_(k>=1)|b_k| z^k)/(1-z).

Hence A_n=1-sum_(k=1)^n |b_k|=sum_(k>=n+1)|b_k|; the last equality
follows by taking z upward to 1 in -z/log(1-z). Tonelli's theorem applies
to these nonnegative terms and yields, for j>=1,

    sum_(n>=1) a_n/n^(j+2)
       = sum_(k>=1)|b_k| H_(k-1)^(j+1).

Thus the Cauchy-number series in the proposed article is precisely the
known Young coefficient formula under a change of coefficients.
