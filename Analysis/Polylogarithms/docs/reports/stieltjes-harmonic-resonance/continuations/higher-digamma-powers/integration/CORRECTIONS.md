# Proposed source corrections

The article contains the full proofs and qualifications.

## 1. Bailey–Borwein: reversed integrals

Inspected source: D. H. Bailey and J. M. Borwein, Computation and theory of
Mordell–Tornheim–Witten sums II, author-hosted version dated 5 May 2014.

https://www.davidhbailey.com/dhbpapers/mtw2.pdf

Location: equation (110), printed page 24, PDF page index 23.

Let

    A(a) = 1/Gamma(a+1) * integral_0^1
           [(-log u)^a * (-log(1-u))/(1-u)] du
    B(a) = integral_0^1 Li_a(u) * (-log(1-u))/u du.

For Re(a)>0, the correct identity is

    zeta(a+2) = B(a) - A(a).

The inspected equation (110) prints A(a)-B(a). At a=1, A(1)=zeta(3) and
B(1)=2 zeta(3), so the printed right side is -zeta(3). Its preceding
equation (109) remains valid. A direct proof uses

    sum_(n>=1) 1/[n(m+n)] = H_m/m,

which gives T(a,1,1)=Z(a+1,1)+zeta(a+2) throughout Re(a)>0 by absolute
convergence. The correction is limited to this inspected version, with no
claim about an uninspected final typesetting.

## 2. Mező: the multiple-zeta target is too broad

Inspected source: I. Mező, Nonlinear Euler sums, Pacific Journal of
Mathematics 272 (2014), no. 1, 201–226.

https://msp.org/pjm/2014/272-1/pjm-v272-n1-p09-s.pdf

Location: printed page 205, paragraph before Theorem 1.

The statement that expressibility of the indicated nonlinear harmonic sums
as multiple zeta values is unknown is false as worded. For q>=2 and
positive integer harmonic orders, finite stuffle products reduce every
product of finite harmonic sums to a finite combination of strict words.
For each nonempty word b,

    sum_(n>=1) H_n(b_1,...,b_l)/n^q
      = Z(q,b_1,...,b_l) + Z(q+b_1,b_2,...,b_l).

This proves finite multiple-zeta expressibility. A precise replacement
should name a smaller target, such as ordinary zeta values and their
products, or a specified family of linear Euler sums. The article does not
claim that those stronger reductions always exist. The later theorems of the
paper are not invalidated by this wording correction.

## 3. Local attribution in the ProveIt S2 section

Add the citation Xu–Wang, Dirichlet type extensions of Euler sums,
arXiv:2009.11704v3, Section 3.4, Example 3.13, beside the classical formula
for S2 using Li_3((1+i)/2).

https://arxiv.org/html/2009.11704v3

Their R_(1,bar2)=4 S2 gives precisely the same value. The wider manuscript
already cites the work. This is a local attribution improvement, not a
mathematical correction.

## Audit scope

No new false theorem was found among the selected repository statements
used in this continuation. The audit is not exhaustive. S6 and revised S8
remain conjectures; the arithmetic reduction of chi and Omega_4 is also
unresolved. Those limitations are not described as errors in the sources.
