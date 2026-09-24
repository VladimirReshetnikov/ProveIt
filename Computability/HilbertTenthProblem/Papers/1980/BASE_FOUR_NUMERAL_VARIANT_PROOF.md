# The 106-operation base-four system with eight numeral constructions

The system in `MAIN_PELL_BASE_FOUR_PROOF.md` admits a 106-operation
certificate whose fixed numeral construction costs eight further
operations, giving 114 when only the numeral 1 is supplied. The core
has 59 multiplications and 47 additions; the complete certificate has
64 multiplications and 50 additions. It retains 34 positive unknowns
and 22 equality tests. The separate 107-operation construction with
113 operations including numerals remains the smaller certificate under
that stricter convention; this variant does not claim to improve it.

`../verification/round15_1980_certificate.py` verifies the complete core
and strict primitive schedules, every source residual identity, and all
support bounds. Its JSON contains both schedules and their residual
receipts. No preceding certificate or fixed index is modified.

## An equivalent arrangement of the base-four arithmetic

As in the base-four construction, the supplied positive coordinate is
`a=a_0`, and the mathematical main Pell parameter is `A=a_0+4`.
The predecessor computes `A-1`, `A+1`, and the E14 modulus `8A-17` by

    am1 = a+3,        ap1 = am1+2,
    a4 = 8a,         a4m5 = a4+15.

Instead use the following four instructions, with `ap1` moved before
its first use:

    ap1 = a+5,       am1 = ap1-2,
    a4 = 8ap1,       a4m5 = a4-25.

They compute exactly the same three required registers:

    ap1=A+1,    am1=A-1,    a4m5=8(a+5)-25=8A-17.

The intermediate `a4` is used only to compute `a4m5`; its new value
requires no other change. Each subtraction remains one primitive
addition with the equality reversed, exactly as in the declared
complexity convention. In particular, the replaced subtraction
results are positive: `am1=A-1>0` and `a4m5=8a+15>0`.
The number of core instructions is unchanged. The source equations,
including the base-four exponent congruence and its positive-domain
proof, are identical for any fixed exponent `L`.

## The enlarged fixed exponent and index

Keep the modular Sidon weights and all row positions from
`MODULAR_SIDON_PROOF.md`. In particular,

    v_i = 1+3(122i+(i^2 mod 61)),    0<=i<=59,
    t_* = 316719070,    K=t_*+1=316719071.

Replace only the fixed exponent by

    L=5^16=152587890625.

The exact required margin still holds:

    3K+2=950157215<L.

All other separation inequalities are independent of `L`. The old
coefficient polynomial `D`, the power of two `z` strictly above its
absolute coefficients, and `Z=2z` are unchanged. For the new exponent
define the fixed index by

    ell_0(B) = sum_{i=0}^{59} B^(v_i)+sum_{r=0}^{1831} B^(t_r),
    e_0(B) = z sum_{j=0}^{K-1} B^j+D(B),
    V = ell_0(Z)+e_0(Z) Z^L,
    H > max(2Z^(2L+1),4^(t_*+3) Z 1900^2,3L,16),

where `H` is a power of two. Thus the index is rebuilt for the enlarged
`L`, with no dependence on the queried input `x`.

The proof of `MODULAR_SIDON_PROOF.md` requires only the displayed support
margin and `L>=2`; it does not require its particular value `2^32`.
The bounds on `H` are enlarged accordingly. Consequently the canonical
polynomial degree estimates, evaluation-at-4 argument excluding aliases,
Pell index comparison, and all positive witness choices remain valid.
For example, the high-mask estimate follows again from
`e,C<B^K` and `L>3K+2`, which give `2eC^2<q` after `q=B^L`.
The fixed-exponent equation is explicitly replaced by

    kappa=L+Delta(A-1)=L+Delta(a+3).

The checker changes both its source residual and its instruction
literal, so this is a change of admissible index, rather than a
renaming of a constant in the operation count.

## Eight constructions and the complete strict certificate

After the rearrangement the complete literal set, apart from 1, is
`2,4,5,8,25,L`. Starting with 1, generate it by

    two = 1+1,
    four = two*two,
    five = four+1,
    eight = four+four,
    s2 = five*five,
    s4 = s2*s2,
    s8 = s4*s4,
    L = s8*s8.

Here `s2=25`, `s4=625`, `s8=390625`, and the final value is `5^16`.
These are exactly three additions and five multiplications. Replacing
every literal in the 106-operation schedule by its corresponding
constructed register gives a complete 114-operation certificate using
only literal 1. The queried input and the fixed admissible parameters
`x,Z,V,H` retain precisely the same supplied-input status as in the
preceding strict certificates. No construction cost for them is hidden
in this comparison, and no optimality is claimed.
