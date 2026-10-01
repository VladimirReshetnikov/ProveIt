# Eight paid gates for a fixed-block input and synchronized counter

The boundary below costs **8=5M+3A operations**, one comparison and one
new positive witness, when the recoder already computes `Q-1`. Computing
that subtraction locally gives **9=5M+4A**. Every multiplication by a
fixed numeral is charged. The output is a computed register; equating
it to a separately supplied output adds one comparison.

This is a complete boundary relation **conditional on the typed recoder
inputs and stated word format**. It is not a complete universal tag
polynomial. The [fixed-rule halt bridge](binary_tag_fixed_halt_bridge.md)
supplies the relevant word morphism. Dyadic duration typing and the
machine input-format normalization are separate obligations.

## 1. Word interface

Let the desired binary word be

    PREFIX DATA_w1 ... DATA_wn MIDDLE MU^(m*n) TAIL,

where all capitalized blocks are fixed, `DATA_0` and `DATA_1` have the
same length `D>=2`, `MU` has length `t>=1`, and `D=m*t`. Bits `w1...wn`
are a length-n, most-significant-bit-first binary expansion of positive
ordinary input x, with leading zeros allowed. The counter block therefore
has the same length `D*n` as the data block.

Suppose the recoder supplies

\[
 Q=2^{Dn},\qquad z=\sum_{j\ge0}\operatorname{bit}_j(x)2^{Dj},
 \qquad 0<x<2^n.
\]

No dyadic restriction on n is needed for this boundary theorem itself.
That restriction belongs to the intended machine-counter application.

Write `p=2^|PREFIX|+val(PREFIX)` for the sentinel-coded prefix,
`v0=val(DATA_0)`, `v1=val(DATA_1)`, `f=|MIDDLE|`, `b=val(MIDDLE)`,
`M=val(MU)`, `g=|TAIL|`, and `e=val(TAIL)`. Empty fixed prefix, middle
and tail blocks are permitted. Set

\[
 L=2^D-1,\qquad C_\mu=\frac{2^D-1}{2^t-1}.
\]

`C_mu` is a fixed integer because t divides D. Supply just one new
positive witness r and impose

\[
                         Lr=Q-1.                         \tag{1}
\]

At the typed scale, it uniquely equals the data repunit
`r=(2^(Dn)-1)/(2^D-1)`. The counter repunit is **the same r times a fixed
numeral**:

\[
 \frac{2^{tmn}-1}{2^t-1}=C_\mu r.
\]

Thus the direct sentinel value of the entire word is

\[
 Y_{\rm direct}
 =\left(\left(\left(pQ+v_0r+(v_1-v_0)z\right)2^f+b\right)Q
             +MC_\mu r\right)2^g+e.                    \tag{2}
\]

The data identity follows digit by digit: the constant block v0 occupies
all n positions and the difference v1-v0 occupies exactly the one bits.
It is valid for either sign of that difference.

## 2. Constant folding and the actual source

Precompute the fixed numerals

\[
\begin{aligned}
 A&=2^{f+g}(pL+v_0),& B&=2^{f+g}(v_1-v_0),\\
 T&=2^g\big((2^fp+b)L+MC_\mu\big),&
 E&=2^g(2^fp+b)+e.
\end{aligned}
\]

They depend only on the fixed blocks. Their use as coefficients is
charged at each multiplication; their binary lengths do not depend on
the input or the duration. A variable program prefix cannot be silently
compiled into these numerals; its arithmetic or valid program-parameter
slices require a separate interface. Using (1), equation (2) becomes

\[
                       Y=(Ar+Bz)Q+Tr+E.                 \tag{3}
\]

The complete incremental source, with `modulus` the existing literal
`Q-1` register, is

    repunit_product = L*r          # 1M, compare with modulus
    prefix_data = A*r              # 1M
    data_delta = B*z               # 1M
    data_body = prefix_data + data_delta
    data_counter_scale = data_body*Q
    counter_frame = T*r
    before_tail = data_counter_scale + counter_frame
    tag_input = before_tail + E

There are five multiplications and three additions. This count includes
the relation defining r. It contains no exponentiation, division,
input-dependent coefficient, or uncounted coefficient multiplication.
Shared mode requires the caller's actual `Q-1` register, rather than an
unconstrained supplied value. The standalone source pays its subtraction.

The off-zero correction is explicit:

\[
 Y_{\rm direct}-Y
 =2^g\big(2^fp(Q+1)+b\big)(Q-Lr-1).                   \tag{4}
\]

Thus (3) is equivalent to the direct boundary under its paid comparison;
the two expressions are not claimed identical on arbitrary assignments.
The checker verifies (4) on signed assignments as well.

## 3. Positive domains, degree and scope

For every typed recoder tuple with n>=1, equation (1) has exactly one
positive solution r. Substitution gives exactly the positive sentinel
integer of the displayed word. Conversely, any positive boundary zero
over those typed inputs has that r and that output. This proves both
directions of the conditional boundary relation.

For arbitrary positive Q,z,r before typing, A,T,E are positive. If
`v1>=v0`, B is nonnegative and the output of (3) is unconditionally
positive. If `v1<v0`, positivity is guaranteed only at the typed word
interface. A composition requiring positivity before its typing theorem
must prove the required coefficient order or retain a separately supplied
positive endpoint and its equality. The generic loader does not silently
assume that order.

As a polynomial in independent Q,z,r the output has exact degree two:
its quadratic part is `A*r*Q+B*z*Q`, with A>0. This is a boundary degree,
not the degree after composing a recoder or history. No degree or total
arithmetic count for a complete tag compiler follows from this packet.

The intended counter-reuse format has a fixed dyadic a binary tape cells
per padded input bit and b>0 fixed frame cells. If n is dyadic and an>=b,
then the exact minimal initialization counter is `c0=2an`, since
`an < an+b <= 2an`. For fixed tag-bit block length K and CTS half-period
z0, take `D=2a*z0*K`, `t=z0*K`, and `m=2a`. Both data and counter then
have length Dn. This arithmetic observation still requires a proved
machine format and a paid dyadic-duration recoder. It does not license
replacing the exact counter by an arbitrary larger power of two.

## 4. Executable evidence

The [source](binary_tag_shared_counter_loader.py) exposes fixed-block
`constants`, `build`, `direct`, `folded` and `frame`. The
[receipt](binary_tag_shared_counter_loader.json) records literal ledgers
for both shared/local subtraction and computed/supplied output interfaces.
Signed correction checks are separate from direct string-concatenation
checks at genuine recoder values. The latter include non-dyadic durations
to verify the boundary's broader, precisely stated domain, both block
orders, equal blocks, zero counter words and empty fixed frames.

```sh
python binary_tag_shared_counter_loader.py
```

All finite cases support the elementary concatenation and repunit proof;
they do not instantiate a universal tag production or native Pell zeros.

Author writer/fresh replay and independent proof/source/fresh review pass.
The receipt contains768 correction identities (384 signed),778 literal
frames, and281 positive off-zero definition checks. The independent
review adds1024 actual-DAG string/interface checks across256 fixed block
sets and all four interfaces, plus512 signed correction checks. A separate
2048-case algebra stress test also allowed zero inputs and width1; those
cases are outside this packet's stated positive-input, width-at-least2
interface. No review findings remain.
