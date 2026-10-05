# Independent review of the first unequal-scale Fourier profile exclusion

**PASS; no correction requested.** I read the full frozen note
`/tmp/markov_distinct_scale_first_profile_exclusion.md`, SHA-256
`33231c7f6306a5ad2c6b64a1bf809a2ccee08f7e87274e285ff93ca62d3b8850`,
and its metadata receipt, SHA-256
`31e47e95ab0cfd200a335e62355568eb6fc28ac73ddda95dae2dcea378c6ea2e`.
This is a proof-only independent challenge; no helper, source array,
archived or frozen program was executed or imported.

The exact full-action convention is retained: one positive normalized
doubling mask acts as lambda I, and the other as mu times the decrement
Jordan matrix, with distinct positive scales on the same real finite
trigonometric space. The already reviewed frequency theorem is pinned
at `23e5c13ca92ce1522489c6a54a6905f184daf0023d0a39ef421bd14f911941ee`.

For m=1 the odd part is Bz+conj(B)/z with B nonzero. Its two nonzero
roots are simple and on the unit circle. The common-eigenvector mask
difference forces f(z^2) to vanish at both; the first eigenvector equation
then forces f_even to vanish there. This establishes actual Laurent
divisibility, including all possible common factors of f and g, and
turns a-1 into an odd real Laurent polynomial with extreme degrees ±3.
Continuity fills its two removable values; no division at a pole is used.

The frequency-three coefficient of T_a g forces a_3=lambda; the
frequency-two coefficient of T_a f then forces f_2=f_1=A nonzero.
Vanishing of f_even at the odd-part roots gives f_0=A+conj(A).
The frequency-one equation gives a_1=lambda-1-lambda t,
where t=conj(A)/A. I independently substituted this into the constant
coefficient equation: it reduces to lambda(t^2+t^(-1))=0, hence t^3=-1.
This exhausts all complex phases; no real-coefficient restriction on A
has been added.

For t=-1 or exp(i pi/3), the resulting mask vanishes exactly at
z=exp(i pi/3); for the conjugate phase it vanishes at the conjugate
point. The identity (1-omega)omega=1 gives the second case directly.
Every case contradicts strict positivity, independently of any missing
generic factor case. Positivity of the second mask is not needed after
the continuity reduction, as the note correctly observes.

The predecessor forces maximum frequency 3m. Excluding m=1 therefore
excludes every such space through maximum frequency five. The first
remaining profile under these two notes alone is
`(M_f,O_f,M_g,O_g)=(4,1,6,5)`; neither existence nor impossibility of that
profile is asserted by this packet. Nonnegative masks with zeros,
nontrigonometric coordinates, unnormalized operators and actions only
on a counter ray or zero-test line remain outside its exact theorem.

No numerical search is needed for the argument. This review does not
certify a full integer counter-history construction or any gate saving,
and no repository/Git mutation occurred.
