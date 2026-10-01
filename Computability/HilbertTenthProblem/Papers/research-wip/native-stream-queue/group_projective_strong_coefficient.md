# The retained strong coefficient lowers the six-field polynomial degree

The six-field [computed-checksum compiler](group_projective_computed_checksum_field.md)
admits an exact **eight-degree reduction at unchanged arithmetic cost**.
Use its already computed `Delta(f^2-1)` as the auxiliary norm coefficient
in place of `(ic^2)^2`. The equation equating these two quantities remains
explicitly in the certificate. Thus this is an equivalence on exactly the
same positive witness vectors, requiring no new sign or index argument.

Write, with the same fixed-table and optional-mask hypotheses,

    C=3m+3h+p+185+f_flow-3min(h,3)-epsilon,
    L=m+18 if epsilon=0, L=2m+10 if epsilon=1,
    nu=1+chi.

The new six-field bounds are

    certificate: C+3,
    equations: 10-chi,
    positive witnesses: m+28-chi,
    single SOS polynomial: C+32-3chi,
    exact degree: nu(38L+2m+30)+52.                 (1)

The illustrative ten-letter instance with both optional projections has
**261 certificate / 287 polynomial operations, nine equations, 43 positive
witnesses and exact degree 3368**. Without controller-mask reuse it has
**262/288 operations and degree 2760**, with the same equation and witness
counts. The separate numerical universal 75/88 frontiers are unchanged;
no numerical universal matrix alphabet is instantiated.

## 1. An exact residual transformation

Let `T=ic^2`, `K=Delta(f^2-1)`, `V=of-c` and y be the auxiliary Pell
coordinate. The retained strong comparison is `delta=T^2-K=0`. The
parent norm unit and its replacement are

    N3=T^2(V^2-y^2)+y^2,
    N3'=K(V^2-y^2)+y^2=N3-delta(V^2-y^2).         (2)

Both T^2 and K are already computed. Redirecting one multiplication
operand changes no gate, comparison or supplied coordinate count. The
[source](group_projective_strong_coefficient.py) checks both the literal
gate pattern and the retained strong comparison, then topologically
orders the source so the replacement coefficient is available.

After the checksum projection the full unit product is
`N0*N1*N3*Nk*Nl`. Its residual therefore changes by exactly

    -N0*N1*Nk*Nl*delta*(V^2-y^2).                 (3)

Every other residual is identical, including delta itself. At every
zero of either system delta vanishes, so (2)-(3) prove both directions
of equality of their zero sets. All positive domains and the ordinary
input x are unchanged. No degree reduction is obtained by applying an
equation for free: the replacement uses a paid register and delta
remains an explicit summand in the final SOS.

The parent excludes a negative auxiliary norm unit by a congruence
argument using the square T^2. For the replacement, the retained strong
equality gives N3'=N3 and hence the same exclusion. There is also an
unconditional direct check: Delta and f^2-1 are each zero or three
modulo four, so K is zero or one. Therefore N3' is congruent to y^2
or V^2 modulo four and cannot equal minus one for any integer tuple.

## 2. Exact highest forms

Degree is in the actual supplied coordinates before imposing equations.
Use stars for highest homogeneous forms. As in the parent,

    deg q=nu L, s*=2*odd_half, k*=eta+zeta,
    a*=w*s* q*^2, c*=k*s*q*, V*=-c*.

Here `deg a=2nu L+2`, `deg c=nu L+2`; f and y are supplied coordinates
of degree one. Thus `Delta*=a*^2`, and (2) has the nonzero highest form

    (N3')*=a*^2 f^2 c*^2,
    deg N3'=6nu L+10.                           (4)

The old factor has degree `6nu L+14` and highest form `i^2 c*^6`.
All four other unit factors retain their parent highest forms. The
unit product residual remains the unique largest residual; its square
is the nonzero highest part of the SOS. Replacing its factor by (4)
lowers the exact SOS degree by eight, giving (1).

This substitution is deliberately limited to the six-field variant.
When c is supplied, the old factor's degree is only ten, while the
replacement has degree `4nu L+10`. The earlier four-field packet is
therefore retained unchanged. This is a local degree improvement, not
a claim of an optimal degree at the displayed arithmetic cost.

## 3. Audited source and scope

The [receipt](group_projective_strong_coefficient.json) stores ten compact
ledgers and one full source. Across those variants, 640 positive or signed
assignments verify the exact full residual transformation (3) and final
numeric SOS. Ten exact weighted-offset polynomial evaluations verify
each unit factor's degree and leading coefficient and all residual
degrees. The proof above establishes the symbolic highest forms and
positive zero-set equivalence; finite evaluations are supporting checks.

Run the checker normally for receipt comparison or with `--write` to
regenerate it. All parent sources and receipts remain unchanged.

Independent proof/source/default review passed after correcting the
unconditional modulo-four observation. Another 160 signed assignments
checked the norm directly from supplied scalars, its exact correction,
every unaffected register and the complete SOS.
