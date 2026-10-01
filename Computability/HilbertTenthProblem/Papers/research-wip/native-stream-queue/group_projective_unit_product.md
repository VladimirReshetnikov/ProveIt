# Two norm factors share the checksum comparison

Three comparisons in the complete
[shifted-boundary compiler](group_projective_shifted_boundary.md) can be
replaced by one product equation. The certificate adds two multiplications,
while its single sum-of-squares polynomial saves **four additions**.
No witness, typing condition, scalar bound or accepted ordinary input
changes. An optional reuse of the existing controller mask saves one more
multiplication for m>=8, with its degree tradeoff stated separately.

Let the shifted-boundary parent's certificate cost be

    C0=3m+3h+p+184+f_flow-3min(h,3).

Here m=2^h is the padded edge count, p the paid physical-port cost and
f_flow=f_M+f_A the sparse-flow cost. The two original field-elimination
variants give the following complete successor ledgers:

| Supplied-field variant | Certificate | Equations | Positive witnesses | SOS polynomial | Exact degree |
|---|---:|---:|---:|---:|---:|
|four computed fields|C0+2|20|m+36|C0+61|12m+232|
|six computed fields|C0+2|18|m+34|C0+55|36m+674|

The four-field degree is unchanged by the product. The six-field degree
increases from 24m+444. All fixed numerals and squares remain charged.
These are complete fixed-table formulas, not numerical claims about an
instantiated universal alphabet or improvements on the separate75/88
frontiers.

## 1. Two integers that cannot be negative units

Use names from the retained selection kernel:

    Delta=(a+2)^2-1, T=ic^2, U=jc-(2r+1),
    N1=d^2-Delta*c^2,
    N3=T^2*(U^2-y^2)+y^2,
    Q=q-(F0+F1+F2+F3).                             (1)

All are integer polynomials even on arbitrary signed supplied assignments.
The old three comparisons are exactly N1=1, N3=1 and Q=1. In particular,
N3 uses the actual square T^2 from the source; it does not replace that
square by the strong-auxiliary equation's other side.

Modulo four, Delta is zero or three. Thus N1 is congruent either to
d^2 or to d^2+c^2, neither of which is three modulo four. Hence N1
cannot equal -1. Also T^2 is zero or one modulo four, so N3 is congruent
respectively to y^2 or U^2. It too cannot equal -1. These exclusions
are unconditional: they require no Pell equation, positive-coordinate
assumption, scale typing, strong-auxiliary comparison or checksum.

It follows over the integers that

    N1*N3*Q=1  iff  N1=N3=Q=1.                   (2)

Indeed an integer product equal to one has each factor equal to +1 or
-1. The first two exclusions force both norm factors to +1, and then
force Q=1. The converse is immediate. No separate exclusion for the
otherwise unrestricted integer Q is needed.

Equation (2) restores all three original comparisons before invoking
any native-selector or geometric theorem. Thus the entire parent's
positive typing proof applies in its original order. The replacement
has exactly the same positive solution tuples, not merely the same
accepted inputs.

## 2. Literal gates and an off-zero residual identity

The old source already pays for d^2, Delta*c^2, T^2*(U^2-y^2), y^2,
q and the sum of its four fields. Make only these three gate changes:

| Old gate | New gate |
|---|---|
|R15=Delta*c^2+1|R15=d^2-Delta*c^2=N1|
|P17=1-y^2|P17=T^2*(U^2-y^2)+y^2=N3|
|bs_q=F0+F1+F2+F3+1|bs_q=q-(F0+F1+F2+F3)=Q|

The displayed sums on the right are existing registers, not newly
expanded expressions. Each changed instruction remains one addition or
subtraction. Add `unit_pair=N1*N3` and `unit_product=unit_pair*Q`.
Replace the three old comparisons by `unit_product=1`. A stable
topological sort moves their new definitions after their operands.
No other source register uses the three changed result registers.

Write the old residuals with their actual source orientations as

    Rmain=N1-1, Raux=N3-1, Rchecksum=1-Q.

The replacement residual is the exact polynomial

    Rnew=(Rmain+1)*(Raux+1)*(1-Rchecksum)-1.        (3)

Every other residual is identical on arbitrary integer assignments.
The new SOS therefore equals the old SOS minus these three old squares
plus Rnew^2. This identity is audited directly; no old comparison is
silently used to simplify an off-zero polynomial.

If the parent has e comparisons, the new certificate has e-2 and costs
C0+2. Its SOS costs

    C0+2+3(e-2)-1 = C0+3e-5,

four less than the parent's C0+3e-1. The two additional certificate
multiplications are canceled in the SOS ledger by two fewer residual
squares; the net saving is exactly four additions.

## 3. Optional controller-mask reuse for m>=8

This is a separate arithmetic/degree variant. Keep all scalar history,
output, checksum, margin and repunit bounds. In the range compiler let

    Mc=J*(1+P+...+P^(m-1)), Hb the eight-lane history pack,
    T0=P^(m+8),
    H0=Hb+P^8*Hc, M0=Mb+P^8*Mc, Z0=Zb+P^8*Hc.

The original range mask is R8=(2D-1)J*(1+P+...+P^7), paid by two
multiplications after the already computed range coefficient 2D-1.
For m>=8 replace it by

    Rm=(2D-1)*Mc.                                (4)

This needs one multiplication. Enlarge that range region from eight
to m base-P lanes:

    T2=T0*P^m,
    H=H0+T0*Hb+T2*B,
    M=M0+T0*Rm+T2*(B-1),
    Z=Z0+T0*Hb,
    N=T2*P^2=P^(2m+10), q=16N.                   (5)

The existing P^m register is available from the joined controller source.
Changing the second operand of the T2 multiplication adds no gate.
All other region-building operations remain. Hence this variant saves
exactly one multiplication in both the certificate and its polynomial.

To justify (5) without circular digit assumptions, first restore the three
comparisons by (2), so the exact native AND theorem is available. The
retained scalar comparisons imply

    P=(B-1)J+1, B=8D>=32, B<=P<P^2,
    0<=(2D-1)J<P,
    0<=Hb,Mb,Zb<P^8, 0<=Hc,Mc<P^m.

Therefore Rm<P^m and Hb<P^m, using m>=8. All three lower regions
H0,M0,Z0 remain below T0. The body regions are below T2, and the top
two-lane coefficient is below P^2. This bounds H,M,Z<N before any
Boolean interpretation.

The exact scalar AND makes N, hence P, a power of two. Separating the
regions then gives the same four obligations as before:

    Hb AND Mb=Zb, Hc AND Mc=Hc,
    Hb AND Rm=Hb, B AND (B-1)=0.                  (6)

The last relation types B; the retained repunit then recovers P=B^t
and J=1+B+...+B^(t-1), with t>=1. Because Hb<P^8, its new mask test
in (6) depends only on the lowest eight lanes of Rm, which are exactly
R8. Thus it forces precisely the same range 0<=X_i(j)<2D. The extra
m-8 lanes of the range mask meet zero history lanes and impose nothing
else. All selected-source, chronological controller, carry-free history
and endpoint proofs are unchanged.

Conversely, every genuine accepted word still gives positive outer
fields satisfying (6), and the same bounds prove H,M<N. Choose the
fresh positive native AND extension at the new scale16P^(2m+10).
This proves the same complete positive ordinary-input predicate.
It does not claim a bijection between native witness tuples at different
scales. At m=8 the masks, scale and all remaining registers are literally
the same; there the one-multiplication saving has no degree cost and
preserves the positive tuples exactly.

For m<8 this variant is not offered: Mc does not contain all eight
history lanes. The default eight-lane source works for every m>=2.

## 4. Complete arithmetic and degree tables

Let epsilon be zero for the original eight-lane range mask and one for
the controller-mask variant, the latter requiring m>=8. Put

    L=m+18 if epsilon=0, L=2m+10 if epsilon=1.

The complete certificate has the exact split

    M=m+2h+82+f_M-d_M-epsilon,
    A=2m+h+p+104+f_A-d_A,

where (d_M,d_A) is (1,2) for h=1, (3,3) for h=2 and (5,4) for h>=3.
Its total is C0+2-epsilon. The SOS splits are

    four fields: M=m+2h+102+f_M-d_M-epsilon,
                 A=2m+h+p+143+f_A-d_A;
    six fields:  M=m+2h+100+f_M-d_M-epsilon,
                 A=2m+h+p+139+f_A-d_A.

Thus the polynomial base constants, excluding the inherited
3m+3h+p+f_flow-3min(h,3), are245-epsilon and239-epsilon.
The witness and comparison counts remain those in the opening table.

For degree, treat all supplied coordinates as degree one and fixed
compiler numerals as degree zero. Write highest homogeneous parts as
stars. In both variants

    q*=16P^L, s*=2*odd_half, k*=eta+zeta,
    a*=w*s* (q*)^2.

In the four-field variant c,r remain supplied. The product residual
has degree at most5L+16: the main norm has degree at most4L+6,
the auxiliary norm at most ten, and Q degree L. Since L>=20,
5L+16<6L+8. The first native norm remains the unique highest residual,
with highest part w^2*(s*)^4*(k*)^2*(q*)^6. Thus the SOS has exact
degree12L+16 in this variant.

In the six-field variant

    c*=k* s* q*,
    F3*=16 H2 P^(m+15),
    r*=(q*)^3 F3*=16^4 H2 P^(3L+m+15).            (7)

The joined output Z is unchanged by the optional mask enlargement;
its dominant term is still P^(m+8) times the highest history lane.
This explains why m and L are separate in (7).

There is a necessary cancellation in the main norm. From
d=ac+ga*(4a+3)+X, its leading a^2 c^2 term cancels the corresponding
term in Delta*c^2. The remaining unique highest part is

    N1*=8*ga*(a*)^2*c*, degree5L+7.              (8)

The auxiliary norm has highest part i^2*(c*)^4*(2r*)^2, of degree
10L+2m+42; Q*=q*. Therefore the product residual has unique highest
part

    [8*ga*(a*)^2*c*] * [i^2*(c*)^4*(2r*)^2] * q*,

of degree16L+2m+49. It dominates every unmerged residual. Squaring
gives exact SOS degree32L+4m+98. The resulting degree table is

| Computed fields | Eight-lane mask | Controller mask, m>=8 |
|---|---:|---:|
|four|12m+232|24m+136|
|six|36m+674|68m+418|

The columns coincide at m=8. No equation such as P=B^t is substituted
when calculating these degrees, and no cancellation between distinct
highest squares is assumed.

## 5. Source and independent formulas

The [source](group_projective_unit_product.py) exposes
`build(codes, alpha, beta, variant, controller_mask)`. The two field
variants are `four` and `six`; the mask option defaults to false.
It asserts the m>=8 domain when the option is true. The source retains
all scalar bound gates and witnesses, so the pretyping argument has
not been weakened by dropping a bound.

The [receipt](group_projective_unit_product.json) contains twelve full
literal DAGs and SOS ledgers over m=2,4,8,16. Across1,536 assignments,
including384 signed cases, the checker compares every residual with
independently expanded original native/history formulas and (3), checks
all unaffected registers against the appropriate range source, and
verifies the entire SOS. It includes the native strong-equation
correction in the manual residual; no zero-set reduction is used.

Twelve weighted offset univariate evaluations check the actual DAG's
exact degree and highest coefficient, including cancellation (8).
The full128 residue classes for the two modulo-four exclusions are
checked. Another384 Boolean region fixtures over m=8,16,32 verify
the enlarged AND, its canonical zero digits and both positive scalar
bounds, the identical m=8 mask, and rejection of a forbidden range bit.
These are audits of the exact algebra and interfaces, not finite tests
offered as a proof of universality or materialized full Pell solutions.

Run the source normally to compare the deterministic receipt, or use
`--write` to regenerate it. The shifted-boundary parent and all earlier
packets remain unchanged.
