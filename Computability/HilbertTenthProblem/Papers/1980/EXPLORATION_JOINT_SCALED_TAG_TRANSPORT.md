# Sharing both transport scales for a zero-leading tag appendant

For a fixed binary appendant of length at least two whose first symbol is
zero, the established encoded-word tag interface has a complete
**105-operation certificate: 53 multiplications and 52 additions**, with
**34 positive existential unknowns and 21 equations**. This is a restricted
successor to the frozen
[106-operation interface](EXPLORATION_SHARED_MARKER_LOW_PACKING.md).
The same two encoded-input parameters are retained. No ordinary numerical
input loader or universal operation bound is asserted.

Every new positive solution maps to a positive106 solution with the same
packed integer, index and Pell witnesses. Every actual halting history has
a canonical new solution. We do not assert that every formal106 tuple
continuing after a genuine halt admits the new parameterization.

## 1. Constants, inputs and the shared divisor

Keep the predecessor's deletion number `beta>=1` and the little-endian
binary word convention. Let the nonempty appendant `u` have length `a>=2`
and first symbol zero. The constants are

    K=3^beta, Kh=K/3, B=3^(a-1), U=value(u),
    c=(Kh-1)/2.

In particular `U=3U3` for the fixed nonnegative integer `U3=U/3`.
The fixed radix coefficient `C` is a power of three with

    C>max(K,3^a,2U+3).

Thus `Cbar=C/Kh` is a fixed positive integer. These divided constants
are chosen at compilation time; there is no division operation in the
certificate. Multiplication by each such constant remains a counted
operation.

The supplied parameters still describe a specified binary word `w`:
`Linit=3^|w|`, `Ninit=value(w)`, and `|w|>=beta`. All digits are zero or
one in radix three. The fixed rules are `0 -> 0` and `1 -> u`, with
deletion number `beta` and halting at the first word shorter than `beta`.

The old two transport equations are

    R(N-3E-S1+U M1)=K(N-Ninit+q Nfinal),
    R(L+(B-1)M1)=Kh(L-Linit+q Lfinal).                (1)

They coexist with the paid relation `R=CA`, all original geometry,
the ten conceptual Boolean fields and the unchanged parity-free Pell
kernel. The selected marker remains `M1=2Q+S1`.

## 2. The nonnegative content parameterization

Replace the supplied positive coordinate `F_N`, which formerly gave
`N=F_N-1`, by a positive coordinate `F_T`. Compute

    T=F_T-1, three_T=3T, N=three_T+S1.               (2)

Here `S1=F_S1-1` is already nonnegative for every positive supplied tuple.
Thus `T>=0` and `N>=0` hold before power, mask or history decoding.
The old positive coordinate is recovered by

    F_N=N+1=3F_T+F_S1-3 >= 1.                        (3)

This is a literal positive-domain embedding. No division, congruence,
mask property or assumption about a decoded selector is used in (3).
The new parameterization is allowed to restrict the set of formal
witnesses; its canonical completeness is proved below.

Using (2) and `U=3U3`, the old content output factors as

    N-3E-S1+U M1=3(T-E+U3 M1).                      (4)

Define a shared arithmetic register

    D=Cbar*A, radix=Kh*D,

and retain the free equality `radix=R`. Both equations (1) are then
equivalent to

    D(T-E+U3 M1)=N-Ninit+q Nfinal,
    D(L+(B-1)M1)=L-Linit+q Lfinal.                   (5)

All quantities divided in this argument are fixed positive constants.
The system itself evaluates (5) solely by integer addition and
multiplication. Its intermediate `T-E+U3 M1` may be negative on an
arbitrary tuple, as permitted by the straight-line convention.

## 3. Exact source correspondence and soundness

Let `f0=Kh*Cbar*A-R` be the unchanged radix source residual, and let
`fC,fL` be the residuals of (5), left side minus right side. Write
`O=T-E+U3 M1` and `OL=L+(B-1)M1`. After substitution (3), the two old
residuals satisfy the unconditional polynomial identities

    old_content = 3Kh*fC - 3*f0*O,
    old_length  = Kh*fL - f0*OL.                    (6)

All eight other outer source residuals are identical to106 under (3).
In particular, the reconstructed `N` has exactly the same value in the
content interval, the conceptual complement `Nbar=Nsum-N`, the packed
word and its index equation. Geometry is not discarded or assumed free.

Consequently every positive solution of the new 21 equations becomes
a positive106 solution by (3), keeping every other supplied coordinate
unchanged. Identity (6) establishes both transport equations; the eleven
kernel equations and their acyclic norm correction are unchanged.
The full106 theorem now proves that the encoded input word really halts.

This order also supplies every pre-kernel bound without a new bootstrap:
the old nonnegative `N` domain follows immediately from (2), all old
outer equations follow algebraically from (6), and only then are the
established106 bounds and decoding results applied. No step requires
the new quotient `T` to be a Boolean word. It is not an extra mask field.

## 4. Canonical completeness and preserved Pell witnesses

Suppose the specified tag computation halts, and stop its history at
the first genuine halt. For each source row `j`, let `n_j` be the
nonnegative little-endian word value and `s_j` its first symbol. The
source word has length at least `beta>=1`, so

    n_j>=s_j,  n_j=s_j mod 3.

The canonical aggregate values are `N=sum n_j R^j` and
`S1=sum s_j R^j`. Hence

    T=(N-S1)/3=sum ((n_j-s_j)/3)R^j                  (7)

is an integer and is nonnegative, including histories where it is zero.
Take `F_T=T+1`. All other supplied coordinates are those of the
canonical106 witness at the same chosen width.

The fixed constant quotient makes `D=Cbar*A` positive, and its paid
product gives `Kh*D=R`. Equations (1), (4) and positive `Kh` imply (5).
Thus all ten outer comparisons hold. The conceptual field order remains

    Gstar, Q, S0, S1, M0, M1, Ebar, E, Nbar, N.

Their values, packed integer `P`, index `r`, scale `q^10` and positive
packing slack are identical to the canonical106 values. The same
seventeen positive Pell auxiliaries therefore work without reconstruction.
The parity-free44 kernel handles both parities of the unchanged index.
Terminal word value zero is still represented by `F_Nfinal=1`.

Equations (3) and (7) prove the needed implications between halting and
existence of positive witnesses. They do not claim that an arbitrary
formal106 continuation after an earlier short word has `N-S1` divisible
by three. Such a claim is unnecessary: soundness uses the embedding (3),
and completeness uses a history stopping at its first halt.

## 5. Full arithmetic accounting and the unrestricted tie

The complete changes from106 are:

| Part | Old cost | New cost | Change |
|---|---:|---:|---:|
| Content adapter | `N=F_N-1`: 1A | (2): 1M+2A | +1M+1A |
| Content output | `3E`, `+S1`, `UM1`, `N-d`, `+`: 2M+3A | `U3*M1`, `T-E`, `+`: 1M+2A | -1M-1A |
| Radix computation | `C*A`: 1M | `Cbar*A`, `Kh*D`: 2M | +1M |
| Two transport right sides | fixed `K*` and `Kh*`: 2M | compare the already computed shifts directly | -2M |

The two left products remain two multiplications; they use `D` instead
of `R`. The terminal products `q*Nfinal` and `q*Lfinal`, both endpoint
differences and all joins remain fully counted. The net change is one
removed multiplication, yielding **105=53M+52A**.

There are still 34 positive supplied coordinates: `F_T` replaces
`F_N`. There are still ten outer and eleven kernel equations. The new
register `D` is computed, not a free positive witness. All old uses of
the supplied `R`, including both geometry equations, remain intact.

For a general appendant, scaling by `D=R/Kh` without (2)--(4) gives

    D*Cout=3*Cshift, D*Lout=Lshift.

The retained multiplication by three cancels the potential saving:
one added multiplication builds the shared scale and reconstructs `R`,
while only one of the two right-side constant multiplications disappears.
The checker constructs this generic alternative and counts exactly106.
This is an accounting tie for that explicit rescaling, not a lower bound
for all generic transport implementations.

The restriction `3|U` is substantive. For a binary appendant it is
equivalent to its first symbol being zero. No recoding of an arbitrary
tag program to this subclass is asserted, and no input alphabet or
initial-word encoding is changed.

The restriction does include the specific halting construction in
[Neary's Lemma 9 and Table 2](https://drops.dagstuhl.de/storage/00lipics/lipics-vol030-stacs2015/LIPIcs.STACS.2015.649/LIPIcs.STACS.2015.649.pdf#page=7).
Table 2 sets track zero to all `b` and track one to all `c`, so its
appendant begins `bc`. Under `b=0,c=1`, its little-endian ternary value
therefore satisfies `U=3 mod 9`, and its length is at least two.
This verifies compatibility with that construction's appendant; its
special input track places the chosen cyclic-tag input inside the
constructed appendant. It does not provide an ordinary numerical-input
loader or establish one fixed appendant for all inputs. The earlier
nonhalting simulation in Table 1 has a different first symbol.

## 6. Fresh verification and evidence boundary

[explore_joint_scaled_tag_transport.py](../verification/explore_joint_scaled_tag_transport.py)
constructs the complete105 DAG over the frozen106 dependency. It
independently checks all 21 source residuals, the unchanged kernel norm
correction, both identities (6), the exact positive-coordinate substitution,
and preservation of the complete packed word and index. It also counts
the generic106 rescaling described above.

The focused polynomial regression checks864 tuples, including192 signed
content outputs, failed radix equations, a nonpower `q`, and zero raw
coordinates. These are exact identities rather than complete solutions.

Fresh canonical construction covers448 halting histories and1,238 source
rows. Every case evaluates the actual105 and106 prefixes, all ten outer
comparisons in each version, all ten conceptual Boolean fields, the
native mask and exact index valuation. All448 indices are preserved:
300 are even and148 odd. There are49 histories with `T=0` and384
with terminal content zero. The140 searches reaching the finite cutoff
remain unclassified.

Enormous Pell auxiliaries are not materialized; their positive existence
and preservation use the same complete106 converse. This result is a
conditional encoded-word certificate with an explicit appendant
restriction, separate from the ordinary-input universal frontier.
Author and two independent complete proof/source reviews and fresh
verification runs pass; the construction and arithmetic are frozen.
