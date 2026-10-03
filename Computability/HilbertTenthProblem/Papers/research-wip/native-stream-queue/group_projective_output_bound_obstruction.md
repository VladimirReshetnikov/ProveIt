# Deleting the output bound gives a false endpoint on an empty table

The positive global output bound in the
[padded-margin compiler](group_projective_padded_program_margin.md)
cannot simply be projected out. There is a fixed eight-edge macro table
whose genuine paired-action language is empty, but the proposed relaxed
compiler accepts **every positive ordinary input**. All remaining scalar
comparisons, the four claimed endpoint transports and the exact joined
AND hold, with a full positive native extension.

The failure is within the generic fixed-table compiler theorem. It is
not a separately demonstrated false input for the specific uninstantiated
universal subgroup alphabet. It rules out this uniform deletion and the
suggested positive graph-substitution proof; it is not a lower bound on
alternative output encodings or other arithmetic certificates.

## 1. The proposed one-coordinate projection

The compiler supplies eight positive output hats and a positive slack:

    Zi=Zhat_i-1>=0,
    sum_(i=0)^7 Zhat_i+bound_global=P+1.             (1)

The existing sum is already paid. A tempting change replaces its final
addition by the subtraction

    computed_bound=P+1-sum_i Zhat_i,                (2)

then deletes (1) and the supplied bound_global. It has the same
certificate gate count and apparently saves one witness, one equation
and three operations in the SOS. The computed value (2), however,
has no positive-domain constraint once the supplied coordinate is erased.

The counterexample below makes (2) strictly negative at full positive
zeros of the relaxed system. More strongly, it changes the accepted
ordinary-input relation. The [source](group_projective_output_bound_obstruction.py)
implements exactly this rejected projection for all four/six native-field,
eight-lane/controller-mask and supplied/computed-P variants. Its
[receipt](group_projective_output_bound_obstruction.json) does not promote
their apparent three-operation saving to an established compiler bound.

## 2. A fixed table with no genuine accepted word

Use precisely the six one-letter macro codes

    (3), (4), (5), (6), (7), (8).

In the inherited four-register convention these are the two signs of
the first block's lower shear and both signs of both shears in the
second block. The padded controller has m=8 edges, including its hub
idles. The alphabet is closed under inverses.

Every first-block product is a lower triangular unipotent matrix
`[[1,0],[n,1]]`. Acting on the required input (1,u) it preserves the
first coordinate at one. Therefore it can never reach e2=(0,1), for
any word or any u. The genuine paired-action language is empty.

Fix any positive alpha,beta with alpha+beta+1>=8. For every ordinary
x>0 put u=alpha*x+beta+1>=8. This meets the actual padded-margin
compiler hypothesis for this one fixed table; neither the table nor
the program constants vary with x.

Consider the chronological physical word

    8^(u-1), 6, 4^u,                              (3)

where the superscripts mean repetitions, not free gates in the
certificate. Its duration is t=2u. The first segment lowers the fourth
coordinate from u to one; the letter6 then zeros the third coordinate.
The final u lower shears zero the second coordinate. Thus the true
signed trajectory has

    initial=(1,u,1,u), true terminal=(1,0,0,1).      (4)

This is a legal hub-to-hub macro word. Its first coordinate remains one
throughout, as required by the invariant. The terminal (4) differs
from the claimed terminal (0,1,0,1) in exactly the first two coordinates.

## 3. All genuine scalar, range and selector data

Choose any power of two D>u+1, and set

    C0=D-1, B=8D, P=B^t, J=(P-1)/(B-1),
    Omega=P/B=B^(t-1).                            (5)

Use the actual shifted histories C0+state for (3), the genuine edge
indicators and physical selectors. All shifted digits lie strictly
between zero and2D, all four packed histories are positive, and their
sum is less than P. Hence the retained history-bound slack is positive.
The positive height slack is D-u; B>m follows from the fixed-numeral
margin. J and optionally P are exactly their computed scalar definitions.

Let Ti be the true eight selected-source words for these histories.
Only three physical letters are used, giving

    T0=T1=T2=T4=T6=0,
    T3=D*B^u*(B^u-1)/(B-1),
    T5=D*B^(u-1),
    T7=D*(B^(u-1)-1)/(B-1).                       (6)

In particular T3>=D*Omega>Omega. The coefficient D occurs because
each selected source has signed value one, hence shifted value C0+1=D.

The exact controller and range predicates hold for these genuine data.
Their lower selected-source AND has output

    Zb_true=sum_i Ti*P^i.

Every Ti<P. Moreover one physical letter acts per cell, so
`sum_i Ti<=(2D-1)J`. Thus the genuine output slack

    beta_true=P-7-sum_i Ti>=6DJ-6>0               (7)

is positive. These statements do not assert that the genuine histories
meet the claimed endpoint: their four transport residuals are instead
(P,-P,0,0), by (4).

## 4. A packed alias that cancels the false endpoint

Define the positive integer

    G=Omega*P*(P-1).

Replace the individual output words by

    Z0=G, Z1=G+Omega, Z2=0, Z3=T3-Omega,
    Zi=Ti for i=4,5,6,7.                         (8)

All Zi are nonnegative, and every supplied Zhat_i=Zi+1 is strictly
positive. By (6), even Z3 is strictly positive. Their packed word is
unchanged, because

    sum_i (Zi-Ti)P^i
      =G(1+P)+Omega*P-Omega*P^3
      =0.                                       (9)

Consequently the complete joined output Z is unchanged. Histories,
selectors, radix and scale are unchanged too, so the complete joined
H,M,Z,q and all four padded truth fields stay exactly the same. The
scalar AND remains true at its proper prescribed scale, with H,M below
that scale. No carry has contaminated its controller, range or radix
regions.

The individual paired differences, however, change by

    (Z0-Z1)-(T0-T1)=-Omega,
    (Z2-Z3)-(T2-T3)=+Omega,
    other paired differences unchanged.          (10)

Each transport has actual residual

    B*(Hi+Z_(2i)-Z_(2i+1)-C0*(S_(2i)-S_(2i+1)))
       -Hi-Ei*P+Ii.                             (11)

With the true products, (4) gives residuals (P,-P,0,0).
Equation (10) changes them by (-B*Omega,+B*Omega,0,0).
Since B*Omega=P, every claimed transport in (11) is now exactly zero.
The same histories which actually end at (1,0,0,1) therefore satisfy
the relaxed certificate's comparisons to (0,1,0,1).

Meanwhile

    sum_i Zi=sum_i Ti+2G,
    computed_bound=beta_true-2G<0.                (12)

Indeed beta_true<=P-7, whereas G=Omega*P*(P-1) and P>=32. The omitted
positive bound rejects precisely this assignment.

This is stronger than a harmless common shift of two paired outputs.
The paired differences really change, and cancel a wrong endpoint.
No normalization preserving them can restore the genuine selected
products: if all Zi<P, (9) and uniqueness of radix-P expansion would
force Zi=Ti, contradicting (10). Nor can a different normalized history
or macro word accept the same x on this table, because its first-block
invariant rules out every genuine endpoint.

The packed bound Zb<P^8 itself still holds in this counterexample:
Zb equals Zb_true. Therefore replacing (1) merely by a bound on the
aggregate packed output would not suffice. The missing condition is
also needed to prevent noncanonical individual lanes from altering
the four differences consumed by the histories.

## 5. A full positive relaxed zero, not only a formal carry pattern

Every retained non-native comparison has now been established: the
actual chronological controller, computed J/P, positive history bound,
range and radix tests, both scalar input ports, and all four claimed
transports. Each retained supplied outer coordinate is strictly positive.

Apply the exact prescribed-scale AND converse from
[selector63](native_binary_masked_selection63.md) to the unchanged
nonnegative H,M,Z and dyadic scale. Its four-bit prefix makes all four
truth classes positive. It supplies every remaining positive native
auxiliary. The computed native-field substitutions and the unconditional
unit-product equivalence transfer this extension to each current variant.
Neither local theorem assumes that the eight output lanes already have
their intended selected-source interpretation; that was the missing
global bound's job.

Thus the huge positive native extension exists at these exact outer
fields. No use is made of the full correct compiler's endpoint theorem
to infer it: that theorem would reject (4). The extension uses only
the separately proved scalar AND component, whose contract is fully
satisfied by (9).

For this fixed table and every fixed positive alpha,beta satisfying
alpha+beta+1>=8, the two exact ordinary-input projections are therefore

    genuine/compiler-with-bound language = empty set,
    proposed relaxed compiler language = all positive integers.   (13)

This holds for both native-field variants, both range-mask variants
(m=8 satisfies the reuse condition), and both supplied/computed-P variants.
The fixed alphabet and constants remain unchanged as x varies.

Equation (13) disproves the uniform fixed-table compiler obtained by
this projection. It does not claim that the same three-letter word
exists inside the separately fixed universal subgroup alphabet, or
settle the language of a relaxed certificate specifically restricted
to that alphabet. Any further universal optimization would need a
different sound argument or a replacement condition excluding (8).

## 6. Executable evidence and boundaries

The checker constructs the rejected source at unchanged certificate
cost, removes exactly the one positive output slack and comparison,
and verifies the apparent three-operation SOS saving. One complete
rejected DAG and compact ledgers are stored in the receipt.

Twenty-four genuine-history fixtures cover all eight compiler variants
at (alpha,beta,x)=(1,6,1),(24,12,1),(24,12,2). They construct the
histories and both true/fake selected fields, verify (6)–(12), check
every retained outer comparison, and compare every native input and
native residual before and after the alias. The minimal case has u=8,
D=16 and duration16, meeting the fixed-numeral margin exactly.
Its native Pell coordinates are explicit placeholders: their existence
as full positive extensions is proved in Section5, not claimed as a
numerically materialized witness tower.

Another512 assignments, including128 signed cases, independently audit
the full residual response to the algebraic perturbation (8), with
arbitrary Omega: only the first two residuals change, by exactly
-B*Omega and+B*Omega, and the complete SOS matches those changes.
The source checks the empty-language matrix invariant for each fixed
generator and256 further words; the all-word conclusion follows
algebraically from closure of lower triangular unipotent matrices.

Run the source normally to compare the deterministic receipt, or use
`--write` to regenerate it. Parent packets and established arithmetic
frontiers remain unchanged.

Two independent full proof/source reviews passed without findings; the
author and one reviewer also replayed the default receipt successfully.
They checked the empty-table invariant, the closed-form selected fields,
the exact packing and endpoint signs, and the standalone native extension
without invoking the failed full-compiler conclusion. One review added96
independent closed-form trajectory/selection fixtures for u=8 through39
at three dyadic heights each, verifying every required positivity and
the exact true/fake transport residuals. Both reviews confirmed the
generic-table scope of the false-input theorem.
