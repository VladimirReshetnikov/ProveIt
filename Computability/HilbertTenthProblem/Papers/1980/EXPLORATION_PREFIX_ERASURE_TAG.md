# Deleting the prefix bound accepts every normalized Neary instance

Deleting Ebar from the current nine-mask tag source permits an entire
remaining queue to be erased at a zero-headed step. This is stronger
than a counterexample on an unrelated small tag program: the resulting
system has a complete positive witness for **every normalized Neary
encoded instance**, including the nonhalting ones.

The proposed source has **87 operations: 47 multiplications and
40 additions/subtractions**, with **29 positive unknowns and 18 equations**.
It retains the other eight masks, both transports, true radix geometry,
the fixed singleton-zero endpoint, and the positive fixed-plus43 kernel.
It is unsound and gives no improvement to the valid 91-operation result.

Author and two independent complete proof/source/dependency reviews and
fresh verification pass, including the primary-source startup facts.
The exact evidence is recorded in the
[checker](../verification/explore_prefix_erasure_tag.py) and
[receipt](../verification/explore_prefix_erasure_tag.json).

## 1. Exact proposed source

Use the constants, coordinates and eight outer comparisons of
[the product-coordinate91 certificate](EXPLORATION_PRODUCT_COORDINATE_TAG.md).
In particular D=R/k, Z=AH is recovered by the integer geometry, and

    M1=2Q+S1,
    N=3T+S1        for a zero-leading appendant,
    N=3T-2Q        for a one-leading appendant.

Remove only the Ebar field. The eight retained fields are

    S0=H-S1, S1, Q, G=Q+Z,
    M0=L-M1, M1, E, GN=N+jZ.

Their packing becomes

    P=H+(q-1)S1+q^2[Q+q(Q+Z)]
      +q^4{L+(q-1)M1+q^2[E+q GN]}.                 (1)

Replace the scale q^9 by q^8 in the kernel, index and packed bound.
Deleting ccH, (q-1)E and their sum removes two multiplications and
one addition. The shorter scale saves one more multiplication.
Thus 91=50M+41A becomes 87=47M+40A. The checker verifies both full
leading-symbol schedules, all eighteen source comparisons and the
computed-u norm correction at zero-based comparison16.

## 2. A general whole-content erasure construction

Let beta>=2 be even, a>=2, and suppose

    a=1 mod(beta-1), initial_length=1 mod(beta-1).   (2)

Assume the genuine computation has a finite prefix that starts with0,
has positive initial content beyond the first symbol, reads a1, and
then reaches a source word headed by0. For positive E it is sufficient
that a genuine deleted prefix in this finite prefix contains a nonzero
bit beyond its head, or that the chosen zero-headed source has nonzero
content. Neary supplies the former condition at the initial step.

Keep all genuine source words and transitions up to that zero-headed
word. Write its ternary content and marker as n and L, so 3 divides n.
At this one step replace the prefix quotient by

    e=n/3.                                         (3)

The encoded head selector is still0, and M1row=Qrow=0. Its scalar
content equation now gives

    n-3e-0+U*0=0.

Thus the successor content is0. Keep the ordinary zero-branch length
transition, so the successor length is len-beta+1. Thereafter use
all-zero words of these lengths and ordinary zero transitions. By (2),
the lengths decrease by beta-1 and reach exactly1. The encoded terminal
word is therefore the single zero symbol.

The altered e is Boolean because n is Boolean and its unit trit is0.
The retained E mask accepts it. When the actual tail beyond the deleted
prefix is nonzero, e exceeds cc=(3^(beta-1)-1)/2, and the omitted Ebar
mask is exactly what would reject the step. All other source contents,
selectors and markers are ordinary Boolean words. The length equations
are genuine at every step; only the content erasure is changed.

If the actual initial computation is nonhalting, the tail at the chosen
zero-headed source must be nonzero. Otherwise its next genuine queue
would be all zeros and would halt after finitely many zero transitions.
Thus on nonhalting inputs this construction necessarily uses an invalid
prefix, rather than merely redescribing a genuine halt.

## 3. All positive coordinates, masks and equations

Choose a sufficiently large odd exponent m, with R=3^m=CA, A greater
than every source marker and m>2(beta-1). Pack the constructed finite
source sequence in radix R. All noncontent fields have their ordinary
canonical values. The single altered e remains below its source marker,
so its support fits inside the row. All eight retained fields are
Boolean, nonnegative and below q=R^t; the content guard N+jAH is typed
because every content lies below A.

The earlier genuine selector-one step makes Q,S1 positive. The positive
initial content beyond the head gives T>0 in the zero-leading branch;
the one-leading formula adds the nonnegative quantity M1/3. The prefix
condition in Section2 gives E>0. All other supplied geometry coordinates
and D,Z are strictly positive. The scalar transitions established above
telescope to both complete transport equations, with the unchanged input
and terminal content0/marker3. Choose C to meet its fixed compiler bounds
and K^2 Li<C; for Neary this follows from its fixed input length.

The first field S0 has unit1 because the initial selector is0. With (1),
put D0=q^8 and r=P+(D0-1)/2. The packed slack D0-r is positive, the
native unit-two valuation is exactly 8mt, and all general-scale kernel
bounds hold. It remains to arrange the fixed plus sign's even index.

Sum the eight fields modulo2. Since A,q are odd and j=beta modulo2,

    P=N+E+L+beta*H mod2.

The exponent of D0 is even, so (D0-1)/2 is even. For even beta,

    r=N+E+L mod2.                                  (4)

Use the established wrapped zero-edge construction, with h=beta-1:

    delta=R^t*3*sum((R/k)^i, i=0,...,m-1).

Add delta to M0 and L, increase the height by m-h, and extend q,H and
the guard fields accordingly. Its identity

    ((R/k)-1)delta=3R^t(R^(m-h)-1)

preserves the length transport and the fixed terminal marker. Content,
Q,S1,E,N,T and the initial input are unchanged. The additional M0 bits
are distinct and lie in the new rows; the other retained masks extend
by their usual guard patterns. All eight masks and positivity remain.
The m new bits change L's parity by the odd number m. Equation (4)
therefore shows that exactly one of the two complete outer tuples has
even index. The fixed-plus43 converse supplies sixteen fresh strictly
positive auxiliaries at that chosen index. This gives a solution of
the entire proposed 87-operation source, including its kernel.

## 4. Why this applies to every normalized Neary instance

The primary-source facts are Table2 and its startup traversal, Lemma9,
and Theorem11 in
[Neary, STACS2015](https://drops.dagstuhl.de/storage/00lipics/lipics-vol030-stacs2015/LIPIcs.STACS.2015.649/LIPIcs.STACS.2015.649.pdf).
Their use in this repository is detailed in the
[positive-startup proof](EXPLORATION_POSITIVE_STARTUP_TAG.md) and
[terminal normalization](EXPLORATION_ZERO_TERMINAL_TAG_PARITY.md).

Here beta=10p with p>=1, the appendant length is a=beta*s, and the
designated initial word has length ell=a-beta+1. The normalization
chooses s=lambda*(beta-1)+1, so both a and ell are1 modulo beta-1.
The input begins001, giving strictly positive initial prefix quotient
and content quotient.

The input track ends with p garbage codes b^4 c b^6. Its final c and
the immediately following b are two consecutive original input-track
reads. They occur at read indices s-7 and s-6. Both are reached before
a halt is possible: for every original read i<s, the queue length is
at least

    ell-i(beta-1)>=(s-1)beta+1-(s-1)(beta-1)=s>=beta.

This bound holds regardless of which earlier appendant branches are
taken, since every step appends at least one symbol. Thus the finite
genuine prefix required in Section2 exists for every designated instance,
with a selector1 followed by a selector0. Choosing the latter as the
erasure step gives the complete positive witness above.

Consequently the proposed 87-operation system is satisfiable on every
normalized Neary instance. Neary's simulation includes nonhalting
instances, so this is an obstruction on the full normalized undecidable
family. The argument does not depend on constructing a small appendant
that happens to resemble a few entries of his table.

## 5. Exact finite evidence and its limits

The checker verifies both 87-operation schedules and all36 source
comparisons. Six finite examples exercise both fixed leading branches
and beta=2,4,10, with twelve complete canonical/padded outer tuples.
Each checks every outer comparison, all eight retained masks, strict
positivity, the opposite parities and exact kernel valuations. All six
examples have an erasure quotient beyond the ordinary prefix bound.

The first example has beta=2, appendant0100 and input001001. Its genuine
orbit reaches the certified nonhalting cycle

    001000 -> 10000 -> 0000100 -> 001000.

Erasing content at the third source instead gives an eight-row false
history ending at0; its canonical index is even with exact valuation1216.
The source check includes both canonical and padded outer witnesses.

Twenty-seven normalized startup-size cases check the traversal and
congruence arithmetic used in Section4. The track suffix itself is a
primary-source fact, not inferred from those finite tests. The examples
are not materialized Neary simulators. The full-family statement follows
from the general erasure construction and the verified source promises;
large Pell auxiliaries are supplied by the proved converse.
