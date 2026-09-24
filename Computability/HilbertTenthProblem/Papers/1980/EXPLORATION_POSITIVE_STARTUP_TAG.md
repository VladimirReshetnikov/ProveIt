# Positive startup coordinates give a95-operation tag certificate

The startup of Neary's normalized encoded instances makes four canonical
history coordinates strictly positive. Supplying those values directly,
instead of subtracting1 from positive adapters, reduces the complete
single-zero99 source to **95 operations = 51 multiplications + 44
additions/subtractions**, with **29 positive unknowns and18 equations**.
All nine masks, both transports, true radix geometry and the fixed-plus43
kernel remain. The encoded input is unchanged.

The general arithmetic result has an explicit completeness domain: even
beta>=2, a genuine halt at the single-symbol word0, a nonzero bit beyond
the head in the initial deleted prefix, and at least one genuine selector-one
event before halting. Soundness is actual eventual halting on every valid
encoded input. Neary's source-supported startup and terminal normalization
supply all these promises, so95 is a complete certificate on that encoded
instance family. It is not a fixed-appendant raw-input universal bound.

Author and two independent complete proof/source reviews and fresh
verification runs pass without findings. The maintained [checker](../verification/explore_positive_startup_tag.py)
and [receipt](../verification/explore_positive_startup_tag.json) give both
complete fixed-leading-symbol schedules. The published99 and104 sources
are unchanged.

## 1. Exact source substitution and operation ledger

Use the single-zero99 specialization in
[the zero-terminal parity proof](EXPLORATION_ZERO_TERMINAL_TAG_PARITY.md).
Replace its supplied positive coordinates

    F_Q,F_S1,F_T,F_E

by supplied positive

    Q,S1,T,E.

Here T is the checker's Tcontent register. Delete exactly the four instructions

    Q=F_Q-1, S1=F_S1-1, T=F_T-1, E=F_E-1.

Every later operand already uses Q,S1,T,E. No replacement computation or
new comparison is needed. In particular retain

    M1=2Q+S1,
    N=3T+S1       if the fixed appendant starts with0,
    N=3T-2Q       if the fixed appendant starts with1.

All other supplied coordinates, parameters and18 comparisons are identical
to99. Thus the number of positive unknowns stays29, while four additions
disappear:95=51M+44A. The product q*3 in the fixed length endpoint remains
charged. The checker expands every source in both fixed-leading branches,
using the exact substitutions F_Q=Q+1,F_S1=S1+1,F_T=T+1,F_E=E+1.
It verifies every comparison against its99 counterpart and includes the
retained computed-u norm correction at comparison16.

## 2. Soundness is a positive restriction of99

Given any95 solution, define the four F-coordinates by adding1 to its
positive Q,S1,T,E. These are positive integers. The source identities in
Section1 give a full99 solution with the same raw words, packing, index,
geometry, endpoints and positive Pell auxiliaries. The established99
soundness theorem therefore proves that the specified actual input halts.

The inverse map is a mathematical witness construction, not extra runtime
instructions in the95 certificate. Soundness does not assume the startup
promises used below to prove completeness.

## 3. A sufficient startup condition for completeness

Take a genuine halting trace in the completeness domain stated above. Let
its source contents and markers be n_i and L_i, selectors s_i in{0,1},
and deleted prefixes d_i. Choose the usual sufficiently wide radixR. Its
canonical coordinates are

    S1=sum s_i R^i,
    Q=sum s_i (L_i-1)/2 R^i,
    E=sum (d_i-s_i)/3 R^i,
    N=sum n_i R^i.

All summands are nonnegative. A genuine selector-one event has L_i>=K>=9,
so it makes both S1 and Q strictly positive. The initial-prefix hypothesis
means (d_0-s_0)/3>=1, so E>0.

For a zero-leading appendant, T=(N-S1)/3. The initial-prefix hypothesis
gives n_0-s_0>=3, while all later differences n_i-s_i are nonnegative.
Thus T>=1. For a one-leading appendant,

    T=(N+2Q)/3=(N-S1)/3+M1/3.

Here M1=2Q+S1 has integer nonnegative quotient by3, since every genuine
selected length marker is divisible by3. Hence T>=1 in this branch too.

The zero-edge parity cycle from99 leaves Q,S1,E,N and T unchanged. Thus
both the canonical and padded outer tuples have strictly positive raw
coordinates. Select the even-index member and invoke the fixed-plus43
positive converse. Supply its raw Q,S1,T,E directly to95. This proves
completeness on the stated domain without altering the input, changing
the packed index, or paying an extra parity-selection operation.

## 4. Neary's startup supplies these positivity hypotheses

The relevant primary source is Table2 and the startup argument following it
in [Neary, STACS2015, pp655-656](https://drops.dagstuhl.de/storage/00lipics/lipics-vol030-stacs2015/LIPIcs.STACS.2015.649/LIPIcs.STACS.2015.649.pdf).
Use b=0,c=1. The deletion number is beta=10p with p>=1. The appendant
has length beta*s; the designated input is its suffix starting at beta-1.
The even tracks contain only b, track1 contains only c, and the input
track begins with b^(beta-2). Consequently the input starts b,b,c:
its positions0,1,2 come from appendant positions beta-1,beta,beta+1.
Thus its first deleted prefix and numerical content are at least9.
The appendant starts with b, so the applicable branch is zero-leading,
and the initial contributions give T>=3,E>=3.

The input track ends with p displayed garbage codes b^4 c b^6, so a c
occurs on that track even when the simulated cyclic input is empty.
The paper's size choice, and any enlargement used for terminal normalization,
give s>=11(p+n+beta-2)>=beta. Initially the length is(s-1)beta+1.
Every step deletes beta symbols and appends at least one. Before initial
track read i, for0<=i<s, the length is therefore at least

    (s-1)beta+1-i(beta-1)>=s>=beta.

All s original track symbols are actually read before halting is possible.
In particular a c is selected, making S1,Q positive. This argument uses
only the cited track prefix, its suffix and the two fixed tracks; it does
not depend on interpreting the table's middle-padding notation.

The normalization in the paper's Theorem11 makes every genuine halt end
at a single b. Together with even beta and the startup facts, this supplies
the completeness domain of95. As with99, this is a family whose cyclic
program and input are compiled into the appendant. No uncharged loader
for one fixed appendant and ordinary numerical input is asserted.

## 5. Exact evidence and scope

The source checker reproduces both95 DAGs and all36 source comparisons,
including their exact lifts to99. Its startup arithmetic covers168 size
choices; the three Table2 entries themselves are identified and read in
the proof, not inferred from a finite simulation.

The fresh history regression covers26 genuine traces satisfying the
positive-startup and single-zero conditions, with99 actual source rows.
It constructs52 complete canonical and padded outer tuples, evaluates
all eight comparisons and nine individual masks, and checks all raw
coordinates are strictly positive. Both leading branches occur; the
canonical indices split13 even and13 odd. Thus13 selected even witnesses
need the padding. Exact mask valuations and scale bounds supply the
fresh positive43 extension; enormous Pell auxiliaries are not materialized.

Excluded terminal types, missing startup properties and simulation cutoffs
are recorded separately. These small regression programs are not claimed
to be materialized Neary simulators. The theorem is supported by the
general positive-coordinate proof and the explicit primary-source startup
properties, with finite arithmetic checks validating its implementation.
