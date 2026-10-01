# Folding paired selector offsets into one packing bias

Equal offsets in two opposite selector ports cancel from their history
comparison. Collecting those offsets into the selector's existing packing
subtraction can save arithmetic. The rewrite preserves **the entire
polynomial on every integer assignment**, including signed assignments;
all positive witnesses and comparison counts stay unchanged.

The illustrative ten-letter [strong-unit compiler](group_projective_strong_unit_product.md)
now costs **258 certificate / 278 polynomial operations**, with seven
comparisons, 42 positive witnesses and exact degree 3502. The same local
rewrite applies to all three [shared-history variants](group_projective_shared_history_rhs.md).
For a table in which each of the eight physical labels occurs the same
number c>=2 of times, it removes seven operations. Other tables may save
less or nothing; the compiler keeps the parent when no tested plan helps.

This is a fixed-table optimization. It does not assume these label
multiplicities for the abstract universal alphabet, instantiate that
alphabet, or change the separate numerical universal 75/88 bounds.

## 1. The two exact identities

Let c_i be the number of edges carrying physical label i+1, and let
U_i be the sum of their positive edge hats. The parent port is

    Shat_i = 1+sum_(label(e)=i+1)(Ehat_e-1)
           = U_i-(c_i-1)                     if c_i>=1,
    Shat_i = 1                               if c_i=0.

Only ports with c_i>=2 have a private offset-subtraction gate. For a pair
(2j,2j+1) with equal arity c>=2, replace both ports by their already paid
raw sums. The history comparison is unchanged because

    [U_(2j)-(c-1)]-[U_(2j+1)-(c-1)]
        = U_(2j)-U_(2j+1).                              (1)

Choose any subset I of such pairs. Put delta_i=c_i-1 for their ports,
and delta_i=0 for every other port. The raw port pack increases by

    D(P)=sum_(i=0)^7 delta_i*P^i.

The parent subtracts the already paid eight-lane repunit

    R8(P)=1+P+...+P^7

from its Horner pack to obtain Sbatch. Replace that subtraction's right
operand by a paid expression for

    K(P)=R8(P)+D(P).                                    (2)

Then the new Sbatch is exactly the old Sbatch. All following joined
fields, norms, residuals and final outputs are identical. Both (1) and
(2) are polynomial identities with no assumption on positivity, radix
size, binary typing, or whether another comparison holds.

The examples with no selected pair simply retain R8 and the original
ports. Empty ports keep the parent constant one. In particular the
argument does not replace an empty sum by a positive existential field.

## 2. Every cost is paid in a literal circuit

The [source](group_projective_port_bias_folding.py) enumerates at most
sixteen subsets of the four eligible opposite-label pairs. For each it
constructs an explicit arithmetic plan for K, reusing only radix
polynomials already computed by the actual parent source.

A small exact polynomial compiler considers splits at P, P^2 and P^4,
exact factors already available, fixed coefficient factors, and an
available radix polynomial as an additive baseline. Constant folding
uses fixed program data only. A new multiplication by a fixed nontrivial
numeral is charged. Shared new expression nodes are emitted once. This
is a bounded candidate grammar, with no claim of global circuit optimality.

If k pairs are selected and the bias circuit needs b new gates, the
literal saving is

    s=2k-b.                                             (3)

The empty choice costs zero, so the chosen s is nonnegative. If s=0,
the compiler explicitly keeps the parent. It never adds gates solely
to normalize the ports. The multiplication saving is minus the number
of new bias multiplications; the addition saving is 2k minus the number
of new bias additions/subtractions. Thus a beneficial rewrite can trade
some additions for a multiplication while reducing the total count.

The source checks the exact edge-hat sum schedules, all eight port
values, the complete Horner chain, and all four history differences.
Every deleted offset register must have exactly the two expected
consumers: its history difference and its packing gate. None appears
in a retained comparison. A dependency audit stops at the identical
history differences and Sbatch; no other changed register can escape
the packing fragment. The bias cannot reuse a register in that changed
fragment. Its polynomial is evaluated symbolically over integer
coefficient tuples and checked against (2), before source emission.

Topological ordering then verifies that every referenced register is
available. The ordinary input and supplied-coordinate lists are exactly
the parent's lists. No eliminated port, scalar bound or typing equation
is reconstructed as an unpaid runtime gate.

## 3. Useful concrete patterns

In the illustrative ten-letter table the arities are

    (2,2,1,1,1,1,1,1).

Only the first opposite pair is eligible. Here

    K=R8+(P+1).

Both R8 and P+1 already exist, so one new addition replaces the two
private subtractions: **one addition is saved**. The same argument
works if any other, unselected port has arity zero; its baseline port
and constant-one treatment remain unchanged.

If all eight arities equal c>=2, select every pair. Then

    K=c*R8.

One paid fixed multiplication replaces eight subtractions, saving seven
operations. No increase in alphabet size or padding is made to obtain
this result: it applies when the supplied table already has those
arities. The checker includes uniform arities two and three, as well
as an unequal-arity example where the original source is retained.

## 4. Complete ledgers and inherited degree

Use the parent notation

    C=3m+3h+p+185+f_flow-3min(h,3)-epsilon,
    nu=1+chi,
    L=m+18 if epsilon=0, L=2m+10 if epsilon=1.

Here p retains the original port-arithmetic count; subtract the actual
audited saving s from (3) separately. Witnesses and equations are
unchanged from the respective parent:

| Variant | Certificate | Polynomial | Exact degree |
|---|---:|---:|---:|
|Four-field, full SOS|C-2-s|C+33-3chi-s|22nu L+54|
|Six-field, unshifted product|C-2-s|C+27-3chi-s|nu(27L+m+15)+46|
|Shifted-X product|C-2-s|C+24-3chi-s|nu(44L+9m+135)+44|
|Shifted-X strong-unit product|C+1-s|C+24-3chi-s|nu(36L+7m+105)+44|

The last degree has the parent's idle-only supplied-P exception, lower
by two; no port is eligible in that exception. Exact degrees are
inherited because the complete output polynomials are identical.

The illustrative strong-unit table has s=1 for all switch choices:

| Mask reuse | Computed P | Certificate / polynomial | Comparisons / positive witnesses | Degree |
|---|---|---:|---:|---:|
|Yes|Yes|258 / 278|7 / 42|3502|
|No|Yes|259 / 279|7 / 42|2926|
|Yes|No|258 / 281|8 / 43|1773|
|No|No|259 / 282|8 / 43|1485|

The smaller shifted-X certificate costs 255 with eight comparisons and
a 278-operation polynomial of degree 4298. The unshifted supplied-P
choices now give 284 operations at degree 1211 or 285 at degree 995,
each with 44 witnesses. The four-field no-mask supplied-P option gives
291 operations at degree 802 with 46 witnesses.

## 5. Verification and scope

The [receipt](group_projective_port_bias_folding.json) stores 88 complete
option ledgers and one full ten-letter source plus its finalizer.
Across 2,112 supplied assignments, including 704 signed assignments,
it checks the bias polynomial, all surviving registers except the
intentionally shifted private Horner intermediates, all comparisons,
and the entire final polynomial against the actual parent sources.

These evaluations supplement the symbolic bias identity and exact
source dependency audit. They are not a substitute for a parametric
proof, a bounded search for accepted inputs, or a materialized universal
alphabet. Run normally to compare the deterministic receipt, or with
`--write` to regenerate it.

Independent full proof/source review and a fresh default replay passed
without findings. Another 128 signed random-table cases independently
reconstructed Sbatch from edge counts and checked all four history
differences, complete residuals and final outputs.
