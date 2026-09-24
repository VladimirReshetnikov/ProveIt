# A single omitted counter track permits a signed underflow

The guarded-content argument for tag histories does not justify dropping a
numerical track mask from the universal counter architecture. Here is a
specific obstruction: retain the guard `t-A0` but omit the mask on `A0`.
An otherwise exact controller path can decrement an initially zero counter
below zero, restore it, and reach the accepting endpoint. **Every requested
source-zero test in this counterexample is an actual zero.** The failure is
loss of counter nonnegativity, rather than an incorrect zero label.

The construction below gives full positive false witnesses for a literal
diagnostic source with **103 operations = 57 multiplications + 46 additions
or subtractions**, 34 positive unknowns and 22 equations. Its extra three
operations put zero in the omitted slot while retaining the twelve-slot
scale. This count is not proposed as an improvement or as a minimum cost
for removing that mask. The purpose is to isolate the exact semantic
failure with a completely specified source. The established100 and104
certificates are unchanged.

The checker is `../verification/explore_counter_track_mask_omission.py`.
Author and independent complete proof/source reviews and fresh full runs
pass without findings. The receipt records314 local negative rows, every row of the fixed
37-state/39-edge ROM, and two materialized complete outer witnesses at width
61,924. Their30/36 serial rows give exact mask valuations22,292,640 and
26,751,168 by the proved support criterion. The packed integers have
35,267,161 and42,333,760 binary digits. No huge Pell auxiliaries were
materialized.

## 1. Exact relaxed interface and source

Use the state-top doubled100 source and its fixed43 kernel. Only the
packing changes. Its undivided twelve conceptual slots become

    Kplus, Kminus, H-D, D, t-A0, 0, t-A1, A1,
    zH-V, V, SH-C, C.

The formerly supplied positive `A0` remains in its guard and the time
equation. It is not set to zero. The new zero is solely a packed mask slot.
All other outer comparisons, positive domains, geometry and compiler
requirements are retained. Write `P100` for the old computed packing and
set

    weight=q4*q, removed=weight*A0, P=P100-removed.

These are two products and one subtraction. Replace only the index
comparison's old packed input by `P`; the scale remains `L=q^12`, and

    2r+1=L+P, r+beta=L.

The old count55M+45A consequently becomes57M+46A. The unchanged signed
packing correction is still `G X+Fsign`, where `G=q-J-1` and
`Fsign=Kplus+Kminus-H`: subtracting the same `q^5*A0` from both the
computed expression and conceptual packing introduces no additional
source correction. The checker expands all22 complete sources with
arbitrary fixed ROM constants. The kernel norm correction is unchanged.

## 2. Local negative rows admitted by the remaining masks

Divide the doubled numerical and flag words by two for this proof. Let

    b=R/3, g=(R-3)/6=(b-1)/2.

At a nozero source the undoubled gap row is `g`. The retained three
counter masks are `g-a0`, `g-a1`, and `a1`. For any `1<=n<=b`, split
the ordinary ternary number `n-1` as

    n-1=eL+e1,

where `eL,e1` have only ternary digits0/1, supported below `b`. Such a
split always exists: split each digit2 into1+1 and each digit1 into1+0.
Define

    a0=g-b-eL, a1=g-e1.

Then

    a0+a1=-n,
    g-a0=b+eL, g-a1=e1, a1=g-e1.

All three retained expressions are Boolean. The first uses the previously
unoccupied trit at `b`; the last is a digitwise complement below `b`.
Meanwhile `a0<0`. This is a literal signed row expansion, not a negative
supplied global unknown.

For a nonnegative ordinary source value `v<b`, split `v=a0+a1` into
two Boolean tracks below `b` in the usual way. Their complements relative
to `g` are Boolean. At a requested zero source use `a0=a1=0` and gap0.
Thus both positive and negative rows have the three required masks, while
all zero requests can remain truthful.

## 3. One fixed empty program and its illegal accepting path

The ordinary three-counter program is

    bad:     decrement counter1;
             if zero go to reject, otherwise go to restore
    restore: increment counter1; go to cleanup
    cleanup: decrement counter0;
             if zero go to accept, otherwise go to cleanup.

Its input is `[x,0,0]`, with positive `x`. Its actual first instruction
always takes the zero branch to reject. The represented accepting set is
therefore empty for every input, not merely the tested inputs.

Compile it using the existing two-bank, three-lane physical compiler,
mandatory initial plus/minus prefix with its marked source-zero request,
and accepting-entry quotient. Select the following controller path:

    prefix; bad/nonzero; restore/inc;
    cleanup/nonzero repeated x times; cleanup/zero; entry.

It is a genuine path of the fixed compiled graph. It has `24+6x` serial
source rows, starts with sign plus, and ends at the cyclic entry. Starting
with physical values `[2x,0,0]`, all its arithmetic updates are exact signed
unit updates and the final vector is zero. The only negative source values
are `-1,-2,-1` on counter1, during the invalid decrement and its restoration.
No source-zero request occurs at those rows. The marked prefix and final
cleanup zero branch both read actual zero. The last three source values
are1 and have no zero requests.

Apply Section2 at every row. Pack the signed `a0` rows and Boolean `a1`
rows in radix `R`; their sum is the signed physical counter history. Hence
the exact time equation follows coefficient by coefficient, including
all three initial and zero terminal values. Doubling gives exactly the
retained `4x` input convention.

Both packed track coordinates can be strictly positive. Assign the last
source1 to track0 and the preceding source1 to track1. Each dominates all
possible earlier negative coefficients, whose absolute values are belowR.
The third-last source1 may be placed on either track without affecting
this positivity or any retained mask. Choose it so that the undoubled
global `A0` is even. Since R is odd, its parity is the sum of its signed
row parities.

The omitted track really violates its old mask. At its first negative
source, which is `-1`, the signed track0 coefficient is `g-b`. Earlier
track0 rows are nonnegative and belowR, so there is no incoming borrow.
Its normalized remainder is

    R+g-b=2b+g,

whose trit at `b` is2. Thus the undoubled global track is not Boolean.

## 4. The fixed ROM and every other mask

The checker constructs the actual compiled graph above, including both
branches of each decrement instruction, the rejecting vertex and cyclic
acceptance quotient. It assigns the initial vertex the minimum Sidon
coordinate, uses a common grid spacing with `3^ell` larger than the
number of vertices, and compiles the standard edge, count-marker, sign
and nozero terms. It checks distinct table exponents and all pair sums.

For each graph edge it explicitly checks that the selected destination
and emitted labels are coefficient-one terms of the product. Removing
them leaves positive Boolean junk on the fixed grid, outside both label
ports. A fixed additional high forbidden trit is placed above all ROM
products and all required width thresholds. The paid positive grid slack
then gives the same intrinsic width conditions as100.

Use this exact ROM on the path in Section3. The state, junk, support
complement and global-grid complement fields are genuine Boolean words.
The sign and nozero flags are complementary actual row-head words; the
removed positive zero flag is reconstructed as a strictly positive word
because the mandatory prefix requests zero. The top relation
`6t=(R-3)D` holds. These conclusions use an actual controller path, with
no malformed selector, target or junk term.

Choose sufficiently wide grid-aligned R so `R>4x` and every nonnegative
source value is below `R/3`. Every supplied outer coordinate is then
positive. The checker materializes complete outer witnesses at inputs1
and2 using one fixed ROM and width, and evaluates all twelve outer
comparisons of the103 schedule. Neither input belongs to its accepting
set.

## 5. Complete positive fixed43 extension

There are eleven genuine retained Boolean fields and one zero slot.
Their doubled concatenation P has digits0/2, unit2, and `0<P<L=q^12`.
Set `r=(L+P-1)/2` and `beta=L-r`. Both are positive and

    L/2<=r<L, L>=81, r>=27, L<r^2.

The last inequality follows already from `L>4` and `r>=L/2`; it does
not require multiplying enormous indices in the checker.

For parity, let h be the undoubled head word and tau the undoubled gap.
The sum of all twelve original formal fields, even if the omitted track
is signed, is `2h+2tau+(S+z)h`. The relaxed field sum subtracts the
undoubled `A0`. The serial height `24+6x` is even, so h is even; Section3
chooses `A0` even. Thus the undoubled P is even. Also `(q^12-1)/2` is
even, proving that r is even.

The unit-two theorem gives exact central-binomial valuation
`12*width*(24+6x)`. All hypotheses of the fixed-sign43 positive converse
hold, so it supplies every positive Pell auxiliary for this new index.
No auxiliary is transported from an old100 solution, and these enormous
auxiliaries are not materialized. The resulting full positive solution
of the103 diagnostic source is a false positive for the fixed empty
program.

The result refutes this single-mask omission. It does not rule out a
different signed-counter encoding with an additional mechanism to
exclude underflow, nor a cheaper replacement with a separate soundness
proof. The tag proof's short-length monotonicity provides no such
mechanism for this counter example.
