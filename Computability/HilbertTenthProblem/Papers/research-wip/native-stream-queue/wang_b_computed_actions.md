# Computed actions give a331-operation fixed Wang program compiler

The [native coupled-unit successor](native_binary_index_coupled_units.md)
reduces this example's literal-input polynomial to330 operations and
degree at most5503. A separate [non-erasing TM compiler](wang_b_nonerasing_tm_compiler.md)
now pays the Theorem7 Wang expansion and binary pair loader, with an
illustrative642-operation ordinary-input predicate. Neither example
instantiates a universal instruction table.

The four action hats in the [chronological Wang compiler](wang_b_packed_program.md)
can be defined from its already-paid instruction-edge selectors. This
removes four positive witnesses and four comparisons by an exact positive
graph bijection. Reassociating the global bound saves further arithmetic.

For the parent's six-instruction example, the normalized-unit endpoint
polynomial now costs **331=146M+185A**, with **305=137M+168A** certificate
gates, **9 comparisons**, **33 positive witnesses** and degree **at most3838**.
The literal positive binary-input interface costs **333=147M+186A**, with
**307=138M+169A** certificate gates,9 comparisons,36 witnesses and degree
**at most5767**. Both degree bounds are unchanged.

The [source](wang_b_computed_actions.py) and
[receipt](wang_b_computed_actions.json) handle all four parent native
forms, both input interfaces, and optional bound reassociation. They
preserve the complete fixed-program halting theorem, including current
reads, common duration, first halt and the paid input shift. No universal
Wang instruction table or TM-to-Wang input morphism is instantiated, and
no new numerical universal bound is claimed.

## 1. Existing paid edge sums define the action words

Let E_e=E_e_hat-1 be the parent's nonnegative edge words. The compiled
instruction table partitions its edges by action M,L,R,J. Write

    E_M=sum_(mark edges) E_e,
    E_L=sum_(left edges) E_e,
    E_R=sum_(right edges) E_e,
    E_J=sum_(jump edges) E_e,
    E_all=sum_e E_e.                                (1)

The source already computes the first three sums for its comparisons
I=E_M,L=E_L,R=E_R, the full sum for E_all=J, and E_J for the jump
mask when jumps exist. An empty sum is the fixed numeral0; a singleton
sum is its existing edge register and needs no copy gate.

The old source also contains

    I=I_hat-1, L=L_hat-1, R=R_hat-1,
    J=I_hat+L_hat+R_hat+Stay_hat-4.                  (2)

Define instead

    I=E_M, L=E_L, R=E_R, J=E_all.                   (3)

Erase the four supplied hats I_hat,L_hat,R_hat,Stay_hat and the four
comparisons just named. Every use of the raw I,L,R,J registers is
redirected to its paid edge sum, including all masks, native ports,
chronological transports and declared public interfaces. No selector
sum is free: the existing literal gates producing(1) remain charged.

In the plain schedule, retain the three old action-hat names as computed
registers

    I_hat=E_M+1, L_hat=E_L+1, R_hat=E_R+1.            (4)

These three additions replace the three old subtractions in(2) at the
same cost. They supply the original global bound. The old three-addition,
one-subtraction calculation of J is deleted entirely. Stay_hat has no
remaining arithmetic consumer, so its positive reconstruction does not
require a gate in the new polynomial.

Thus the plain graph schedule saves4 certificate additions/subtractions,
four comparisons and four witnesses. Every complete finalizer saves
another12 operations, for a total reduction16. The example endpoints
350/352 therefore become334/336 even without the next optimization.

## 2. A paid global-bound identity

The old global bound contains the four-term contribution

    J+I_hat+L_hat+R_hat.

Because E_all=E_M+E_L+E_R+E_J, substitution(3)--(4) gives the exact
polynomial identity

    J+I_hat+L_hat+R_hat=2J-E_J+3.                   (5)

In the plain schedule, forming the three hats and adding them into the
bound costs six additions. The default folded schedule replaces those
six gates by the following literal expression:

* Mixed jump/nonjump program: J+J, subtract E_J, add3; three additions.
* No jump instructions: J+J, add3; two additions.
* Every instruction is a jump: J+3; one addition, since E_J is literally
  the already-computed full partition sum.

The checker verifies the appropriate source/table condition before each
specialization. These counts are source-derived; the extra saving is3,
4 or5 additions respectively, not always3. The six-instruction example
has both kinds of edge and therefore receives the extra3-operation saving.

This reassociation preserves the final bound as an ordinary polynomial
identity. Some partial bound accumulators change, and the audit identifies
them explicitly; equality of every intermediate bound register is not
claimed. Every other retained certificate register and every native unit
factor agrees under the lift below.

On positive assignments, E_J<=J follows from the edge partition as a
sum of nonnegative words, even before any equation or bit interpretation.
Therefore2J-E_J+3>=3. The folded bound does not introduce a hidden
negative or zero native input port.

## 3. Exact maps, positivity and preservation of the full theorem

For every new supplied positive tuple, restore the old coordinates by

    I_hat_old=E_M+1,
    L_hat_old=E_L+1,
    R_hat_old=E_R+1,
    Stay_hat_old=E_J+1.                              (6)

All four are strictly positive unconditionally. The old raw actions
become(3), and the old value of J becomes E_all. All four erased
comparisons are identically true. Identity(5) restores the final old
global bound. Every other comparison, native factor, parameter and
supplied coordinate retains its value.

Consequently every new positive zero lifts to a complete parent positive
zero. This invokes the full parent theorem, including the current-tape
jump condition and chronological instruction sequence. There is no new
use of final-tape reads, aggregate control flow or an independently chosen
duration.

Conversely, take any complete positive zero of the selected parent form.
The three retained parent action comparisons give I=E_M,L=E_L,R=E_R.
Its partition comparison gives J=E_all. Equation(2) then forces

    Stay_hat-1=E_all-E_M-E_L-E_R=E_J.

Thus all four old hats already have exactly the values(6). Erasing them
is inverse to the positive lift and gives a new zero. This converse is
valid for every supplied parent zero, not merely for some fresh canonical
choice of native auxiliaries. In particular, when the selected parent is
the normalized-unit form, the new map changes none of its five strong
auxiliaries. The parent's earlier existential normalization theorem is
preserved, and this additional graph projection itself is a bijection.

The same formulas are algebraic over arbitrary integer assignments.
The four discarded residuals become zero identically and all retained
residuals and unit products agree, so both complete finalizers obey

    Polynomial_new(v)=Polynomial_parent(lift(v)).   (7)

For a normalized-unit parent this is checked separately for its unsquared
integer-product finalizer and its SOS finalizer. No off-zero sign or
native interpretation is assumed in(7).

Absent action types cause no domain problem: their lifted hat is1.
A singleton edge is simply reused by name. If every edge hat is1,
all E_e vanish, all four restored hats are1 and J=0. The global bound
then rejects the tuple exactly as in the parent. Pretyping positivity
does not rely on the existence of a nonzero edge word.

Moreover the new definitions strengthen the convenient pretyping bounds:
I,L,R,E_J and every subset edge sum are automatically at most J before
equations. J>=0, B>1 and P=(B-1)J+1>=1 still hold on the entire positive
domain. The full parent native embedding is therefore preserved without
an additional range comparison.

The literal-input initialization x*initial_head+1 is unchanged. So are
its head typing and finite-window translation. The existential positive
projection remains exactly halting on that fixed program's literal
positive binary input. The example program is still not asserted universal.

## 4. Costs, degrees and actual source interfaces

Let C,e,w denote the chosen parent's certificate, comparison and witness
counts. The plain schedule has

    C_new=C-4, e_new=e-4, w_new=w-4,
    Polynomial_new=Polynomial_parent-16.

For the folded schedule let b be the one-, two- or three-gate bound
calculation from Section2. Then

    C_new=C-(10-b), e_new=e-4, w_new=w-4,
    Polynomial_new=Polynomial_parent-(22-b).        (8)

Only certificate additions are deleted; the finalizer additionally saves
four multiplications and eight additions. All multiplication by fixed
numerals and every retained selector-sum gate remain paid.

For the parent's six-instruction example, the default folded ledgers are:

| Interface/form | Certificate | Polynomial | Comparisons | Witnesses | Degree bound |
|---|---:|---:|---:|---:|---:|
|Endpoints, raw|300|359=152M+207A|20|40|556|
|Endpoints, positive scale|300|356=151M+205A|19|39|556|
|Endpoints, six fields|300|338=145M+193A|13|33|1264|
|Endpoints, normalized units|305|331=146M+185A|9|33|3838|
|Literal input, raw|302|361=153M+208A|20|43|832|
|Literal input, positive scale|302|358=152M+206A|19|42|832|
|Literal input, six fields|302|340=146M+194A|13|36|1900|
|Literal input, normalized units|307|333=147M+186A|9|36|5767|

The four projected quantities are affine in the remaining edge hats.
All raw action words, J and global-bound expressions keep degree at most1.
No degree bound of any downstream source register increases. The removed
comparisons have degree at most1, while remaining outer/native residuals
dominate them. The native source rows, including the guarded main-norm
cancellation, are unchanged. Actual degree propagation gives the same
parent bounds on all emitted schedules. These remain conservative upper
bounds, not claims of exact degree or optimal arithmetic complexity.

`rewrite(old,fold_bound=True)` checks the exact chosen frozen compiler
form before substitution, audits the private total/hat consumers and
four deleted comparisons, and topologically sorts the resulting source.
It also requires the frozen parent's exact public-export declaration;
an added export of a reassociated intermediate bound value is rejected.
It recursively remaps actual interface/public-register leaves, including
optional None entries and zero/singleton action sums. Every resulting
declared register must be present in the new source or input domain.
The reported number of outer equations is updated from8 to4.

The inherited native-helper parent packets are explicitly historical.
The wrapper does not rerun a native helper against stale pre-action
metadata. Its `action_parent` is the exact original selected form;
`lift_to_parent` first restores(6), after which `raw_lift` may use the
parent's existing native maps. The new native factor formulas are also
checked literally when the selected form uses norm units.

`build(program,literal_input=False,form='units',fold_bound=True)` selects
one of raw, scaled, projected or normalized-unit parent forms before
performing this new rewrite. Setting fold_bound=False emits the paid
334/336 plain alternative. Existing parent files are not modified.

## 5. Reproducible checks

```sh
python3 wang_b_computed_actions.py
```

The receipt emits128 complete source ledgers from eight programs, two
input interfaces, four native forms and both bound schedules. They
include missing actions, singleton edges, an all-jump program and a
19-instruction program crossing the radix-factor threshold.

There are2,048 arbitrary-assignment audits,1,024 signed and1,024 positive.
Every positive assignment has a positive four-hat lift, including an
explicit all-zero edge-word assignment for each schedule. The checker
compares all retained residuals, every unit factor and all unaffected
registers, checks coordinate round trips, and executes both finalizers
for unit forms. This gives2,560 exact whole-output identities. Every
emitted arithmetic gate reaches the final output, and all actual public
register leaves resolve. A separate rejection fixture checks the forbidden
added export of a reassociated bound prefix.

The184 genuine outer-history instances contain1,008 chronological rows;
152 instances omit some action type and96 use a singleton edge. Erasure
and lift agree exactly on all four old hats, and all four surviving
outer equations, the joined AND and positive bounds hold. Their native
coordinates remain placeholders: no finite fixture is called a complete
positive Pell zero. The full positive extension follows from the graph
bijection and the already-proved parent converse.

Author receipt generation and a fresh default replay pass. All three
local links resolve. The root reviewer completed the full proof/source
review, including the final public-export guard, without remaining
findings. Two separate independent1,152-case audits,576 signed each,
also passed: one used its own emitted rewrite and four-hat lift, and
the other compared that independent source directly with the author's
source across both bound schedules. Both unit finalizers were included.
The root's final fresh replay passed after the zero-edge, metadata and
public-export rejection updates.

A second reviewer completed the full proof/source review and a fresh
default replay without findings. Its own executor and manual four-hat
lift passed384 complete-output, retained-residual and recursive-interface
cases,192 signed and192 positive, including64 all-zero edge-word lifts.
It also checked64 literal ledgers across four additional programs, all
four native forms, both input interfaces and both bound schedules. All
three local links resolved in that independent review.
