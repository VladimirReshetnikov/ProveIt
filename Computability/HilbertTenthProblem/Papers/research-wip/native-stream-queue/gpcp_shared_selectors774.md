# Paid selector sums save31 operations in the complete sparse-TM compiler

The complete normalized, ordered U15,2 compiler now costs
**774=352M+422A**, with125 positive existential witnesses,24 comparisons,
three fixed positive program parameters and ordinary positive input x.
Its certificate costs703=328M+375A. The exact degree remains205092.
Keeping the initial history value supplied gives **777=353M+424A**,
126 witnesses,25 comparisons and exact degree8532.

These are exact complete integer-polynomial identities with the two
canonical ordered forms of the [805/808 normalized parent](gpcp_normalized_strong_compiler.md).
Every supplied coordinate, domain, fixed tile, program numeral and input
interpretation is unchanged. This improves a separately instantiated
universal route; it does not improve the smaller75/87, U9 or C2 bounds.
The [source](gpcp_shared_selectors774.py) and
[receipt](gpcp_shared_selectors774.json) contain both complete emitted
polynomials and their literal ledgers.

The mechanism transfers the paid-sum reuse already used in
[the packed counter compiler](korec_packed_selector_sharing380.md) and
[the C2 selector compiler](tseytin_selector_sharing428.md) to this actual
57-tile sparse-TM graph. It is a new concrete schedule, not a new machine
universality theorem or a general circuit lower bound.

## 1. A disjoint cover by existing scalar registers

Write h_i=`hist__Shat_i`, for0≤i<57. The parent forms the positive-hat
sum with56 successive additions and then computes

    J=(h0+...+h56)−57.

The same source separately pays for sums used by its slope classes and
affine transports. The following25 existing registers partition all57
hats exactly. Eleven are individual supplied coordinates; fourteen are
already-emitted sums.

|Existing register suffix in `hist__`|Selector indices|
|---|---|
|individual Shat coordinates|2,3,31,32,37,46,48,49,50,52,56, each as its own block|
|selector_sum__4|0,1|
|group_sum__457|4,5|
|group_sum__472|6 through20|
|group_sum__482|21,22,23,24,29|
|linear_group__617|25,26,27,28|
|linear_group__619|30,39|
|linear_group__621|34,36|
|linear_group__698|33,35|
|linear_group__626|40,41|
|linear_group__707|42,53|
|linear_group__709|43,54|
|linear_group__623|38,47|
|linear_group__716|51,55|
|linear_group__628|44,45|

Each index occurs once. Thus the sum of these25 registers is exactly
h0+...+h56 on every integer assignment. No Boolean, one-hot, positivity,
range, history or Pell hypothesis enters this identity. The executable
checker expands each existing register's actual addition DAG into its
57-dimensional integer coefficient vector and checks every vector and
their sum. It does not infer a block from its register name.

The old first addition h0+h1 remains live because a slope-group definition
uses it. The other55 additions are replaced by24 additions joining the
25 cover blocks. Their final result retains the old total-sum name, so
J and every descendant receive precisely their previous values. Therefore

    new prefix work=1+24=25 additions,
    saving=56−25=31 additions.                         (1)

There are54 erased old intermediate names,23 new joining names, and one
retained total-sum name with a new definition. No multiplication is added,
removed or treated as free. Every reused block remains necessary for the
other slope or transport expressions that originally paid for it.

The fixed cover is the emitted construction. A bounded discovery search
among existing pure0/1 selector sums found it, but no optimality over
other covers, signed decompositions, re-encodings or arithmetic circuits
is asserted.

## 2. Privacy, ordering and complete polynomial identity

The supported parents are precisely

    gpcp_normalized_strong_compiler.build_ordered_universal(
        inline_initial=True or False)

with their default sparse-tuned code. `rewrite` compares the entire
supplied packet to its canonical parent, including the literal source,
comparison list, domains, machine, prefix code and program data. Other
code variants, rule orders and unnormalized strong treatments are outside
this wrapper's interface.

The local audit additionally checks every old selector-prefix row. Each
erased prefix has exactly its old next-prefix consumer; none occurs in
any active exported comparison or metadata field. The first prefix and
final total are retained. Every cover block expands solely through
addition rows to supplied hats, and cannot use any erased prefix, J,
packing geometry, native variable or update subtotal. Consequently moving
the joins after these already-paid blocks introduces no cycle. The source
is then topologically sorted and every operand is checked against the
original inputs or an earlier defining row.

All original registers except the54 erased private prefixes remain and
have exactly their old values. The erased values have the explicit
restoration

    selector_sum__(i+3)=sum_(j=0..i) h_j, 1≤i≤56.       (2)

Equation(2) also checks the retained first and last prefix values. This
is a register-restoration statement; the witnesses themselves do not
change. Historical raw, recoder and history emitters remain inside the
nested parent provenance. Active history metadata contains only fixed
geometry data and no stale alternative emitted source.

Let U be the complete parent unit product and R_j its other comparison
residuals. The literal finalizer is unchanged:

    F=U(1+sum_j R_j²)−1.                              (3)

The common prefix identity preserves every unit factor and every R_j.
Thus the two complete polynomials agree on all integer supplied tuples,
including arbitrary signed and off-zero assignments. In particular the
identity map is a bijection between all their supplied positive zero
sets, before restricting the three program parameters to valid codes.

The actual [ordered sparse-TM compiler](gpcp_ordered_sparse_tm.md) already
contains the fixed U15,2 transition table,53 rewriting rules plus four
copy tiles, the paid binary recoder, ordinary-input block morphism, fixed
program frame, terminal append and all selected-history/native proofs.
Those data and scalar expressions are unchanged here. For every valid
parent program slice, the new source therefore accepts exactly the same
ordinary inputs with the same permitted leading-zero padding. No abstract
universal alphabet is left to instantiate, no native witnesses need to
be rebuilt, and no new semantic endpoint argument is used.

## 3. Literal ledgers and exact degrees

Both certificate interfaces have703=328M+375A gates. Their only cost
difference is whether the initial history value is computed by the paid
boundary or supplied with its retained comparison.

|Initial history value|Complete operations|M|A|Comparisons|Positive witnesses|Exact degree|
|---|---:|---:|---:|---:|---:|---:|
|Computed, default|774|352|422|24|125|205092|
|Supplied|777|353|424|25|126|8532|

The parameters are x, program_prefix, program_suffix_scale and
program_suffix_value; only x varies within a fixed universal program
slice. All four remain positive integer inputs in the packet. The
source charges every fixed-numeral multiplication and every finalizer
operation exactly as its parent.

Every new joining register is a nonzero linear form in the supplied
hats, so has degree one. Every retained degree-dictionary entry equals
its parent's entry. The three main-norm cancellations still follow
literally from

    D=X+ac+G, G=gamma(4a+3), Delta=a²+4a+3,
    D²−Delta*c²
      =X²+2Xac+2XG+2acG+G²−(4a+3)c².                (4)

The checker verifies the defining source rows for(4), propagates every
row in the changed DAG and compares all retained entries. It separately
runs the parent's exact-degree audit, including its nonzero highest-form
evaluation, on the new source. The factor degrees, maximal residual
degree, leading sign and leading-coefficient digest all equal the parent
records. Moreover, the complete polynomial identity independently
preserves exact degree. The displayed numbers are the established exact
degrees for these two polynomials, not minimum degrees among universal
representations.

## 4. Reproducible checks and scope

`build(inline_initial=...)`, `polynomial_source`, `degree_dictionary`,
`degree_audit` and `ledger` are the guarded APIs. Complete packet equality
is checked before emitting a finalizer, degree record or ledger. Default
execution recomputes the deterministic receipt; `--write` regenerates it.

The author audit checks the25 exact paid coefficient vectors and their
disjoint total;128 complete register restorations and128 complete
parent/direct-finalizer identities,64 on signed assignments; eight cases
with every decoded selector zero; both literal opcode, full output
reachability and retained-degree ledgers; and91 malformed canonical,
private-consumer, export and cover-definition callers. These are exact
algebraic/source fixtures, not newly materialized full packed Pell zeros.
The universal theorem transfers by identity, rather than being inferred
from a bounded execution test.

Author writer59000 and separate fresh replay12660 passed on the same
source and receipt. All six local links and whitespace pass. Independent
review is pending.

Root's independent full proof/source/dependency review and fresh23998
passed with no findings. Its separate executor checked48 complete
prefix-restoration, retained-register and manual-factor/output maps
(24 signed),114 coefficient-basis cases and both exact-degree records.
