# Positive branch guards for every fixed counter program

The Markov positive-domain observation extends to the complete one-step
graph of **every fixed finite INC/conditional-DEC counter program** at a
vector-coordinate interface. The control state, target lookup, both guards,
all counter updates and the final SOS are included below. It saves three
operations against the same displayed schedule with a separate Boolean
residual. This is a proved parameterized source template, not an emitted
unbounded-history compiler or an operation-minimum claim.

## 1. Program, tables and supplied coordinates

Fix r>=1 counters and K>=1 control states labelled1,...,K. Every state
has exactly one instruction, either INC(i,j), or DEC(i,j,k) with a successful
decrement target j and a zero target k. All targets lie in1,...,K. Missing
instructions and an accepting halt can be totalized as in the existing
counter-program substrate; reachability is tested before any outgoing
post-acceptance action. No new universality theorem about a particular
two-counter machine is assumed.

For a state s define signed update entries d_i(s), with exactly one
nonzero entry: +1 for its incremented counter or -1 for its tested counter.
Define target values t_0(s),t_1(s): for INC both equal its target; for DEC
they are respectively its zero and successful-decrement targets.
Interpolate the r+2 columns

    D_i(s)=L*d_i(s), T_0(s)=L*t_0(s),
    J(s)=L*(t_1(s)-t_0(s))

at s=1,...,K, with one positive common denominator L and integer
coefficients of degree at most K-1. All are evaluated by padded Horner
schedules. These fixed tables are not unpaid variable lookups.

The external positive integer coordinates are the current and next states
s,s' and counter hats C_i=c_i+1, C_i'=c_i'+1 for1<=i<=r. Supply exactly
two additional positive integer witnesses: beta, a branch hat, and v,
a current-state range slack. Put

    e=beta-1, t=beta-2,
    V=sum_i D_i(s)*C_i, E=sum_i D_i(s),
    G=2V-E+L.

The complete relation is

    s+v=K+1,
    t*G=0,
    L*(C_i'-C_i)=D_i(s)*e                 (i=1,...,r),
    L*s'=T_0(s)+J(s)*e.                              (1)

There are r+3 equations. No separate Boolean equation is imposed.

## 2. Unrestricted positive-integer proof

The range equation forces1<=s<=K, so the table has the prescribed row.
Suppose the selected instruction is INC at counter i. Then
`G=2L*C_i>0`. Its zero guard forces t=0, hence beta=2 and e=1. Every
counter update and the control update are therefore exactly the specified
increment, with the other counters unchanged.

Suppose instead it is DEC at counter i. Here
`G=-2L*(C_i-1)`. If C_i>1, then G is nonzero, again beta=2 and e=1;
the updates give the successful decrement and its target. If C_i=1,
the active update gives `C_i'=1-e=2-beta`. Since both beta and C_i'
are positive integers, beta=1 and C_i'=1. All counters remain unchanged
and the control equation selects the zero target. Thus beta cannot take
any other positive integer value in any instruction case.

Conversely every legal step satisfies (1), with beta=2 on INC or a
successful DEC and beta=1 on a zero branch, and v=K+1-s. Both witnesses
are positive and unique. The relation therefore gives the exact complete
labelled step graph, not merely a set of possible counter endpoints.
The prescribed next state is automatically in1,...,K, so no additional
next-state range test is being silently assumed.

**Remark 1 (scope of positivity).** At a zero-tested counter, admitting
beta=2 and C_i'=0 would permit an illegal decrement. Similarly positive
noninteger beta between1 and2 would give a fractional successor. The proof
uses the stated positive integer domain. It also uses exactly one signed
unit update in each instruction; arbitrary simultaneous affine updates
do not follow from this theorem.

## 3. Explicit paid source template

Compute each of the r+2 interpolants by K-1 repeated multiplication/addition
pairs, with fixed integer coefficients. This costs
`(r+2)(K-1)M+(r+2)(K-1)A`, including zero or constant columns in the
declared padded schedule. Then emit these rows:

1. `range=s+v`; `e=beta-1`; `t=beta-2`.
2. All r products `D_i*C_i`, joined using r-1 additions to V. Join the
   r supplied computed D_i using r-1 additions to E. Compute
   `twice=V+V`, `difference=twice-E`, `G=difference+L`, then `guard=t*G`.
3. For each counter compute `difference_i=C_i'-C_i`,
   `left_i=L*difference_i`, `right_i=D_i*e`.
4. Compute `state_left=L*s'`, `jump=J*e`, `state_right=T_0+jump`.

The resulting equality-side cost after the interpolants is

| Block | M | A |
|---|---:|---:|
| Current-state range and e,t | 0 | 3 |
| G and its zero guard | r+1 | 2r+1 |
| All counter update sides | 2r | r |
| Control update sides | 2 | 1 |
| Total | 3r+3 | 3r+5 |

Thus the full graph with comparisons free costs

    ((r+2)K+2r+1)M + ((r+2)K+2r+3)A
      = 2(r+2)K+4r+4 operations.                         (2)

For one polynomial, form `range-(K+1)`, the r update differences and
`state_left-state_right`. The guard is already a residual; do not subtract
zero as an extra operation. Square these r+3 residuals and join them in
r+2 additions. Finalization adds `(r+3)M+(2r+4)A`, yielding

    F: ((r+2)K+3r+4)M + ((r+2)K+4r+7)A
       = 2(r+2)K+7r+11 operations.                       (3)

For r=2, the graph costs8K+12 and the complete SOS8K+25, with two
positive witnesses and five residuals. This interface has six external
coordinates s,s',C_1,C_1',C_2,C_2'. It must not be cost-compared to the
two-external-coordinate prime-encoded graph without paying a conversion.

For all r,K the output degree is at most2K+2: G has degree at most K,
its branch guard at most K+1, and the other residuals at most K. No
uniform assertion of exact degree is made; constant columns can lower it.
All constant multiplications by L remain paid. No division occurs in the
source, although cancellation of the fixed positive L is valid in the proof.

The same template with an additional Boolean residual `b=e*t` costs
exactly three more operations: one product to form b, one square and one
SOS join. The existing e,t are already needed. Both polynomials have the
same positive integer zeros by Section2, and the old one equals `F+b^2`
as an all-value polynomial identity. The saving is2M+1A, with unchanged
witnesses. This comparison is local to these two explicit schedules.

## 4. Ordinary inputs, universality and remaining work

The counters are actual vector coordinates, so this theorem introduces no
prime-power input recoding. To bind a queried positive integer x to one
initial counter hat use the paid addition `C=x+1`; fixed initial counters
and a fixed program code give fixed hats, and the initial state is fixed.
This is only an initialization interface. It does not identify one step
with acceptance or remove the need to certify arbitrarily long histories.

Any already established universal counter program obeying the stated
instruction contract can use this complete step graph. The inherited
Korec discussion in the parent concerns its actual finite number of
registers and ordinary-input register contract; it is not replaced by a
claim that r=2 preserves that particular strong input interface. The
r=2 cost specialization is simply the theorem for any given two-counter
program. No particular new universal program has been built or audited.

This is a proof-only source-template result. No vector array, fixture,
program, history or numerical experiment was executed for this note.
Only the separate scalar complement-reuse packet has emitted fresh arrays.
The proof and count permit such an implementation, but are not a claimed
execution audit of a universal machine or an improved universal polynomial.

Inert dependencies read in full:

- `markov_positive_guard_savings.md`, SHA-256
  `901accac868c13967883c56ff5b5a949ef42fcfd82a470999f042272ead8dc15`.
- `residue_affine_factored_counter_step.md`, SHA-256
  `60250f0f6d12f7583b5de747c82d0d91205eab98ca0f4095992d458aaf8a951f`.

These sources supply the accepted guard and program-interface context;
no external universality theorem or frozen helper was independently run.
