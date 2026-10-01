# An explicit universal polynomial in 389 operations

Two positive witness projections reduce the complete
[395-operation U9 construction](neary_woods_universal_population_bound395.md)
to **389=189M+200A operations**, with **67 positive existential witnesses**,
**22 comparisons** and four positive program parameters besides the ordinary
positive input x. Its certificate costs **324=167M+157A operations**.
The total degree is **at most 2241**, including the program coordinates.
This is an upper bound, not an exact-degree claim. The separate best
established universal construction remains
[87 operations](complete75_normalized_strong87.md).

The [source](neary_woods_universal_population_projection389.py) and
[receipt](neary_woods_universal_population_projection389.json) retain the
complete arithmetic DAG. All eleven fixed-numeral roles, the actual U9
machine, its CTS production and its positive program slice are unchanged.

## 1. Two coordinates already determined by existing expressions

Write the retained population and duration expressions as

    Q=q+power_gap,  B=2^(D-1)*Q,
    ell=program_E+program_duration_gap,
    v=duration_quotient,  t=quotient_hat,
    D=47946621298704238734708993009920.

The optional five-parameter form instead uses its independent positive
program duration bound in ell. All supplied coordinates are positive.
On every positive raw assignment q>=1, Q>=2 and B>=8. On every positive
unit or normalized assignment q=x+input_slack>=2, so Q>=3 and B>=12.
These inequalities do not assume that any residual has vanished.

The parent has the comparisons

    J=(B-1)*v+ell,
    Ahat+Q=(Q-1)*t+z+2.

Define the two eliminated coordinates by

    J*=(B-1)*v+ell,                                  (1)
    Ahat*=(Q-1)*t+z+2-Q
         =(Q-1)*(t-1)+z+1.                          (2)

Both are positive on every positive supplied assignment:
J*>=B and Ahat*>=2. Neither expression depends on either eliminated
coordinate. Thus there is no circular definition or additional
Diophantine condition hidden in the projection.

For J, the entire expression in (1) already exists in the certificate.
Alias every J consumer to it, remove the positive J coordinate and
remove its defining comparison. This changes no certificate gate.

For Ahat, the parent already computes the right side of its comparison.
Its private left-side addition Ahat+Q has no other consumer. Replace
that addition by the subtraction in (2), alias every Ahat consumer to
the result, and remove Ahat and its comparison. One addition is replaced
by one subtraction, so this projection also changes no certificate cost.
The implementation checks the literal source rows and consumer sets,
then stably sorts the resulting DAG and checks every fixed-numeral role.

## 2. Exact identity and positive zero-set bijection

Apply these projections to each already compiled parent form: raw SOS,
native units, or three normalized strong units. This order keeps the
parent wrappers' source contracts intact. Let L restore whichever of
J and Ahat have been removed using (1) and (2). Every retained
certificate register agrees with its parent under L, by induction along
the DAG. Every removed residual is identically zero. Consequently

    P_projected(y)=P_395(L(y))                       (3)

for every integer assignment to the retained coordinates, for each of
the three complete finalizers. This is an off-zero identity of complete
polynomials, not merely a relation between their zero sets.

On positive assignments L is positive by the inequalities above.
Thus every positive projected zero lifts to a positive parent zero.
Conversely a parent raw zero makes every squared residual vanish.
For either unit form, its integer finalizer is

    U*(1+sum of outer residual squares)-1;

at a zero, the second factor is a positive integer, so it equals one,
and every outer residual vanishes. The removed comparisons therefore
force precisely (1) and (2). Forgetting their coordinates gives a zero
of the projected source. The restoration and forgetting maps are
inverse: for each form they give an exact bijection of positive zero
sets, preserving the input and all program parameters.

The earlier 395 projection removed the private geometry bound slack
R-B, where R=(2^D-1)*J. Its positivity originally needed the duration
comparison to vanish. Whenever J is now projected, (1) instead gives

    R-B >= (2^D-2)*B > 0

on every positive supplied assignment. The default construction
therefore lifts positively all the way to the
[399-operation population parent](neary_woods_universal_population_tag.md)
even off its zero set. The Ahat-only option retains the earlier
zero-set restriction for that particular geometry slack.

The complete unprojected parent is stored as `projection_parent`.
Older unit audit metadata still describes its supplied J/Ahat interface;
its audit functions must be called after restoring the coordinates.
They do not accept the shorter values dictionary unchanged. The new
verifier performs that restoration explicitly.

## 3. The ordinary-input universal contract is unchanged

The fixed machine remains the original U9-derived binary clockwise
machine with 1968 states, CTS half-length z=59101 (period 2z=118202), binary tag parameter
beta=1182020 and the fixed D displayed above. The exact fixed production
and all eleven numeral recipes are inherited from the 395/399 packets.
The computations here neither replace that machine nor alter its input
encoding.

For each recursively enumerable set S, the parent supplies four fixed
positive program values A_S,B_S,T_S,E_S. The sentinel E_S dominates the
fixed physical overhead b_S. The retained duration is ell=E_S+gap;
at zeros it is the genuine dyadic duration n. The initial physical tape
has 64n+b_S cells and its exact least dyadic counter is 128n. This exact
counter rule, positive DATA ordering, valid U9 slice with at least six
A symbols, and the separate selected history checksum are retained.
Arbitrarily long dyadic zero padding gives completeness on every
ordinary positive input x in S.

Combining that established universal theorem with the positive
bijection above gives one fixed polynomial F such that

    x in S iff there exist y_1,...,y_67>0 with
    F(x,A_S,B_S,T_S,E_S,y_1,...,y_67)=0.

The four program values are fixed per set; they are not counted as
existential witnesses. The two projections add no hidden constraint,
parameter, checksum or arithmetic operation.

## 4. Arithmetic and degree tradeoffs

Each removed comparison saves one subtraction, one square and one sum
addition in the finalizer: **1M+2A**. Each projection also removes one
positive witness, while certificate operations stay fixed.

| Form, both projections | Certificate operations | Comparisons | Positive witnesses | Polynomial operations | Degree upper bound |
|---|---:|---:|---:|---:|---:|
| Raw SOS |309|53|86|467|544|
| Native units |318|25|67|392|1405|
| Three normalized strong units |324|22|67|**389=189M+200A**|**2241**|

Both duration-bound interfaces have these counts. The normalized
variants expose the operation/degree tradeoff:

| Projected coordinates | Polynomial operations | Positive witnesses | Degree upper bound |
|---|---:|---:|---:|
| Neither, parent 395 |395|69|2204|
| Ahat only |392|68|2206|
| J only |392|68|2239|
| J and Ahat |389|67|2241|

The Ahat-only variant has the better degree bound at 392 operations.
The J-only option is included for reproducibility, not as an improved
tradeoff. Raw degree bounds remain 544 for all four choices; native-unit
bounds are respectively 1384, 1386, 1403 and 1405.

The source propagates degrees over the actual transformed DAG, treating
fixed numerals as degree zero and all input, program and witness
coordinates as degree one. It checks the literal cancellation guards
for all three main normalized norms before applying their expanded
bounds. With both projections the unit product has degree at most 1911,
and the largest outer residual at most 165, giving 1911+2*165=2241.
Substituting computed quadratic coordinates raises some degrees; no
parent degree formula is reused unchanged.

## 5. Executable evidence and limits

The 24 ledgers cover three forms, two duration-bound interfaces and
four projection choices. The writer and fresh default verifier both
pass. The checker evaluates 768 exact complete polynomial identities,
384 signed and 384 positive, comparing all shared non-finalizer source
registers and the removed zero residuals. Positive cases additionally
check the positivity of every restored coordinate and, when J is
projected, of the earlier geometry slack.

These algebra checks assign each fixed-numeral role one finite integer
consistently throughout both complete DAGs. Most roles are sampled
independently; these fixtures do not impose all cross-role arithmetic
relations of the actual coefficients. The positive cases use radix 4
and repunit divisor 7. They do not materialize the enormous actual coefficients or native Pell
zeros. Universality and positive witness completeness follow from the
proof and the parent theorem, not from finite numerical fixtures.

```sh
python3 neary_woods_universal_population_projection389.py
```

Final independent proof/source/prose reviews by the reduction and native
reviewers passed after correcting the finite-substitution description
and the distinction between z and the CTS period 2z. Their separately
executed audits add 384 and 192 complete identities respectively,
192 and 96 signed, across all 24 configurations. The native audit also
compares every retained residual. Both verify the unconditional positive
restoration directly from (1) and (2). Root's writer, fresh default,
complete source and proof reviews pass; all local links resolve.
