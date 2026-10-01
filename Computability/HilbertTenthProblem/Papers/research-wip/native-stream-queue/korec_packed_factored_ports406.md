# Factoring the U21 native ports removes four additions

> Successor: [combined range/zero masks](korec_packed_zero_range397.md) reach397
> operations with one program parameter, or396 with two. Its accepted-input
> equivalence uses fresh native witnesses; the exact polynomial identity below
> belongs to this historical406/405 step.

The [literal source](korec_packed_factored_ports406.py) reduces the complete
[positive-program410 construction](korec_packed_positive_program410.md) to
**406 = 147M + 259A**, with **50 positive witnesses**, one fixed program
parameter, ordinary positive input and the same degree bound **42589**.
Its certificate costs405 operations and has one comparison. The
[two-program-parameter409 variant](korec_packed_program_radix409.md) similarly
falls to **405 = 148M + 257A**, with degree bound80458. The two interfaces
retain their different valid program recipes.

This is an exact integer polynomial rewrite. Supplied coordinates,
domains, every residual and native factor, and both complete finalizers
are identical to the matching parent, even away from zero. The parent
positive soundness and completeness theorems therefore transfer without
new native or chronological sign arguments. The separate75/87 bounds
are unchanged. The [receipt](korec_packed_factored_ports406.json) stores
all six emitted form/interface schedules.

## 1. The private field and packing identity

Let q be the padded native scale, A and B its padded input ports, and Z
its padded output port. The current source computes

    F1=A-Z, F2=B-Z, F0=q-A-F2-1,
    r=F0+q(F1+q(F2+qZ)).                             (1)

Those field differences cost five additions/subtractions; the Horner
packing costs three multiplications and three additions. The exact
identity over Z[q,A,B,Z] is

    r=(q-1)[A+1+(q+1)(B+(q-1)Z)].                   (2)

Both sides expand to

    q-1+qA-A+q^2B-B+q^3Z-q^2Z-qZ+Z.

There is no division, range assumption, native typing or zero equation
in this identity. The new expression has the same three multiplications
and only five additions, saving three additions. The factored expression
in brackets is retained under `counter_factored_inner`.

The input port has one further private row A=scaled_A+12, where
scaled_A=16H is already paid. Since (2) uses A only through A+1, compute
A+1=scaled_A+13 directly. This costs one addition instead of two and saves
the fourth addition. Multiplication by16 and every other fixed coefficient
remains charged. The old native scale, packed index r, X bound, masks,
range, initial word and all transport expressions keep their exact values.

## 2. Complete source guard and register restoration

The compiler accepts only the canonical computed-field, range-unit or
all-unit forms of the two cited parents. The guard reconstructs the entire
caller, checks all twelve replaced rows and every private consumer, and
rejects erased fields in live parameters, witnesses, comparisons, unit
factors, outer pairs and nested public interfaces. The packed register r
keeps its old name and all its downstream consumers.

The eliminated F0,F1,F2, intermediate Horner registers and padded A can be
restored diagnostically by (1) and A=A_plus_one-1. These are not unused
paid gates in the new circuit. Historical parent packets and diagnostic
register lists retain their original meaning; active diagnostic lists
include only live registers. Every emitted gate reaches each finalizer.

Thus evaluation of the new source on any integer assignment gives exactly
the old values for every surviving register. Diagnostic restoration gives
the old values for all erased registers as well. The comparison list and
all supplied coordinates are unchanged, so both whole polynomials agree
identically. In particular their full positive zero sets are identical,
not merely their accepted-input projections.

## 3. Literal ledgers and evidence

|Program interface|Native form|Certificate|Comparisons|Witnesses|Polynomial|Degree bound|
|---|---|---:|---:|---:|---:|---:|
|One parameter|Computed fields|397|4|50|408|42580|
|One parameter|Range unit|399|3|50|407|42589|
|One parameter|All units|405|1|50|406|42589|
|Two parameters|Computed fields|396|4|50|407|80442|
|Two parameters|Range unit|398|3|50|406|80458|
|Two parameters|All units|404|1|50|405|80458|

The all-unit SOS alternatives cost407 and406 respectively, with degree
bounds85178 and160916. All propagated degree dictionaries agree with the
matching parent dictionaries, including their guarded main-norm cancellation.
No exact-degree or optimality claim is introduced.

Run `python3 korec_packed_factored_ports406.py`; `--write` regenerates the
receipt. A symbolic coefficient check verifies (2). Across six complete
contexts,192 arbitrary-integer graph and diagnostic-restoration checks,
including96 signed assignments, verify every parent register; both
finalizers give384 complete output identities. The source checks all six
literal ledgers and closure in both finalizers, and rejects six incompatible
callers. No new finite-run or Pell existence hypothesis is needed because
the complete polynomial is unchanged identically.
Author receipt generation and a separate fresh replay pass. Independent
proof/source review and another fresh replay pass without findings. Its
separate symbolic padded-index calculation,288 manual register restorations
and576 complete finalizer identities cover all six contexts, with half the
assignments signed. Twelve literal opcode/closure checks and six independent
degree/domain checks also pass; every surviving propagated degree is unchanged.
