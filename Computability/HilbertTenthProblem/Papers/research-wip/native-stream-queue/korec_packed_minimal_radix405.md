# Minimal time radix and a paid native bound give405 U21 operations

> Successor: [one selected range mask](korec_packed_zero_range397.md) also
> enforces zero branches, reaching397/396 operations in the respective
> parameter interfaces. The narrowed scalar bound is part of its proof.

The [literal source](korec_packed_minimal_radix405.py) gives a
**405=146M+259A** universal counter polynomial with **one fixed positive
program parameter**, ordinary positive input,50 positive witnesses and
degree at most36165. The two-program-parameter interface gives
**404=147M+257A**, with the same witness count and uniform degree at
most68314. Each default has one comparison; their certificates cost404
and403 operations respectively. The [receipt](korec_packed_minimal_radix405.json)
contains all six complete form/interface schedules.

The parent is the [factored406 compiler](korec_packed_factored_ports406.md).
This packet is restricted to its canonical strongly universal U21 table,
labels and eight registers. It makes no generic-table or newly optimized
control-plan claim. The one-program recipe remains E>0, as proved by
[positive_program410](korec_packed_positive_program410.md). The second
interface retains the [program_radix409 recipe](korec_packed_program_radix409.md):
fix E>0 and a dyadic C>=4 with C>E, then keep both fixed as ordinary x
varies. The separate U9 and75/87 results are unchanged.

There are two changes with different logical scopes. Replacing the time
radix2D^8 by D^8 needs a direct chronology and positive-extension proof.
Reusing an existing native port factor gives a triangular coordinate
identity **only against the intermediate source with the new time radix**.
No arbitrary-point identity or identical-positive-tuple claim is made
between this source and the original2D^8 compiler.

## 1. Paid definitions and source guards

The two height interfaces are unchanged:

    one program: h=E+x+eta, D=2h;
    two programs: h=x+eta, D=C*h.                    (1)

Here every supplied coordinate is positive. The first interface has h>=3,
D>=6; the second has h>=2,D>=8. In both cases E,x<D. The new time radix is

    B=D^8,                                          (2)

using the existing paid eighth power. Delete the private multiplication
`time_radix_80=2*D8_79` and alias all its consumers to `D8_79`. In
particular the active B interface and multiplier metadata now say(2).
The explicit false/true program-radix flag, parameter lists and all
non-radix interfaces retain their respective meanings.

Let q be the padded native scale and A,Bp,Z its padded input/output
ports. The parent's already paid factorization is

    S=A+1+(q+1)(Bp+(q-1)Z), r=(q-1)S.

Change only the first operand of the native bound addition:

    X=q(r+beta_old)  becomes  X=q(S+beta).            (3)

This costs no additional gate. The surviving factor S is used by both
its existing index multiplication and the native bound. Thus(2)--(3)
save exactly one multiplication in either interface and every supported
form. No coefficient, comparison, supplied variable or loading operation
is omitted from the ledger.

The guard reconstructs the complete canonical factored406 caller, verifies
the old radix row and eighth power, and checks every bound/index row and
the sole native-bound witness consumer. Its dependency cone excludes that
witness from S and r. It rejects any changed table, form, interface, domain
or arithmetic source. Active exports are rewritten through the deleted
radix alias, while stored parent packets retain their historical meaning.
Both complete finalizers have full source closure.

## 2. Untyped ranges with B=D^8

There are K=34 edges. Write E_i=edgehat_i-1>=0 and

    J=sum E_i, P=(B-1)J+1,
    W=counter_word_hat-1>=0, Y=final_counter_hat-1>=0,
    R=(h-1)(1+D+...+D^7), RM=RJ.

A positive zero in any supported form supplies either the exact global
comparison or its signed unit

    N_G=RM-(W+1+gamma) in{-1,+1}.                    (4)

If J=0, its right-hand side is at most-2, or the exact comparison is
impossible. Hence J>=1. Both signs of(4) give W<RM. Since h<D,

    R<B-1, RM<(B-1)J<P.                              (5)

Every selector E_i<=J<P. The selected zero-register word obeys
Zword<=D^7 J, without any Boolean or branch semantics assumed. Its mask
therefore satisfies

    ZM=(D-1)Zword< (B-1)J<P,                         (6)

because(D-1)D^7=D^8-D^7<D^8-1. This is the zero-lane estimate that
formerly had an unused factor2 of room. The inequalities hold at h=2
in the two-program interface and at the smallest untyped h=3 in the first.

The literal joined words, before native padding, are

    Epack=sum E_i P^i,
    A0=Epack+P^K W,
    H=A0+P^(K+1)W,
    M=J(1+P+...+P^(K-1))+P^K RM+P^(K+1)ZM,
    Q=B P^64.                                       (7)

Here A0 is the output word, not the padded input A. Equations(5)--(6)
put every displayed coefficient below P. Thus H,M<P^36 and
Q>H+M-A0, since B>=6^8>2. Also H-A0>=0, and M-A0>0: the selector
mask minus Epack is nonnegative, and RM-W>0. Padding by16 with residues
12,10,8 gives positive reconstructed truth fields

    F0=q-A-Bp+Z-1,
    F1=A-Z=16(H-A0)+4,
    F2=Bp-Z=16(M-A0)+2,
    F3=Z=16A0+8.

Their sum is q-1, each is below q, and their residues are1,4,2,8 modulo16.
Their packed index is exactly r=(q-1)S, even though the redundant field
registers were deleted by the factored parent. Thus S>0 and the new bound
has the strict pretyping margin

    X-r=q(S+beta)-(q-1)S=S+q*beta>0.                 (8)

No old stronger bound X/q>r, binary lane interpretation or positive
chronological sign was used in these estimates.

## 3. Native typing and chronological soundness

Apply the independent local native sign/rank proof in
[the U21 unit theorem, Section4](korec_packed_counter_units.md).
Its hypotheses are precisely the positive fields and checksum, r>q and
large-index bounds, X>r, odd positive scale multiplier, both strict ratios
and the retained complete normalized strong relation. Congruences recover
the norm signs and rank/duplication recovers the linear sign before using
an outer product sign. The raw scalar population theorem at
r'=r+epsilon-1 gives q=2^popcount(r'). The unchanged residue r=1 modulo16
and positive checksum force

    popcount(r)>=log2(q),
    popcount(r-2)>=popcount(r)+2,

excluding epsilon=-1. Consequently all native factors are+1 and the
complete prescribed AND holds.

Now q=16BP^64 is dyadic, so B,P are dyadic. Equation B=D^8 makes D dyadic
without requiring a factor2 in B. In the one-program interface D=2h makes
h dyadic; in the second the fixed dyadic C and D=C*h do the same. In
particular D>=8 in both typed cases. The repunit equation then gives

    P=B^T, J=1+B+...+B^(T-1), T>=1.

The selector lanes and K=34<B force exactly one edge in each chronological
digit. The range lane puts the post-decrement counter digits in[0,h-1].
The zero lane imposes zero in its selected register; a positive test puts
one in both the current and following action word, preserving its register.
Thus all three U21 instruction kinds have the inherited exact meaning.
The unchanged label coefficients are at most5 and are distinct within
each register. With D>=8 they are below D-2, so codes lambda*D^r are
injective and lie below B=D^8. Every current or following counter vector
has digits at most h<D, hence also lies below B. The initial integer
ED+xD^2 is below B since E,x<D, including when E>=h in the second interface.

For all-unit sources, the negative counter-transport sign would force
the current low register digit D-2, which exceeds h. The negative control
sign would force low digit D-2 or D-1, neither of which is a legal code
residue. These are exactly the inherited low-digit exclusions, with
stronger or equal margins at the smaller time radix. Both factors are
therefore+1; the product then fixes the range factor+1. The range-only
form already retains both transport comparisons. The computed-field form
retains all three comparisons. Thus in every form the exact transports are

    B(W+I)+ED+xD^2 = W+L+P Y,
    B*following+D = current.                        (9)

Their words have digits below B and their initial values fit below B.
Coefficient comparison recovers every adjacent counter vector and every
control step from the actual initial state0 through the unique halt21.
The top coefficient forces Y<B even though final_counter_hat was not
bounded in the pretyping argument. There is no endpoint-only flow
shortcut. These facts prove soundness for the unchanged ordinary input.

## 4. Positive completeness at the new radix

Fix a genuine finite halted U21 run with the indicated E,x and, if used,
one valid C fixed for that E. Choose dyadic h more than two above every
counter in the run, also h>E+x in the one-program interface or h>x in
the two-program interface. Set the corresponding eta by(1), D by(1) and
B=D^8. These choices are positive, and both D,B are dyadic.

The new `pack_history` checks each actual transition, then packs the
edge indicators and post-decrement vectors using this B, including the
one-below representation for a positive pure test. Every such counter
digit is at most h-3. Hence

    RM-W >=2(1+D+...+D^7)J>2.

The plain form takes gamma=RM-W-1>0; each unitized range form takes
gamma=RM-W-2>0. The correct terminal vector and actual control path
satisfy(9). All required outer factors are+1, and the joined AND is genuine.

The complete native extension theorem now supplies private positive
coordinates for this new prescribed scale and packed index, including
fresh normalized strong auxiliaries. Its canonical X=2^(2r+1) gives

    beta=X/q-S>0,

because q<r and S=r/(q-1)<r, while X>qr. Divisibility by q holds in the
canonical dyadic extension. Every factor and comparison therefore has
its required value. This proves completeness at the new radix, separately
in both parameter interfaces, for arbitrary finite halting time.

Original and new sources consequently represent the same accepted inputs,
but their chronological packed integers and native coordinates generally
differ. This argument does not identify their supplied positive zero sets.

## 5. Exact bound identity at the intermediate source

The source retains an intermediate packet which has already changed B to
D^8 but still uses X=q(r+beta_stage). Only against that packet define

    beta_stage=beta+S-r, beta=beta_stage+r-S.         (10)

The r/S cone does not contain either bound coordinate. Equation(10) is
an inverse triangular polynomial map on arbitrary integer assignments.
It makes every retained register, factor, residual and both complete
outputs exactly identical. The formal stage slack can be negative on
positive off-zero tuples; the checker records such cases.

At a positive new zero, the restored scalar exponent gives
beta_stage=X/q-r>0. Conversely r-S=(q-2)S>0 at a positive intermediate
zero, so the forward beta is positive. Thus the bound-only step has a
positive-zero bijection **at the same new B**. It does not provide an
identity to the frozen406 source with B=2D^8. A separate algebra oracle
can replay that old source after explicitly replacing its radix row by
D^8 and applying(10); this is a changed-definition check, not an old-polynomial
identity.

## 6. Literal ledgers and checks

|Program interface|Native form|Certificate|Comparisons|Witnesses|Polynomial|Degree bound|
|---|---|---:|---:|---:|---:|---:|
|One parameter|Computed fields|396|4|50|407=147M+260A|36156|
|One parameter|Range unit|398|3|50|406=147M+259A|36165|
|One parameter|All units|404|1|50|405=146M+259A|36165|
|Two parameters|Computed fields|395|4|50|406=148M+258A|68298|
|Two parameters|Range unit|397|3|50|405=148M+257A|68314|
|Two parameters|All units|403|1|50|404=147M+257A|68314|

The default all-unit SOS alternatives cost406 and405, with respective
degree bounds72330 and136628. The one-program native factor bounds are
5875,14094,3231,7634,2645,2645; its outer factors have bounds9,16,16.
For two program parameters they are11099,26622,6103,14418,4997,4997
and16,31,31. These are conservative propagated bounds from the actual
source, retaining only the inherited guarded main-norm cancellation.
They are neither exact-degree assertions nor global circuit optima.
Specializing C to a numeral before propagation recovers the corresponding
one-program degree dictionary; the displayed two-program bounds count C
as a variable of the uniform polynomial.

Run `python3 korec_packed_minimal_radix405.py`; `--write` regenerates the
receipt. Author generation checks all six complete ledgers and both
output closures. There are192 complete intermediate-register/outer maps,
including96 signed assignments, and384 complete output identities. All96
positive assignments in this bounded sample have nonpositive formal stage
slacks, illustrating why(10) needs a separate positivity theorem at zeros.
A separately executed literal U21 interpreter supplies12 halted histories
covering all five branch kinds. The new radix packer checks108 outer
packs with17820 chronological rows, their full transport equations,
AND and terminal corruptions. Another96 weak-range corner cases include
16 at h=2 and48 negative range signs. Six incompatible callers are rejected.
These finite checks do not materialize full positive Pell tuples; their
existence is the unbounded native extension in Section4.

Author receipt generation and a separate fresh replay pass. All six local
links resolve; source and receipt are stable for independent review.

An independent full proof/source/dependency review and fresh replay pass with
no findings. Its separate executor and manual bound maps checked288 complete
register maps and576 finalizer identities(288 signed outputs), including144
positive off-zero assignments with a nonpositive formal intermediate gap.
It independently checked12 degree/opcode/closure ledgers and332 minimum-radix
corners. A separate U21 interpreter and packing formulas checked nine halted
histories at ordinary inputs5,6,9, with54 positive outer packs covering8910
rows and54 rejected terminal corruptions. All six local links and whitespace
checks pass. These are algebra and outer-history checks, not complete Pell
fixtures. Source and receipt are unchanged after this review.
