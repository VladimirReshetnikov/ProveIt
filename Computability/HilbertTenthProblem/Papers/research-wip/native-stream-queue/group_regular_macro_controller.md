# A paid regular macro controller with one shared typing kernel

This packet arithmetically certifies the fixed regular language of signed
shear codes in the [four-register matrix route](group_four_register_history.md).
It pays for edge typing, exactly one edge per position, finite-state
adjacency, both hub endpoints, and all eight physical selector outputs.
Unused edges and absent physical letters are allowed. The only external
hypotheses in the controller theorem are that its positive parameters
`B,P` are powers of two. A paid repunit equation then supplies their
common cell duration.

For an edge table padded to `m=2^h>=2` edges, the literal generic circuit is

    (3m+2h+30)M + (4m+h+p+30)A = 7m+3h+p+60,

with **25 equations** and **m+22 strictly positive auxiliary coordinates**.
Here `p<=m` is the exact cost of the eight output sums, defined below.
Its literal sum-of-squares polynomial costs `7m+3h+p+134`. The generic
schedule deliberately charges even fixed coefficient-zero and
coefficient-one products in the state-flow block. These are exact counts
of the supplied schedule, not optimality claims.

The large, fixed universal subgroup alphabet has not been transcribed
into a numerical edge table. Thus this is a compiler with an exact
parameterized ledger, not a numerical complete universal bound. In
particular, its two dyadic typing predicates and the matrix route's
duration/height condition have not been included in these counts.

## 1. The fixed controller and its positive scalar interface

The matrix route constructs a finite set of nonempty physical code words
over letters `1,...,8`, one for each signed subgroup generator. Letter0
is an identity step. The required language is

    R = (0 | code_1 | ... | code_r)*.

Use a hub state0, its letter0 loop, and separate hub-to-hub paths spelling
the codes. Give every interior vertex a different positive integer code.
An empty code, if produced for an identity matrix, can be dropped: the
hub identity loop already represents that generator. This construction
is a nondeterministic finite controller; uniqueness of a parse is not
needed.

Duplicate the hub identity loop until the edge count is a power of two
`m=2^h>=2`. Duplicates change neither the physical language nor the matrix
product. The number of states is at most m, so their codes lie in
`{0,...,m-1}`. Write each fixed edge as

    e = (a_e,b_e,label_e),

where `a_e` is its source, `b_e` its target, and `label_e in{0,...,8}`.
All these entries, m and h are fixed compiler data.

Supply positive relation parameters `B,P,Shat_0,...,Shat_7`. The eight
physical selector values to be certified are `S_i=Shat_i-1`; they may be
zero. Supply positive edge hats `Ehat_e`, a positive repunit J and a
positive margin beta. Put `E_e=Ehat_e-1` mathematically; the source does
not spend m separate gates decoding these values.

Pay the three comparisons

    (B-1)J+1=P,          m+beta=B,
    sum_e Ehat_e=J+m.                                  (1)

The first costs1M+2A, the second1A, and the third m additions, counting
both its sum and its right-hand side. Equation(1) gives

    B>m,       sum_e E_e=J,       0<=E_e<=J.

Under the external assumptions `B=2^d,P=2^ell`, with d,ell positive,
the first equation proves `ell=dt` for an integer t>=1 and

    P=B^t,       J=1+B+...+B^(t-1).                    (2)

For completeness of this elementary geometry step, divide ell by d:
`ell=dt+r`, `0<=r<d`. Modulo `2^d-1`, divisibility of `2^ell-1` gives
`2^r-1=0`; the latter lies between0 and `2^d-2`, hence r=0.
Positive J also gives P>=B and therefore t>=1. Conversely(2) gives
the first equation. This is not a certificate that B and P themselves
are dyadic; those two predicates remain explicit obligations.

## 2. One subset test types all m edge fields

Define

    K=1+P+...+P^(m-1),
    H=sum_e E_e P^e,       M=J*K.                       (3)

Use H and M as packed bit strings only after proving their digit
interpretation. Already from positivity and the checksum in(1),

    H>=0,       M-H=sum_e (J-E_e)P^e>=0.               (4)

The condition `H AND M=H` says H has bits only at the cell origins in
the m consecutive P-sized lanes. Because `E_e<=J<P`, there is no carry
between these lanes when forming H. Because B is dyadic and(2) holds,
the ones of each copy of J are exactly its radix-B cell origins. Thus

    H AND M=H

is equivalent to every `E_e` having t radix-B digits in `{0,1}`. This
is an ordinary bitwise subset relation, not an uncharged arithmetic
instruction. The next paragraph supplies its actual positive kernel.

The applicable imported theorem is the **binary** three-selector53
theorem, Sections1--3 of
[native_binary_three_row_fifo58](native_binary_three_row_fifo58.md).
It is not the different ternary three-selector53 theorem. The binary
source has `53=28M+25A`, fourteen comparisons and nineteen positive
auxiliaries, beyond q and its three positive fields. Its exact projection
is a partition of `q-1` into three binary fields, q a power of two and
F0 odd. Its proof includes the smaller bootstrap `q>=4,r>=21` and a
fresh strictly positive Pell extension for every such partition.

Supply only its field F0 as an additional positive coordinate. Compute

    H8=8H,       F2=H8+4,
    M8=8M,       gap8=M8-H8,       F1=gap8+2,
    q0=F0+M8,    q=q0+7.                              (5)

By(4), F1>=2 and F2>=4. Hence the entire imported positive domain is
valid before invoking its theorem. Moreover

    q=F0+F1+F2+1

is an identity. Remove the native three-addition checksum, omit its
comparison, and compute q by(5) before every q-dependent gate. The
other fifty native gates and thirteen comparisons are unchanged,
with the core scale `n2` aliased to q. Equation(5) costs2M+5A, making
this part **57=30M+27A**. It uses the nineteen original auxiliary
coordinates and F0; F1,F2,q are computed registers.

To see the exact subset relation, the native theorem says F1,F2 are
disjoint. Their low three bits are respectively `010` and `100`.
Their upper parts are M-H and H. Disjointness is therefore equivalent
to `(M-H) AND H=0`, which is equivalent to `H AND M=H`: binary addition
`(M-H)+H=M` has no carries precisely in this case. The third field
fills the complement and has its units bit set. Thus the low-first
class labels are `0,1,2`; all three classes occur even when H=0 or H=M.

Conversely, for any H subset of M choose a power of two Q>M and set

    F0=8(Q-M)-7,       F1=8(M-H)+2,       F2=8H+4.

These are positive disjoint fields partitioning `8Q-1`, and F0 is odd.
Equation(5) computes q=8Q exactly. The binary53 positive converse gives
all nineteen remaining coordinates at this actual new packed index.
This proves a full positive extension; finite numerical experiments
with small Pell values are not used as its substitute.

The conditional positivity in(4) is essential to the proof order.
For arbitrary positive supplied scalars failing the checksum, F1 may
be negative. Such assignments are legitimate evaluations of the
polynomial source, but the binary theorem is invoked only after(1)
has forced every displayed computed field to be positive.

## 3. Exact one-hot edges, adjacency and physical outputs

The subset kernel types every E_e as a Boolean radix-B word. At any
position the sum of their digits is at most m, strictly below B.
The checksum `sum E_e=J` therefore has no carries, and uniqueness of
radix-B expansion forces exactly one selected edge at every position.

Define the two source/target words by charged arithmetic

    A=sum_e a_e Ehat_e - sum_e a_e,
    T=sum_e b_e Ehat_e - sum_e b_e,

and compare

    A=B*T.                                             (6)

All fixed coefficient products in this dense schedule are paid. The
two fixed sums in the corrections are compiler numerals. At every
position, A's digit is the source code of the unique selected edge and
T's digit its target code. These digits are less than m<B. Consequently
(6) is equivalent to: first source0, each later source equal to the
preceding target, and final target0. This follows directly by comparing
the constant, interior and top radix-B digits. It proves an actual
hub-to-hub path in the fixed table, not merely a flow conservation
identity that permits disconnected cycles.

For each physical label i+1 compare

    Shat_i = 1+sum_(label_e=i+1) E_e.                   (7)

These are the eight selector ports used in the four-register packet.
The unique selected edge makes them Boolean and mutually exclusive
at every position; the all-zero case is a hub identity edge. More
generally any letter0 edge in a supplied table represents the physical
identity, but this macro construction puts such edges only at the hub.

The literal port schedule uses no extra witness. If the label has
`k_i=0` edges, compare Shat_i with the fixed1. If `k_i=1`, compare it
with that edge hat. If `k_i>=2`, sum its k_i edge hats and subtract
the fixed numeral `k_i-1`, costing k_i additions/subtractions. Therefore

    p=sum_(i:k_i>=2) k_i <= m                           (8)

is the exact projection cost; all eight comparisons are retained.

**Controller theorem.** Under the explicit dyadic B,P assumptions, the
positive projection of(1),(5)--(7) and the retained binary kernel is
exactly: `B>m`, `P=B^t` for t>=1, and the eight supplied Shat values
encode the physical letters of a length-t path from hub0 to hub0 in
the fixed table. For the constructed table this means a word in R.

Soundness is the sequence of arguments above. For the converse, select
one edge parse of the given physical word. Its indicator fields give
nonnegative E_e and strictly positive hats, including every unused
edge. Set J to the repunit and beta=B-m>0. Equations(1),(6),(7) hold;
the subset construction gives F0 and all positive native auxiliaries.
Thus every auxiliary is restored positively, without requiring the
word to use every edge or every physical label.

## 4. Literal circuit, witnesses and polynomial cost

Since m=2^h, construct K from

    K=product_(j=0)^(h-1) (1+P^(2^j)).                 (9)

The powers use h-1 squarings, the factors h additions, and their product
h-1 multiplications: `(2h-2)M+hA`. Horner-pack the m edge hats, then
subtract K to get H without separately decoding any edge. This costs
`(m-1)M+mA`. Finally M=J*K costs one multiplication. These are literal
gates even though the identities are convenient to state using powers.

| Part | M | A | Equations |
|---|---:|---:|---:|
| Repunit geometry |1|2|1|
| Positive radix margin |0|1|1|
| Hatted edge checksum |0|m|1|
| K, H, M packing |m+2h-2|m+h|0|
| Three-class subset kernel including(5) |30|27|13|
| Dense source/target state flow |2m+1|2m|1|
| Eight physical ports |0|p|8|
| **Total** | **3m+2h+30** | **4m+h+p+30** | **25** |

The strictly positive auxiliary list is

    Ehat_0,...,Ehat_(m-1), J, beta, F0,
    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,y_aux,
    odd_half,bound_beta.

There are m+22 coordinates besides the ten positive relation parameters
B,P,Shat_0,...,Shat_7. Computed registers, including differences and
state-word corrections, need not be positive off the zero set. All
fixed numeral multiplications, such as those by8 and the state codes,
have been charged. State codes and their sums are fixed integers;
no variable preprocessing of the ordinary input is hidden in them.

The source also builds its complete sum of squares:25 residual
subtractions,25 squares and24 additions. Hence its exact literal
polynomial schedule is

    (3m+2h+55)M + (4m+h+p+79)A = 7m+3h+p+134.

This polynomial has exactly the same positive zero set as the displayed
system. No degree optimality or universal operation bound is asserted.
For example, the nonuniversal fixture with codes(1,3),(2,4),(5,7,6,8)
pads to m=16,h=4,p=0 and costs184=86M+98A before sum of squares.
This illustrates the cost of compiling a table rather than claiming
that finite control is free.

## 5. Two omitted-hypothesis failures and the integration boundary

The radix margin is substantive. At B=4,t=2,J=5, take eight edge fields
`(1,1,1,1,1,0,0,0)`. Every field is a bit subset of J, and their sum
is J. Yet five edges occur at the first cell and none at the second.
With an all-hub-loop table, state flow is also satisfied. The paid
margin excludes this carry alias.

Conversely the scalar checksum, bound and flow cannot replace the
subset kernel. At B=8,t=2,J=9, take four all-hub-loop edges and fields
`(2,7,0,0)`. They are nonnegative, each below P=64, sum to J and satisfy
state flow. Their cell digits are not Boolean; the subset kernel rejects
them. These examples refute the respective shortcuts, not other
possible controller compilers.

The matrix application may pad an accepted word with hub identities.
It can therefore choose a longer duration and a larger matrix radix
until B>m. Padding preserves its product. This explains why the fixed
margin does not obstruct the eventual existential matrix representation;
the component theorem itself always states the margin explicitly.

The paid repunit relation links B and P once both are dyadic. It does
not pay for either dyadic predicate or for the matrix height condition
relating physical duration to its initial test-vector parameter. The
local native scale q from(5) is a different integer and must not be
identified with that geometric parameter. The selected-source
AND batch and the matrix recurrence/ordinary-input endpoint also remain
separate components. Their shared registers and positivity hypotheses
must be composed explicitly before quoting a joint count.

This closes a finite-control interface mathematically and arithmetically,
conditional on the stated geometry. The universal subgroup's finite
presentation and codes are not numerically instantiated here. The
controller introduces no new ordinary-input recoding: its physical
ports connect directly to the existing signed-shear history interface.

## 6. Executable evidence

The [checker](group_regular_macro_controller.py) and
[receipt](group_regular_macro_controller.json) record actual instructions,
positive coordinate lists, comparisons and exact ledgers for four fixed
macro tables. They compare every complete residual and the whole
sum-of-squares polynomial on1,024 arbitrary positive supplied assignments
against separately expanded formulas, including assignments for which
computed F1 is negative. The checker retains the original binary43 core;
only its three-field outer source is specialized as proved above.

Finite edge sequences are checked against direct state following, and
small physical languages against an independent word-break recognizer
for the macro expression. Positive outer fixtures include all-idle words
of32 different lengths, so omission of every nonidentity edge is tested.
All6,561 bit-subset pairs through eight bits check the three-class
padding; geometry and both omitted-hypothesis examples are also audited.
The outer fixtures intentionally do not materialize the enormous Pell
coordinates. Their existence is the full imported positive theorem,
applied to the exact newly constructed partition.

Run the checker without arguments to compare its saved receipt; use
`--write` to regenerate it. These finite audits supplement the proofs
and do not turn the remaining geometry assumptions into certificates.

An independent full proof/source/default review passed with no findings.
It additionally compared512 arbitrary positive assignments against the
untouched binary53 source after restoring its three computed fields and
scale;243 assignments had negative computed F1 off the zero set, and
1,958 port instances had no contributing edge. Another13,640 ordered
edge words on separately generated arbitrary tables verified the state
flow and both endpoints. The review checked the positive proof order,
the dyadic geometry scope and every literal ledger.
The root agent also completed an independent full proof/source/default
review without findings. The packet is frozen at the displayed schedule.
