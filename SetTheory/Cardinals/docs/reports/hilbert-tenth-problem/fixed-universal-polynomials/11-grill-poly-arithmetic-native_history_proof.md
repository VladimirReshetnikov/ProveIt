# Scalable weak-cone native history: correctness transfer

## Statement and scope

For any fixed nonempty sequence of uint32 exponents `n[0],...,n[m-1]`,
`native_history.build(dag,n,X)` emits an integer polynomial unit `U`, ten
comparison pairs `(a_j,b_j)`, and the width `P0=X+Z0`. All newly declared
coordinates are required to be positive integers. The arithmetic input `X`
is supplied by the caller and must be positive on the composed valid slice.

With `R_j=a_j-b_j`, define the complete native polynomial

`F_native = U*(1+sum_{j=0}^9 R_j^2)-1`.

This is identically the pinned composed205 native polynomial for the same
program, input, and positive coordinate names, after a bijective renaming of
coordinates. The schedules differ by explicit distributive identities,
prefix summation, and independent exact power/repunit schedules proved below.
This identity holds over the integers without positivity assumptions. It is
not merely an equality of zero sets or a check on valid histories.

Consequently the pinned weak-cone positive soundness and full positive
completeness theorem transfers: positive zeros are equivalent to an actual
halting padded Grill input of value `X` and some dyadic width `P0>X`.
For an already fixed admissible dyadic width and actual finite halting word,
the native converse supplies positive witnesses at that width. The source
packs arbitrary nonempty duration existentially; it has no external trace
cutoff. A closure can have a post-halt suffix, and soundness promises actual
halting at or before the closure length, not causal execution after emptying.

This file establishes only the native history component. Universality, the
ordinary-input decoder, exact initial word binding, and any additional
comparison constraints belong to the caller's separate composition proof.
No historical 205-operation cost is assigned to the large emitted source.
All degree claims must be made from the resulting paid DAG; this file makes
no exact-degree assertion.

## Frozen references and no source execution

All references below are at commit
`2d887f0fa768fd67f3e545d83f8998b5780e530d` of
`VladimirReshetnikov/ProveIt`, under
`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`.

- [Composed205 proof](https://github.com/VladimirReshetnikov/ProveIt/blob/2d887f0fa768fd67f3e545d83f8998b5780e530d/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/grill_tag_native_composed205.md)
- [Weak-cone soundness and complete converse, Sections 2–3](https://github.com/VladimirReshetnikov/ProveIt/blob/2d887f0fa768fd67f3e545d83f8998b5780e530d/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/grill_tag_native_weak_cone.md)
- [Native word-closure theorem](https://github.com/VladimirReshetnikov/ProveIt/blob/2d887f0fa768fd67f3e545d83f8998b5780e530d/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/grill_tag_native_word_closure.md)
- [Native unit/restoration proof](https://github.com/VladimirReshetnikov/ProveIt/blob/2d887f0fa768fd67f3e545d83f8998b5780e530d/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pcp_uniform_affine_pair_units.md)
- [Full small receipt](https://github.com/VladimirReshetnikov/ProveIt/blob/2d887f0fa768fd67f3e545d83f8998b5780e530d/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/grill_tag_native_composed205.json), Git blob SHA `929d89c9f1ac1b727e207d8b518cfab54c8c4125`

The receipt was fetched through the GitHub connector as JSON data. Four
complete unit-source fixtures, for `(0)`, `(1)`, `(0,1,1)`, and `(2,0,1)`,
are frozen in `native_receipt_fixtures.json`. Their upstream source SHA-256
is `4084a58d5cf30694a8717c26d0abdf2aecc2fa6a7099d9815f35521005afab94`.
The four kernels have exactly the same 67 named binary definitions after
replacing their four caller ports by `@H`, `@M`, `@Z`, `@scale`; only
topological order may differ. These 67 definitions, six comparisons, four
unit-factor names, and sixteen positive coordinate names are frozen in
`native_unit_kernel.json`, SHA-256
`2d88343037c08fe8b073f67dca531ee73309c0735c1d98a23c20b9ddb1eb08ae`.
The emitter checks that hash before loading the kernel. No upstream Python
file is imported, executed, compiled, or dynamically loaded.

The inspected exact source motifs are the slope-class history, its positive
unit projection, the native word-closure adapter, phase sharing, phase
residual compression, and the weak input cone. These templates determine
the general parametric formulas below; the small receipts independently
check implementation identity but are not the proof for all program sizes.

## 1. Coordinates and fixed affine coefficients

There are `s=2m` original selector hats `Shat_i`, seven outer coordinates
`Z0,Vfinal,phase_initial,height_slack,H_U,H_V,global_bound`, and one positive
selected-history hat `ZVhat_j` for each distinct exponent. Let `g` be the
number of distinct exponents. Groups are ordered by first occurrence, as
in the pinned slope-class template. Group `j` is

`I_j={2i+1 : n[i]=e_j}`.

These are precisely all nonbaseline V slope classes, with baseline 1. All
U slopes equal 2, so there are no U exception classes. The two tiles at
phase `i` are exactly

`(2,0,1,0)` and `(2,1,b(n[i]),d(n[i]))`,

where `b(n)=2^(2n+1)` and `d(n)=(2^(2n+1)-2)/3`. The latter is an integer
because `4^n=1 mod 3`; it also equals `2*(4^n-1)/3`. Fixed recipes denote
these exact integers, independent of every polynomial coordinate. Reading
a numeral is free in the arithmetic model; multiplying it by a runtime
register is emitted and charged. No variable exponentiation or uncharged
runtime division is used.

The template multiplier is the least power of two at least
`max(8,s+4,1+max_tile(a+c,b+d))`. Since
`1+b(n)+d(n)=(4*b(n)+1)/3` lies strictly between `2^(2n+1)` and
`2^(2n+2)`, our exact numeral is

`K=2^max(3,ceil(log2(s+4)),2*max(n)+2)`.

The code uses `(s+3).bit_length()` for the middle integer, without floating
point logarithms. This also covers `n=0` and the U coefficient bound 3.

The outer positive witness count is `s+g+7`. The native kernel has exactly
sixteen retained positive coordinates, giving `s+g+23`. At the target
`m=397488`, `g=2030`, this is exactly `797029`. Equal appendants retain
different chronological selector hats; only already justified selected
history classes are shared.

## 2. Literal width, height, and affine transports

The emitter computes exactly

`P0=X+Z0`, `Uf=P0*Vfinal+X`,
`D=Uf+phase_initial+height_slack`, `B=K*D`,
`sel_i=Shat_i-1`, `J=sum_i sel_i`, `P=(B-1)*J+1`.

The implementation evaluates J through pair sums; this is associativity
and the subtraction of the same fixed `s`.

Define `G_j=sum_{i in I_j} sel_i`, `z_j=ZVhat_j-1`. Then

`nextU=2*H_U+sum_j G_j`,
`nextV=H_V+sum_j (b(e_j)-1)*z_j+sum_j d(e_j)*G_j`.

Every odd selector belongs to exactly one group, so the first formula is
the literal U linear form. Distributing each grouped second term gives
exactly the template's term for every odd selector and exactly its
constant unhat correction. No selector is identified or eliminated.

The first three comparisons are exactly

1. `H_U+H_V+sum_j ZVhat_j+global_bound = P`
2. `B*nextU+1 = H_U+P*Uf`
3. `B*nextV+1 = H_V+P*Vfinal`

The positive hats in comparison 1 are intentional: this is
`H_U+H_V+sum_j z_j+g+global_bound=P`, precisely the pinned global bound.

## 3. Exact phase residual, with no quadratic polynomial expansion

Let `pair_i=Shat_(2i)+Shat_(2i+1)` and `S_i=pair_i-2`. Then

`J=sum_i S_i`, `Tphase=sum_{i=1}^{m-1}(m-i)*S_i`.

The emitted nested prefix sum has coefficient `m-i` on `pair_i`, because
pair i occurs in prefixes i through m-1. Subtracting `m*(m-1)` removes
`2*sum_{i=1}^{m-1}(m-i)`. Each prefix and accumulator addition is paid,
and each generated register is consumed. Only the current two accumulator
handles are retained; no expanded prefix polynomial is cached.

The historical projections are proof-only formulas

`Next=m*J-Tphase`, `Q=(m+1)*J-m*S_0-Tphase`.

Substituting these and the literal `P=(B-1)J+1` gives the exact identity

`B*Next+phase_initial-Q-m*P`
` = m*pair_0-(B-1)*Tphase+phase_initial-(J+3*m)`.

Those are the emitted comparison operands for m>1. For m=1 the same
residual is `phase_initial-1`, and only those operands are used. This
identity is over every commutative ring and uses no positivity, Boolean
selectors, phase validity, vanishing residual, or independent treatment
of J/P. The same actual B is used on both sides. Hence replacing the
phase residual in the complete polynomial preserves it identically.

## 4. Exact joined native ports

Write `pack(v)=sum_i v_i*P^i` and `rep(k)=sum_{i=0}^{k-1} P^i`, with
`rep(0)=0`. Horner packing is proved by descending induction. The emitted
repunit identities are

`rep(2k)=rep(k)*(1+P^k)`,
`rep(2k+1)=rep(2k)+P^(2k)`.

Powers are fixed-exponent square-and-multiply expressions in P, using
paid binary multiplications and explicit caches. All exponent integers
are fixed by m/g, not existential inputs. The identities are polynomial
identities, including at P=0 or P=1, and require no geometric division.

Set

`S=pack(sel)`, `Mc=J*rep(s)`, `T=H_U+P*H_V`,
`Gpack=pack(G)`, `Hb=H_V*rep(g)`,
`Mb=(B-1)*Gpack`, `Zb=pack(z)`,
`RM=(D-1)*J*(1+P)`.

These are exactly the native slope-class ports for zero U exceptions
and g V exceptions. In particular `S=pack(Shat)-rep(s)` is exact
distributivity, and the same rep(s) is reused in Mc.

With `ec=g`, `er=g+s`, `et=g+s+2`, `ei=g+s+4`, define

`common=P^ec*S+P^er*T`,
`H=Hb+common+P^et*B+P^ei*P0`,
`M=Mb+P^ec*Mc+P^er*RM+P^et*(B-1)+P^ei*(P0-1)`,
`Z=Zb+common`, `scale=P^(g+s+5)`.

These formulas match the inspected native adapter's controller, range,
top/radix, and exact dyadic-input-width lanes term for term. Nothing is
omitted when grouping linear forms. All H/M/Z/scale arithmetic is emitted
before the fixed kernel, and its multiplications are included in the DAG.

## 5. Fixed unit kernel and complete polynomial identity

The sixty-seven frozen native rows receive precisely H,M,Z,scale. Their
q multiplier and padded ports are `q=16*scale`, `16H+12`, `16M+10`,
and prescribed `F3=16Z+8`, exactly as the parent adapter. The same sixteen
positive witnesses occur, with the same six retained native comparisons.
The fourth native comparison is the strong norm coefficient equality;
it is not silently removed. Together with the four outer comparisons,
there are exactly ten nonunit comparison pairs.

The kernel returns the literal four-factor product in the order
`R15 * P17 * first_unit * bs_q`. Since all four input ports and all native
coordinates agree with the template by Sections 1–4, induction along
the frozen native rows proves equality of every kernel register, all six
native residuals, every unit factor, and their unit product. Combining
this with equality of all four outer residuals gives equality of the
whole native polynomial, on all supplied tuples.

For completeness, the sign-safe restoration argument is not an extra
numerical assumption. The three norm factors cannot be -1 modulo 4:
the main norm is a square or sum of squares modulo 4, the auxiliary
factor is congruent to one of two squares, and the first factor is the
positive gap's square modulo 4. If the integer product is 1, every factor
is ±1, hence all three norms are 1 and the fourth checksum is 1. The
retained strong comparison restores the original auxiliary coefficient.
The six projected definitions restore strictly positive native
coordinates, and the odd root gap restores the original positive root.
These are exactly the pinned unit theorem's hypotheses and formulas.

Finally, `1+sum R_j^2` is a positive integer. Therefore
`U*(1+sum R_j^2)=1` holds exactly when U=1 and every R_j=0, regardless
of the sign of U away from solutions. If a caller adds additional
integer comparisons C_k, the correct one-unit extension is

`U*(1+sum_j R_j^2+sum_k C_k^2)-1`.

It equals `F_native+U*sum_k C_k^2`, not `F_native+sum_k C_k^2`.
No second unrestricted native checksum is multiplied into U.

## 6. Positive semantic transfer

On positive coordinates with X>0, `P0>=2`, `0<X<P0`,
`Uf>P0,Vfinal,1`, and `D>Uf,phase_initial` with D>=5. Decoded selectors
and selected-history coordinates are nonnegative, so J>=0 and P>=1.
The global equality at a zero forces P>1, J>0, B<=P, and the required
history/selection bounds. Thus `P0<D<B<=P`. The H/M/Z lanes have the
same no-carry range premises as the native theorem. The retained native
classification forces the scale and P dyadic, separates the lanes, and
in particular gives `P0 AND (P0-1)=0`. P0>=2 makes P0 a genuine positive
dyadic width. The range/selector/transport comparisons recover one
nonempty common reverse affine history, and the phase comparison fixes
its reverse chronological phase path. The endpoint `Uf=P0*Vfinal+X`
then yields the word closure by unique sentinel coding. The queue
therefore halts at or before the proposed closure length.

Conversely, for an actual finite halting word of admissible width P0,
set Z0=P0-X. Reverse its finite tile sequence, construct the two sentinel
histories and the one-hot selector hats, choose dyadic
`D>Uf+phase_initial`, and use positive height slack. Pack at B=KD and
P=B^t. The three transports and phase equation telescope. The unchanged
global estimate

`global_bound >= ((K-4)*D+3)*J+1-g > 0`

supplies positive slack. The joined AND holds at precisely the chosen
scale, including the exact P0 lane. The pinned native AND converse
supplies all positive Pell witnesses, after which the pinned unit
projection supplies the sixteen retained witnesses. This is a theorem
application at the exact requested scale, not the assertion that the
small checker has materialized a complete enormous Pell zero.

The strong/weak signed substitution is unnecessary for this soundness
argument. This component retains the weak cone; it never claims a
positive-fiber bijection to the strong `P0=3X+Z0` cone.

## 7. Checks and ledger discipline

Run `python native_check.py`. This executes only newly written local
code and frozen JSON data. It independently checks:

- identical frozen kernel definitions in all four complete receipts
- exact small K and scale exponents and complete positive witness counts
- all-gate/all-input liveness for the emitted small native source
- every semantic interface, all ten residuals, U and the complete
  native polynomial on 16 exact signed integer and 160 modular tuples
- the exact phase coefficient formulas at seven sizes, including m=397488

Run `python native_backend_check.py` for the independent compact-backend
integration check. It emits the four complete native polynomials into binary
streams, audits every emitted gate and supplied coordinate for liveness, and
compares 192 complete binary-stream evaluations against the pinned source
receipt at four primes. It also checks 180 independent fixed-numeral values,
including the largest target exponent and moduli divisible by three. The
new `(0,1,1)` schedule has 206 operations, 93M+113A, and formal degree upper
1187. It is not the historical 205 schedule: these explicitly counted
schedule differences do not affect the proved polynomial identity.

The finite checks are implementation regressions; Sections 1–6 are the
parametric transfer proof. Full-size counts must come from the caller's
binary DAG, including a backwards liveness audit from the final output.
All numeral-by-register products, all prefix additions, all power and
repunit multiplications, all 67 native rows, and all finalizer arithmetic
are paid. No historical named interface represents an uncharged gate.
