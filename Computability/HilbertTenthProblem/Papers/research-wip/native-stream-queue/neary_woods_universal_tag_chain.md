# A 528-operation universal polynomial with four program parameters

An explicit 131-multiplication addition chain for the fixed exponent D
reduces the [557-operation U15 tag polynomial](neary_woods_universal_tag557.md)
to **528=322M+206A operations**. The resulting certificate uses
**454=297M+157A operations,25 comparisons and69 positive witnesses**.
The fixed tail coefficient also supplies the input-duration bound, leaving
**four positive program parameters**, besides the ordinary positive input.
The total-degree upper bound remains

    496070855427922989652813345268287100.

All fixed machine tables, tag rules, integer coefficient recipes and
positive native-kernel contracts are inherited unchanged. This is an
improvement to the explicit alternative construction; the separate best
universal polynomial bound remains [87 operations](complete75_normalized_strong87.md).
Neither the exponent chain nor this polynomial is claimed optimal.

## 1. The exact fixed exponent and its multiplication schedule

The explicit U15 construction supplies

    D=911894954830740789802965708213760
     =2^9 *100404692303 *17738661339441947785.

The [source](neary_woods_universal_tag_chain.py) lists131 triples
`(e,a,b)`, beginning with the supplied exponent1. Every triple satisfies
`e=a+b`, both a and b have already been computed, and exponents are emitted in
strictly increasing order. It emits
exactly the multiplication

    power_e = power_a * power_b.

The first44 steps reach100404692303. The next78 are a chain for the
second factor, scaled by the first, and the last nine steps double the
exponent. The final register is the existing public Q. Every intermediate
is an ancestor of Q; there are no unused charged steps or uncharged
products. The complete exponent list and actual final polynomial source
are retained in the [receipt](neary_woods_universal_tag_chain.json).

Induction on the listed triples proves that `power_e=q^e` for every
integer q, including zero and negative q. In particular Q remains
exactly `q^D`. No division, root extraction, inverse or subtraction of
exponents is used. This replaces the parent's160 paid multiplications
by131 and saves29 multiplications.

The bounded search used factor partitions and fixed-window schedules.
That search is not part of polynomial evaluation and supplies no
shortest-chain theorem. Correctness depends only on the explicit131
exponent additions, each checked directly by the executable source.

## 2. The fixed endpoint coefficient also bounds the duration

The shared-counter loader writes the fixed-word endpoint as

    Y=(Ar+Bz)Q+Tr+E.

Use the notation of its [proved word interface](binary_tag_shared_counter_loader.md):
`p=2^|PREFIX|+val(PREFIX)`, `b=val(MIDDLE)`, `e=val(TAIL)`,
`f=|MIDDLE|` and `g=|TAIL|`. Its last coefficient is

    E=2^g*(2^f*p+b)+e.

Thus E is exactly the positive sentinel integer of the concatenation
`PREFIX MIDDLE TAIL`, with all variable data and counter blocks omitted.
Here TAIL is the binary terminal encoding E(u), not an extra input block.

For a valid U15 program slice the fixed physical tape overhead has
`b_S>0` binary cells. PREFIX and MIDDLE encode all of them: every physical
binary cell is replaced by a nonempty tau word and then by nonempty
encoded tag blocks. Therefore their combined binary length is at least
b_S. The sentinel gives

    E >= 2^(|PREFIX|+|MIDDLE|+|TAIL|) >= b_S.

The original bound was `N_S=ceil(b_S/128)`. Consequently E>=N_S.
Replace the fifth program parameter `program_bound` everywhere by the
already present positive parameter `program_E`. The duration is now

    n=E+program_duration_gap,

where the gap is a positive existential witness. This is the same one
charged addition, with no new comparison or witness. It ensures n>E,
and hence n>N_S. Together with the recoder's dyadic-duration theorem,

    128n < 128n+b_S < 256n,

so the exact least-power-of-two initialization counter is still256n.
The substitution does not assume that E is a sentinel on arbitrary
parameter tuples; that property is proved for each valid universal
program slice, which is all the universality argument requires.

For every positive ordinary x, arbitrarily large dyadic n satisfy both
n>E and `x<2^n`. The inherited program accepts the same x under every
such leading-zero padding. Thus the stronger duration bound loses no
accepted input. Conversely every new positive zero gives a zero of the
five-parameter parent with its bound specialized to E, which meets the
required valid-slice bound. This is a language-preserving specialization;
it is not a bijection with every old witness tuple at the smaller N_S.

## 3. Exact source compatibility and positive equivalence

`rewrite_raw` first checks the complete old power-chain prefix and the
literal duration-addition gate. It verifies that every deleted power
register except Q is private: no later gate or comparison consumes one.
It then inserts the131 multiplications, retains Q, and optionally aliases
`program_bound` to `program_E`. The default build uses the alias; the
five-parameter option is retained for direct comparison.

The unit-product and three normalized-strong rewrites are applied afresh
to this actual raw source. Their existing critical-consumer assertions
still pass. The recoder low-bit predicate, independent history checksum,
positive computed fields and the fifteen-coordinate canonical auxiliary
converse are all unchanged. The only changed power expression is an
integer-polynomial identity, and the bound substitution identifies two
positive program coordinates.

More precisely, the final four-parameter source computes exactly the
parent integer polynomial after substituting `program_bound=program_E`.
The proof is the exponent induction in Section1 followed by substitution
through the retained arithmetic DAG. This identity holds on arbitrary
integer assignments and for any fixed values of the eleven Numeral
atoms. It makes no claim that off-zero computed fields satisfy the
positive native interfaces.

For each positive r.e. set S retain the parent's four effective positive
loader coefficients `(A_S,B_S,T_S,E_S)`. At a positive zero, restore the
parent source and use Section2 to recover its valid initial-counter
contract. The paid recoder, exact framed tag boundary, complete selected
tile history, fixed-halt bridge and explicit U15 simulation then imply
`x in S`. If `x in S`, choose a sufficiently large dyadic duration n>E_S;
the same component converses and fresh canonical auxiliaries produce
all69 positive witnesses. Hence one fixed integer polynomial F satisfies

    x in S iff there exist y_1,...,y_69>0 such that
    F(x,A_S,B_S,T_S,E_S,y_1,...,y_69)=0.

The four program coordinates are fixed when choosing S. They are not
additional existential witnesses. Huge coefficient integers have the
same finite recipes as in the557 packet and are not constructed at
runtime or treated as extra variables.

## 4. Literal ledgers, degree bounds and evidence

Both program interfaces have the following source-derived costs.

| Form | Certificate operations | Comparisons | Positive witnesses | Polynomial operations |
|---|---:|---:|---:|---:|
| raw SOS |439|56|88|606|
| native units |448|28|69|531|
| three normalized strong witnesses |454|25|69|**528**|

The final source split is322M+206A. Exactly29 multiplications disappear;
all additions, comparisons and witnesses remain. Merging the duration
bound changes only the list of program parameters.

The degree of Q is still D in the supplied recoder scale. Identifying
the two degree-one program coordinates cannot increase total degree.
The actual successor DAG, including the audited main-norm cancellation,
therefore passes the same degree-bound propagation as its parent:
`132D+412` for raw SOS, `342D+1042` for native units, and `544D+1660`
for the normalized polynomial. These remain **upper bounds**, not
exact-degree claims.

The checker verifies all131 integer exponent additions and108 modular
power cases. Every node is independently compared with modular powering,
for14,148 node checks, including zero and negative bases, composite
moduli and noncoprime bases. It checks1,152 full parent/successor DAG
identities,576 on signed coordinates, across all three finalizers and
both program interfaces. These comparisons assign each fixed Numeral
one consistent residue and check every shared register and the final
output. Their role is source integration; the exact exponent induction
proves the identity over the integers.

Ninety-six additional sentinel-frame cases check the E bound and exact
minimal counter without allocating a word of length n or constructing2^n. The receipt includes all six ledgers and the complete
528-gate source. These checks do not materialize the universal production,
a giant fixed coefficient or a complete numerical Pell zero.

```sh
python3 neary_woods_universal_tag_chain.py
```

Author writer and fresh-default replay passed. Root's independent full
proof/source review and fresh replay passed without findings.
Native_controller's independent full proof/source review and fresh replay
of the final sorted-chain receipt also passed without findings. Its
separate literal integer executor additionally checked288 exact complete
DAG/output identities across all three finalizers and both program
interfaces, with q in {-1,0,1} and arbitrary signed fixed-Numeral values.
Every shared register agreed. Those integer specializations supplement
the recorded modular cases; neither is described as a positive Pell zero.
