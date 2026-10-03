# A natural-domain parity truth atom and a paid NAND example

For an **already evaluated signed integer** `L`, the polynomial

```
P8 = (L−2(qp−qm)−b)² + b(b−1)
```

uses three private natural witnesses `(qp,qm,b)`, has degree two, and evaluates in **8=3M+5A** binary arithmetic operations. At every natural zero, `1−b` is the truth value of `L ≡ 0 (mod 2)`. Its witness fiber is infinite. Adding the unsquared natural product `qp*qm` restores a unique fiber at **10=4M+6A**. If `L` is known to be natural, the separate specialization

```
P7 = (L−2q−b)² + b(b−1)
```

uses two private natural witnesses `(q,b)`, has a unique fiber, and costs **7=3M+4A**.

These counts evaluate the complete atom penalty. Separately materializing the truth expression `1−b` costs **one further addition/subtraction**. The emitted NAND compositions below absorb that expression into paid arithmetic, so it is not silently treated as a free output register. Computing an upstream affine `L` remains the caller's cost. There is no variable-modulus, whole-real-orthant, optimality, or universal-operation claim.

The [source](parity_truth_specialization.py) is a portable writer/checker that emits every binary gate of all 18 reported forms into its [receipt](parity_truth_specialization.json). It authenticates the actual existing `presburger_congruence_five.py` source, SHA-256 `f33ba14f16009f4e825e00a91d1714696dadf34002ada3bf72fcbccc04a52cfc`, as comparison context. It does not import or run that source's existing tests.

## Exact natural fibers, including negative input

For every integer `b`, `b(b−1)≥0`, with equality precisely at `b=0,1`. In particular this holds on the supported natural witness domain. Each summand of P8 is nonnegative there. Hence a zero forces `b∈{0,1}` and

```
L = 2(qp−qm)+b.
```

Let `(q,r)=divmod(L,2)`, using `r∈{0,1}` even for negative `L`. Then the complete P8 natural fiber is

```
b = r,
qp = max(q,0)+t,
qm = max(−q,0)+t,          t∈N.
```

Conversely every displayed tuple is a zero. Thus the parity bit is unique and correct, but every input has countably infinitely many auxiliary witnesses. For example, at `L=0`, both `(0,0,0)` and `(1,1,0)` are zeros, as is every `(t,t,0)`.

For P10 = P8+qp*qm, all three summands are nonnegative on natural witnesses. Its zeros have `qp*qm=0`, which forces `t=0` in that ray. This gives exactly one witness for each signed integer input. The added product does not need squaring on the natural domain.

For P7, a zero means `L=2q+b` with the unique remainder bit. If `L≥0`, the quotient `q=floor(L/2)` is natural and unique. If `L<0`, no natural zero exists. Therefore deleting `qm` is justified only for a known-natural input; it is not an all-signed-input simplification. The zero input is allowed.

## Relation to the reviewed five-witness atom

At fixed modulus two, the five-witness parent's natural zeros force its fields `s=0`, `h=1−b`. Its signed quotient split has `qp*qm=0`. Restoring these two fields gives a bijection from P10 zeros to the parent zeros. On `L≥0`, the parent additionally forces `qm=0`, so P7 also bijects to that restricted parent fiber. P8 instead has the same existential truth relation and a many-to-one normalization to the parent: replace its quotient split by `(max(q,0),max(−q,0))` before restoring `s,h`.

These are **zero-set/interface statements**, not equality of the old and new polynomials on arbitrary tuples. Write

```
R = L−2(qp−qm)−b,
U = qp*qm,
V = b(b−1).
```

The old five-residual SOS, after the formal substitution `s=0,h=1−b`, is `R²+U²+V²`. Consequently the exact all-value correction is

```
P_parent|graph − P10 = (U²−U)+(V²−V).
```

The complete source checker proves this symbolic identity. Nonnegative restoration of `h=1−b` is needed only at the zeros, where the remainder is a bit. It is not claimed on arbitrary new natural tuples.

Private ports matter. If another condition sees `qp` or `qm`, P8 cannot replace the canonical parent without reviewing that condition: imposing `qp=qm=1` at `L=0` is satisfiable for P8 and impossible for P10 or the parent. A safe existential replacement exposes only the already evaluated input and parity truth, keeping all quotient helpers private. Canonicality, finite-foldness, witness counting and sampling conclusions must use P10 or P7, not P8.

## Literal atom schedules

For P8 compute, in order:

```
qdiff = qp−qm                 A
q2    = 2*qdiff               M
r0    = L−q2                 A
r     = r0−b                 A
r2    = r*r                  M
bm    = b−1                  A
v     = b*bm                 M
P8    = r2+v                 A
```

P10 appends `u=qp*qm` and `P10=P8+u`: one M and one A. P7 starts directly from `2*q`, omitting the first subtraction. Constants such as 1 and 2 are available, but multiplying or adding them is charged. A register may be negative; only the declared input/witness domain is restricted. There are no unused paid gates in the emitted schedules.

## One complete NAND composition

Let two atoms have inputs `L1,L2`, remainder bits `b1,b2`, and evenness truths `t1=1−b1`, `t2=1−b2`. The supplied natural output `z` should satisfy `z=NAND(t1,t2)`. Reuse the already paid `bm1=b1−1`, `bm2=b2−1` and form

```
g = bm1*bm2 = t1*t2,
v = z−1,
NAND residual = v+g.
```

The complete relation polynomial is

```
P_relation = P_atom1 + P_atom2 + (z−1+g)².
```

The atom penalties and the final square are independently nonnegative on natural assignments, so a zero first fixes both correct parity bits and then fixes the unique Boolean `z`. No extra Boolean witness or truth register is omitted from the count. Adding `v²` accepts exactly the true NAND outcomes. It shares `v` and changes neither atom's private witness semantics.

| Atom mode | NAND relation, supplied z | Accepted NAND, retaining z | z=1 graph projection | Fused accepted predicate |
|---|---:|---:|---:|---:|
| Signed, existential quotients | 22 = 8M+14A | 24 = 9M+15A | 20 = 8M+12A | **17 = 6M+11A** |
| Signed, canonical quotients | 26 = 10M+16A | 28 = 11M+17A | 24 = 10M+14A | **21 = 8M+13A** |
| Known-natural inputs | 20 = 8M+12A | 22 = 9M+13A | 18 = 8M+10A | **15 = 6M+9A** |

Every entry includes all atom arithmetic, Boolean-gate arithmetic, squares and final additions. The signed rows retain six quotient/bit witnesses before an optional z; the natural row retains four. The supplied-output relation and accepted form have degree four. The fused accepted form below has degree two.

Setting `z=1` in the accepted polynomial makes the acceptance square zero and gives

```
P_projected = P_atom1 + P_atom2 + g².
```

This is an exact full-polynomial identity on the restoration graph, not merely a zero equivalence. It erases the output witness because the requested output is fixed, and it is not a replacement for the general supplied-output relation.

A small additional natural-domain simplification merges the two Boolean penalties with the unsquared `g`:

```
B(b1,b2) = b1(b1−1)+b2(b2−1)+(b1−1)(b2−1)
         = (b1+b2−1)²−b1*b2.
```

For natural `b1,b2`, if both are at least one, the three terms in the first expression are nonnegative, and their sum vanishes only at `(1,1)`. If `b1=0`, the sum is `(b2−1)²`; the other case is symmetric. Thus B is nonnegative on N² with zeros **exactly** `(0,1),(1,0),(1,1)`. These are precisely the remainder-bit pairs for true NAND of evenness. Combining B with the two quotient residual squares, and with `qp*qm` terms in the canonical mode, gives the full fused predicate in the last table column.

The factored block B costs `2M+3A`: compute `s=b1+b2`, `s−1`, its square, `b1*b2`, and subtract. Each signed quotient residual square costs `2M+3A`; a natural one costs `2M+2A`. Add the two squares and B with two additions. This proves the 17/15 totals directly, including every finalizer operation. Canonical quotient products add two M and two final additions, giving 21. No now-unused `b−1` register is retained in this fused schedule.

The full all-value relation between the projected and fused forms is

```
P_projected − P_fused = g²−g.
```

Thus the fusion preserves natural zeros, not the full polynomial. The identity is symbolically checked in all three modes. Its soundness does not assume the atom Boolean equations first: it uses the independent nonnegativity and exact zero classification of the combined B block. Individual `g` may be negative on arbitrary natural b's; using it without this combined-block argument would not justify a sum-of-penalties inference.

As a separate mathematical observation, B is nonnegative on every integer pair, with the same three zeros. If `b1*b2≤0`, its second expression is a sum of nonnegative terms and equality forces sum 1 and product zero. If the product is positive, both integers have the same sign; put `s=b1+b2`. For `s≤−2` the bound `(s−1)²−s²/4>0` applies. For `s≥2` it is positive at every integer `s≥3`, and equality at `s=2` forces `(1,1)`. The public zero-set contract remains natural witnesses; in particular the canonical quotient-product variant must not inherit an unrestricted signed-helper claim from this observation.

## Counterexamples outside the contract

- **Nonnegative real witnesses:** P8 at natural `L=0`, `qp=qm=0`, `b=1/2` is zero with a fractional truth. At `b=1/4` it is `−1/8`, so the polynomial is not globally nonnegative on the real orthant. P7 at natural `L=1,q=0,b=1/2` is also a false fractional-bit zero. Unsquared `b(b−1)` is sound because b is an integer, not because it is a product of nonnegative real affine forms.
- **Signed helpers in P10:** `L=3,qp=1,qm=−1,b=0` makes its residual square 1 cancel `qp*qm=−1`, yielding zero with false even truth. Natural quotient witnesses are essential for this canonical penalty.
- **Strictly positive witnesses without shifts:** an even input needs `b=0`; directly reinterpreting the same formula over strictly positive coordinates loses all even inputs. The positive-witness convention requires explicit shifted variables and a newly charged schedule.
- **Other moduli:** the emitted formula hardcodes two and is a parity atom, not a replacement for a general fixed-modulus congruence atom. No arbitrary modulus is accepted by the API.

## API and finite evidence

`build_atom(mode, materialize_truth=False)` and `build_nand(mode, variant=...)` return fresh complete packets. Modes are exactly `signed_existential`, `signed_canonical`, `natural`; NAND variants are `relation`, `accepted`, `projected`, `factored`. `checked` compares every source and metadata field with a fresh canonical build using exact scalar types. `evaluate` requires exact declared keys, exact Python integers and the documented natural witness/input restrictions. Its explicit `integer_arithmetic_only=True` option permits signed all-value circuit evaluation and makes no zero-set assertion. `canonical` returns the selected canonical witness, or the complete ray's requested nonnegative offset in existential mode. `restore_parent` accepts only natural-domain atom zeros and explicitly normalizes private quotient splitting.

The checker proves 18 exact full-source symbolic formulas/degrees and all emitted ledgers, all three acceptance graph identities, all three NAND correction identities and the parent correction. It exhausts 30,656 bounded atom assignments against an independently stated fiber predicate, checks 900 independent Boolean-block pairs, 3,600 arbitrary full-NAND tuples, 432 full large signed circuit evaluations, and all 432 small composed truth cases. It includes large negative inputs, exact-type/canonical-source guards, private-interface and domain counterexamples, and checks that every emitted gate is live. These finite checks support the elementary unbounded proofs above; they are not a substitute for them.

Run with Python and SymPy available:

```sh
python parity_truth_specialization.py \
  --parent /path/to/presburger_congruence_five.py \
  --output fresh_parity.json --expect parity_truth_specialization.json
```

The parent is authenticated before use and never executed. The helper rejects `python -O`. All writes are to the explicitly selected output, and the packet has no repository or temporary-directory dependency. This remains a bounded fixed-parity improvement and one fully specified surrounding circuit, separate from an unbounded universal equation.

The [independent full-circuit review](review_parity_truth_specialization.md) reconstructs all eighteen emitted polynomials and their live paid gates without calling this source's evaluator or verifier. Its separate enumeration checks 24,892 natural atom tuples and 10,201 signed Boolean-block pairs. Root also replayed the complete writer and matched the saved receipt byte for byte.
