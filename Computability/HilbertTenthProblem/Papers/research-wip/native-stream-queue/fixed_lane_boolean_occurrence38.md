# Complete fixed-lane Boolean occurrence quartics

This packet compiles one shared Boolean observation at a supplied index on a **fixed, externally certified lane**. Its best displayed source costs **114 operations, 42 multiplications and 72 additions/subtractions**, has 23 natural witnesses, and is exactly quartic. The other two complete sources cost 121 and 130 operations. These are complete polynomial counts, including affine inputs, domain checks, congruence atoms, Boolean constraints, final truth, every square and the final sum.

The lane declaration is an external premise, not a claimed turmite realization or a lane certificate emitted here. The result does not establish first-hit minimality, validate a turmite rule/background, or improve a universal Diophantine operation bound. The source is a bounded standalone CLI, with no general hostile-packet API promise. No historical or archived Python is imported or executed.

## 1. Fixed interface and occurrence predicate

The supplied external coordinate is an arbitrary signed integer `n`. Declare the lane

```
p(n)=(x,y)=(2n+1,3n−2),   time(n)=5n+2,   0≤n≤50.
```

Its position formulas are paid because the predicate consumes them. The time formula is lane metadata: there is no supplied time port or request to output time, so no unused time-production gate is emitted. Under an actual certification of this lane in the Report38 observation domain, the compiler tests occurrence at its supplied index. That certification would also have to identify the rule, tile/defects, and the valid pre-revisit time domain. This packet supplies none of those additional facts.

The four Boolean predicates are

| Atom | Coordinate predicate | Paid affine input | Modulus |
| --- | --- | --- | --- |
| A | `x+y ≡ 1` | `x+y−1 = 5n−2` | 4 |
| B | `2x−y ≡ 3` | `2x−y−3 = n+1` | 5 |
| C | `x ≡ 0` | `x = 2n+1` | 3 |
| E | `y ≡ 1` | `y−1 = 3n−3` | 7 |

Put `H=A∨B`, `K=¬H`, and let `D` mean the lane domain. The query is

```
D ∧ ((H ∧ C) ∨ (¬H ∧ E)).
```

Its explicit Boolean expansion is

```
D ∧ ((A ∧ C) ∨ (B ∧ C) ∨ (¬A ∧ ¬B ∧ E)).
```

This is the same conditional-selection pattern used in Report38's colour formula. Here its atoms are the four declared coordinate congruences. In particular, `H` is not claimed to be an actual visited-cell predicate. For this fixture the accepted indices are exactly

```
1,4,8,10,15,19,22,34,36,43,46,49.
```

The theorem below follows from the formulas, independently of this finite enumeration.

## 2. General natural-witness compiler and fair reductions

For a fixed positive modulus `d` and evaluated signed affine input `L`, use natural witnesses `(q+,q−,b,s,h)` and the five rows

```
q+q−,
L−d(q+−q−)−b(s+1),
b(s+1)+h−(d−1),
b(1−b),
(b−1)s.
```

The truth output is `1−b`, and its complement is the already supplied coordinate `b`. Relative to the pinned five-witness component, the Boolean residual is negated, which preserves its square. Compute `bs=b*s`, the remainder `bs+b`, and `1−b` once; all five rows, including this truth port, cost `4M+8A`. The same schedule is used for every congruence in every source.

Every integer `L` has exactly one natural solution of these five rows. Indeed `b∈{0,1}`, and the range equation gives remainder `r=b(s+1)` with `0≤r<d`. Euclidean division fixes `q=q+−q−` and `r`; `q+q−=0` fixes the nonnegative split. If `r=0`, then `b=s=0`; otherwise `b=1,s=r−1`. Finally `h=d−1−r`. Thus both truth and falsehood have a unique full witness tuple, including negative `L` and modulus one.

An arbitrary fixed affine inequality `L≥0` can similarly be represented by natural truth/slack `(b,s)` and rows `b(b−1)` and `L−(2b−1)s−b+1`. The unique values are `b=1,s=L` for `L≥0`, and `b=0,s=−L−1` otherwise. Boolean AND and OR gate outputs `z` can be imposed by `z−uv` and `z−u−v+uv`, respectively; NOT is the affine complement `1−u`. By induction over a fixed acyclic Boolean graph, atom truth values determine every gate output uniquely in `{0,1}`. No further Boolean row is needed for those gate outputs. Final output equal to one selects exactly the accepted inputs. With affine inputs and the computed complements, every residual remains quadratic, so the complete SOS has degree at most four. This is a general compiler proof, not an implementation or cost bound for extracting arbitrary turmite observations.

The fixture applies two reductions to **all** three schedules. Domain truth is required unconditionally, so fix both domain truth bits to one and remove their identically zero Boolean/truth rows. Only the natural slacks `lo,hi` remain, with rows

```
n−lo,   50−n−hi.
```

These are zero exactly when `0≤n≤50`, and then the slacks are uniquely `n,50−n`. No nonnegativity of the supplied external index is presumed. Also inline NOT and fix the final query value to one. The last two accepted branches are disjoint in both representations, so their final OR becomes a sum equal to one. The overlapping `AC` and `BC` terms in the DNF still require an OR.

## 3. Three complete sources and zero equivalence

All three sources share exactly the same 22 domain/atom coordinates: two domain slacks and four five-coordinate congruence tuples. They also share the same 61 paid gates producing all coordinate/affine forms and all 22 common residuals. The additional gate coordinates differ; no equality of the entire supplied witness vector is asserted.

Write `A,B,C,E` for the computed atom truth expressions and `b_A,b_B` for their existing complements. Every source first supplies a natural `K` with row `K−b_A b_B`. The additional rows are:

| Source | Other natural gate coordinates | Remaining rows |
| --- | --- | --- |
| Shared mux | `left,right` | `left−(1−K)C`, `right−KE`, `left+right−1` |
| Explicit DNF | `AC,BC,KE,joined` | `AC−AC_atom`, `BC−BC_atom`, `KE−KE_atom`, `joined−AC−BC+AC*BC`, `joined+KE−1` |
| Optimized mux | none | `C+K(E−C)−1` |

In the DNF table, the first three right-hand products mean `A*C`, `B*C`, and `K*E`, respectively; the similarly named left sides are separate supplied gate coordinates. The JSON residual arrays remove this typographical distinction by explicit producer ports.

On the atom zeros, `K=(1−A)(1−B)` is zero or one. The shared source therefore determines `left=(1−K)C` and `right=KE`; these are disjoint Boolean values. The optimized final equation is exactly their sum minus one after substitution. For the DNF, `joined=AC+BC−(AC)(BC)` is the OR of its first two clauses and is zero whenever `K=1`. Hence its last sum is the desired final OR. All additional coordinates in either longer representation are uniquely fixed, natural, and recoverable from the common atom coordinates. This proves a bijection among the natural zero fibers of the three polynomials over every signed integer `n`, and exactly one full natural zero in each representation for every accepted index. Rejected indices have no natural zero.

The Boolean expansion is deliberately not an off-zero polynomial equality. With formal scalar values `a,b,c,e`, put `k=(1−a)(1−b)`. The exact difference between the DNF expression and `c+k(e−c)` is

```
[a*c+b*c−a*b*c*c+k*e] − [c+k(e−c)] = a*b*c*(1−c).
```

The helper checks this coefficient identity. Its vanishing uses the already enforced Boolean atom `C`. The three full SOS polynomials are different; no all-integer or all-rational identity between them is claimed. Each literal source is independently verified equal to its own complete reference polynomial on all values.

Factoring the explicit DNF back into the mux recovers the optimized source. Thus the comparison is between three declared lowering schedules, not a lower bound or proof of optimality for Boolean expansion. The useful representation is the one-witness conditional formula `C+K(E−C)=1` with a paid quadratic definition of `K`.

## 4. Full paid ledger and degree

Every binary multiplication, including multiplication by a fixed modulus, costs one `M`; each addition/subtraction, including a constant shift, costs one `A`. All squares and final additions are paid. Compiler constants are fixed numerals. There is no modulus-specific constant folding. The shared coordinate/affine cone costs 11 additions: four for `x,y`, two for `L_A`, three for `L_B`, one for `L_E`, and one for `50−n`. Its two domain residuals cost two more additions. Four congruence blocks cost `16M+32A`. Thus the common 61-gate prefix is `16M+45A`.

| Complete source | Query rows before SOS | Finalizer | Complete M | Complete A | Total | Natural W | Rows |
| --- | --- | --- | --- | --- | --- | --- | --- |
| Shared mux | `3M+6A` | `26M+25A` | 45 | 76 | **121** | 25 | 26 |
| Explicit DNF | `5M+9A` | `28M+27A` | 49 | 81 | **130** | 27 | 28 |
| Optimized mux | `2M+4A` | `24M+23A` | 42 | 72 | **114** | 23 | 24 |

The optimized schedule saves `7M+9A=16` operations and four witnesses relative to the declared DNF, and `3M+4A=7` operations and two witnesses relative to the declared shared mux. These differences include the changed SOS lengths. Every emitted gate and every supplied coordinate is live in the final polynomial.

All three degrees are exactly four when `n` and the natural witnesses each have degree one. Every row has degree at most two, and the complete expanded polynomial has coefficient `+1` on `A_qp² A_qm²`. No zero-only identity is used in this degree statement. The complete polynomials have respectively 136, 153 and 124 nonzero coefficient entries.

## 5. Authenticated dependencies and bounded evidence

The helper authenticates these repository-relative source/proof files before verification. They are only read as data; the new source implements its own emitter, sparse arithmetic, canonical witnesses, and interpreter.

| Path relative to `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/` | SHA256 |
| --- | --- |
| `presburger_congruence_five.py` | `f33ba14f16009f4e825e00a91d1714696dadf34002ada3bf72fcbccc04a52cfc` |
| `presburger_congruence_five.json` | `a9bf8ced9cdc541fc918994b522b0675b961fe6acd74b6aef97e81f2723c5403` |
| `presburger_congruence_five.md` | `ee158f85fc74e1027de08433f4e4d9065c2c7b219670519047116a04aa931fa5` |
| `review_presburger_congruence_five.md` | `23e5142192d14bd98143a47a1a07a15d1d1ec115550957b0e7d42df88ac7c30e` |
| `review_turmite_first_revisit38_intake.md` | `0742f42aa92b2b9f5b292176a730550d4e58aefd512c5c4a1e6f7fdf56944b8a` |

The placed Report38 proof is `SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/periodic-turmite-first-revisits/source-packet-PROOF.md`, SHA256 `d4fa1ecec1b80d320a36ee464095c38fe671531757cc5dfcb85c3f8b62e30f12`. Its §§1–6 were read for the fixed-lane, pre-departure, interval-congruence, Boolean-indicator, and occurrence/minimality boundaries. Its implementation/testing claims are inherited, not re-established here. The current publication README/article are not dependencies.

The [new helper](fixed_lane_boolean_occurrence38.py) and [saved receipt](fixed_lane_boolean_occurrence38.json) include all three literal complete source arrays and every coefficient of their expanded polynomials. The independent direct-form reference bypasses the affine producer sharing. Verification covers all 365 live gates, 78 residual coefficient identities, three whole-polynomial identities, 413 saved coefficient entries, the formal Boolean-reduction defect, and the full 16-row atom truth table. It checks 354 signed-index canonical assignments, including two 31-digit indices in each mode; all 36 genuine accepted assignments are saved. It rejects 900 one-coordinate mutations and checks 72 complete signed/rational evaluations, including 24 rational ones. These bounded checks support the implementation; the unbounded uniqueness and zero-equivalence arguments are in §§2–3.

Reproduce after installation:

```sh
lane_repo=/absolute/path/to/Proofs
lane_wip="$lane_repo/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue"
python3 "$lane_wip/fixed_lane_boolean_occurrence38.py" --repo-root "$lane_repo" --expect "$lane_wip/fixed_lane_boolean_occurrence38.json"
python3 -O "$lane_wip/fixed_lane_boolean_occurrence38.py" --repo-root "$lane_repo" --expect "$lane_wip/fixed_lane_boolean_occurrence38.json"
```

Fresh normal and optimized-Python exact receipt replays from `/` both passed on the frozen source and receipt. This is a supplied-index component over a fixed finite lane, within the decidable observation setting. Any uniform Turing-complete loader, variable-size lane certification, first-hit minimality proof, or conversion of this variable-query construction into a fixed universal polynomial remains outside the packet.
