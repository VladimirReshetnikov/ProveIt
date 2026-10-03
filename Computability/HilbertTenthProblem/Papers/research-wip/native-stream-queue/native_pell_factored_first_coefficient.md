# Prescribed AND63 and exact first-coefficient savings in unbounded clock circuits

The [complete74 factorization](complete74_factored_first_norm.md) transfers literally to the complete prescribed native AND core. Its comparison circuit becomes **63=32M+31A**, with the same 22 positive auxiliaries and 16 comparisons; its complete SOS polynomial becomes **110=48M+62A**. Applying the same identity to the existing positive-scale interface gives **63 comparison operations and 107 polynomial operations**, with its existing 21 positive auxiliaries and 15 comparisons.

The new prescribed AND63 has an explicit scale input and retains its scale comparison. It must not be confused with the earlier *unrestricted* AND63, whose checksum determines a scale that is not supplied.

The same guarded transfer also improves all four complete [unbounded three-mass clock circuits](three_mass_unbounded_interface.md). These are the actual current emitted sources, including their raw input, target, clock, height, native typing and finalizers.

| Complete source | Comparison M+A | Comparisons | Positive auxiliaries | Complete SOS M+A | Old → new polynomial cost | Degree statement |
|---|---:|---:|---:|---:|---:|---|
| Prescribed native AND |32+31=63|16|22|48+62|111→110|exactly28, inherited|
| Positive-scale prescribed AND |32+31=63|15|21|47+60|108→107|at most28|
| Three-mass increment/decrement |216+322=538|20|59|236+361|598→597|at most2344|
| Three-mass prime-three zero test |161+252=413|20|57|181+291|473→472|at most1192|
| Three-mass no-op |159+252=411|20|57|179+291|471→470|at most1192|
| Three-mass prime-three positive test |166+248=414|20|57|186+287|474→473|at most1192|

Every child is the **same entire polynomial as its own parent on all integer and rational tuples**, on exactly the same supplied coordinates. No witness projection, sign argument, or new existence theorem is needed for this saving. The four clock examples are fixed finite programs with unbounded duration; their raw input is not a universal ordinary-input decoder. There is no new universal arithmetic bound.

The standalone [emitter](native_pell_factored_first_coefficient.py) and [receipt](native_pell_factored_first_coefficient.json) contain all six complete sources and finalizers. Nine parent source, receipt and proof-note files are authenticated before their JSON is read. The historical Python modules are never imported or executed. No arithmetic power, division, or bitwise operation is an emitted gate.

## 1. Exact native identity and source guards

In every selected source, the actual paid registers are

```
X = wn2
Y = sn2
E = UM = X*Y
V = ksn2 = k*Y.
```

The names acquire the literal `native__` prefix inside the clock circuits. In every selected source k is a supplied positive auxiliary. The comparison `k=R10b=eta+zeta` remains an independent equation and must not be assumed at an off-zero tuple.

The old four-gate coefficient is

```
UM2 = E*E
scaled_norm_coefficient = UM2+X
ratio_product2 = V*V
L9 = scaled_norm_coefficient*ratio_product2.
```

Replace it by

```
factored_first_base = E*V
factored_first_next = factored_first_base+k
L9 = factored_first_base*factored_first_next.
```

Writing L=EV gives an identity over every commutative ring:

```
(E²+X)V² = X²k²Y⁴+Xk²Y² = L²+Lk = L(L+k).
```

The identity uses the literal computed equations E=XY and V=kY, not an assumption that another residual vanishes. A deliberate fixture with supplied k=3 and eta=zeta=1 makes R10b=2 and detects the false replacement of the last k by R10b.

The new emitter verifies the literal four old instructions and both defining instructions. Each removed register `UM2`, `scaled_norm_coefficient`, and `ratio_product2` has exactly its declared private consumer and appears in no comparison. The output name L9 is retained, so its original comparison with the unchanged R9 remains in place. In these native sources R9 is the paid shifted-root product `tau*(tau+1)`; it is not changed to the complete74 raw source's different root convention.

All remaining instructions and comparison pairs are retained. The complete local coefficient expansion is verified symbolically, then a shared expression-DAG proof cuts only at this established L9 identity and checks every common register, every residual and the entire final output. Topological induction proves full source equality. The replacement costs2M+1A rather than3M+1A, so exactly one multiplication disappears in each complete circuit.

This is not a public arbitrary-kernel optimizer. `rewrite(root,variant,supplied)` requires the entire exact canonical parent packet for one of the six pinned variants. No caller can present a merely similar four-gate fragment while changing its surrounding equations, input semantics or arithmetic ledger.

## 2. Domains and inherited native relation

For the prescribed raw AND interface, the four supplied arguments P,Hhat,Mhat,Zhat and all 22 auxiliaries are strictly positive integers. Its unchanged projection is

```
P = 2^ell, ell>=0,
H = Hhat−1, M = Mhat−1, Z = Zhat−1,
0<=H,M<P, Z = H AND M.
```

The parent source pays q=16P, the checksum comparison, the four-bit truth prefix and every native Pell and strong condition. All remain. In particular P=1 and H=M=Z=0 are still included by the original positive extension theorem. This packet does not materialize that theorem's large accepting Pell witnesses.

For the [positive-scale variant](native_binary_positive_scale.md), the already-proved parent change computes the old scale auxiliary from the positive bound coordinate and drops one comparison. The current step preserves that parent's supplied 21-coordinate relation exactly. It does not assert a same-coordinate identity between the two different native parent interfaces.

In all four clock forms, x,y,T are natural numbers, including zero, and every listed auxiliary is strictly positive. This mixed domain is preserved by the evaluator and by the identity. The retained positive `final_positive` coordinate and its comparison with y still rule out y=0 at complete zeros; it is not excluded from the declared natural interface by a hidden input guard.

The whole clock polynomial is unchanged. Consequently the parent's encoded-state chronology, absorbing rejecting states, exact first-halt target, dyadic height, enlarged radix, and clock no-wrap proof transfer directly. The original proof uses the actual finite-program residue map and the bound on first-halting path length to convert the paid clock congruence to exact physical time. No part of that argument is weakened to a bounded-horizon test by this rewrite.

The raw-input obstruction also remains: after hiding target and time, the source can see only the two valuations of x+1, so multiplying that positive raw mass by a cofactor coprime to6 preserves halting. The four source programs have no claimed universal ordinary-input interface. The saving does not provide the missing loader or a numerical universal reversible source.

## 3. Complete accounting and degree

All scalar binary multiplications, additions and subtractions are charged, including fixed-coefficient arithmetic. The selected comparison schedules retain exactly their old comparisons. The finalizer explicitly computes one subtraction and one square for each comparison, then accumulates the squares with e−1 additions: total `certificate+3e−1`. Both source and finalizer ledgers check that every paid gate reaches a comparison or the final output, respectively. Free-coordinate sets match the full supplied interfaces exactly, including any coordinate that appears directly in a comparison.

Every new polynomial is literally identical to its respective old polynomial, so its degree is identical as well. The standalone raw prescribed AND has the inherited exact degree28. The positive-scale and clock parents advertise only the upper bounds in the table, and this packet preserves that distinction. It independently propagates formal degrees through the emitted source and checks that the recorded upper bounds agree; it does not promote an upper bound to an exact degree claim.

This factorization does not automatically save an operation in the more economical [native norm-unit routes](native_binary_norm_units.md). Those routes already remove the L9 coefficient cone and replace the first norm by a translated-root unit factor. They no longer contain the four literal instructions proved here. Applying the present rewrite to those sources would require a separate argument and a different guarded implementation. No such improvement is claimed.

## 4. Canonical APIs and bounded evidence

`canonical_parent(root,variant)` authenticates the selected parent bundle and constructs a complete fresh packet. `build(root,variant)` constructs its child; `rewrite` validates a supplied full parent; `checked` validates a full child. `polynomial_source` returns a fresh validated source. `evaluate(...,signed=False)` checks exact integer coordinate types and the inherited mixed natural/positive domains; exact `signed=True` permits unrestricted integer algebra checks. A source-only internal evaluator is used for rational identity tests.

All canonical comparisons are recursive and type-sensitive. Public packets are rebuilt rather than held in an exposed mutable cache. Proof-only inherited metadata is explicitly stored under `parent_metadata`; its original ledgers, examples and source hashes describe the authenticated parent and are not active child register declarations. Current source, comparisons, interface, ledgers, degree records and transformation data are separate validated fields. Every reconstruction rechecks dependency bytes, and `python -O` is rejected.

The receipt gives six exact local polynomial expansions, 2,510 shared-register DAG identities, 111 residual identities and six complete polynomial identities. It includes 288 whole numeric cases (96 rational), 5,328 residual-value comparisons, 192 public integer evaluations, six wrong-k counterexamples, 2,453 malformed caller rejections, six invalid variant rejections, 18 copy checks, nine warm dependency-pin failures, and an optimized-mode rejection. Complete old/new paid ledgers and all literal sources are included. These tests supplement the exact algebraic proof; they neither materialize full native positive zeros nor rerun the previous clock semantic census.

Replay needs only the Python3 standard library and the pinned sibling artifacts:

```sh
python3 native_pell_factored_first_coefficient.py \
  --root /path/to/native-stream-queue \
  --expect /path/to/native_pell_factored_first_coefficient.json
```

`--output PATH` writes the deterministic receipt. No repository files, archived reports, historical compiler sources or existing receipts are modified by the emitter or replay.
