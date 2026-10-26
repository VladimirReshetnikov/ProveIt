# Two additional semantic simplifications

Snapshot: `f00ba53b331833c6cb64707bd90e48489e5610f5`, 26 October 2026.
Both candidates were checked against the prior-proposal corpus by the independent novelty-audit agent. The beta result is the main recommendation. The internal-division result is a smaller cleanup with a useful mathematical boundary.

## 1. The first port's positivity follows from the positive source

### New conclusion

Let `J = (x 0 : Int)`, `beta = ports 0`, `L = (x 24 : Int)`, and `N = (x 16 : Int)`. The first two source rows, already decoded by earlier proposal b, give

- `q = 1 + J * beta`;
- `L = q^2 - 1`;
- `N = q * (1 + L)`.

Assume only `L > 0`, while `J >= 0` and `N >= 0` follow from the natural-coordinate types. Since `1+L > 0`, the second equation forces `q >= 0`. The first equation and integral discreteness exclude `q=0` and `q=1`, so `q >= 2`. Therefore `J*beta=q-1>0`; together with `J>=0`, this forces both `J>0` and `beta>0`. The same equations give `L>=3` and `N>=8`.

The concrete checked theorem is:

```lean
source_port_guard (ports : Fin 4 → ℤ) (x : Fin 31 → ℕ)
  (hL : 0 < x 24)
  (hs : ∀ k, SplitCertificate59.sourceRows ports
    (fun i => (x i : ℤ)) k = 0) :
  0 < x 0 ∧ 0 < ports 0 ∧ 8 ≤ x 16
```

Thus even positivity of `x 0` and `x 16` need not be independent premises for this result. A second checked client derives `2 ≤ x 16 * x 9` using only `hL`, `0 < x 9`, and the source rows.

### Existing proof sites

`NativePellBootstrap.lean`:

- `source_Y_ge_two` (line 95);
- `source_rank_half_lt` (119);
- `source_main_and_half_bounds` (141);
- `source_base_separation` (348);
- `source_bootstrap` (366).

Each currently accepts an independent `hβ : 0 < ports 0`. Their relevant source hypotheses already imply it. The external calls needing argument updates are in `NativePellFirstIndex.lean:59` and `NativePellBootstrap.lean:593`; internal calls occur at lines 124, 148, 352, 374, and 398. `beta_call_sites.txt` records all observed named uses, including axiom checks.

A low-risk adoption path is to add the weaker `source_Y_ge_two_no_beta`, make the existing public theorem a compatibility wrapper, and migrate callers separately. A subsequent cleanup can remove `hβ` from the five signatures. No full downstream signature migration is claimed in this packet. Other `PortBox` bounds remain needed for their own arguments; this result does not remove the complete `PortBox` premise.

### Why this is new relative to the assumed baseline

Packet b, `report.tex:617–641`, already proposes the scale-coordinate decoder. That decoder is assumed available here and earns no new savings credit. Packet f, `report/sections/03_architecture.tex:92–98`, derives `PortBounds.beta_pos` from a separate lower-bound assumption. The new deduction obtains beta positivity **from the source rows and the natural-coordinate domain**, making an independent positivity guard redundant. It remains useful after those earlier APIs are applied.

### Scope, limits, and tests

`SourceGuardRecovery.lean` contains two fully checked generic integer lemmas. `SourceGuardClient.lean` contains two fully checked clients of the literal production `SplitCertificate59.sourceRows` definition. The concrete compilation used an existing production cache; the entire `SplitCertificate59.lean` source was checked byte-identical against the current snapshot (SHA-256 `0b6082b0af3f092f6914263eb1568da1d3730df24032b6c1dff5489875da0a03`). This is a fresh client elaboration, not a clean rebuild of the whole project import closure. All four endpoints have exactly the standard axiom set `propext`, `Classical.choice`, `Quot.sound`.

The integer domain matters. Over rational coordinates, `q` may lie strictly between 1 and 2, so `N>=8` need not follow. The generic sign premises are sharp in the following sense:

| Omitted premise | J | beta | L | N | What fails |
|---|---:|---:|---:|---:|---|
| `L>0` | 1 | 0 | 0 | 1 | beta positivity, q>=2, N>=8 |
| `N>=0` | 1 | -3 | 3 | -8 | beta positivity, q>=2 |
| `J>=0` | -1 | -1 | 3 | 8 | beta positivity and J positivity |

All rows satisfy the two scale equations. The equality case `J=beta=1,L=3,N=8` proves sharpness of the abstract two-row bound, not existence of a solution to the complete source system.

## 2. Internal division: separate quotient intervals

### Exact residual problem

`ObjectDivision.quotient_not_lt` works over arbitrary model naturals `Natural H`, including nonstandard values. It currently introduces both a quotient-gap witness `q'=q+s+1` and a remainder-gap witness `d=r+t+1`, then builds a concrete witness for `n<n` using a polynomial identity.

Only the first gap is needed. From `q'=q+s+1`, the existing internal additive-order equivalence proves

`q*d+d <= q'*d`,

with gap `s*d`. Since `r<d`, additive strict monotonicity gives

`q*d+r < q*d+d <= q'*d <= q'*d+r'`.

The two representations of `n` then contradict this strict inequality. This removes the second successor decomposition and the explicit witness for `n<n`. It requires neither a global ordered-multiplication instance nor external well-foundedness. `DivisionInterval.lean` checks this mechanism over an arbitrary commutative semiring equipped with a linear additive order and the displayed additive-gap/discrete-order laws.

### Why it is not a repeated host-natural division proposal

Packet k already applies `Nat.div_mod_unique` to host naturals and proves certificate-witness uniqueness. Its `certificates/README.md:60–62` expressly excludes replacing `ObjectDivision` with that theorem, because model naturals need not be standard. The present proof applies inside every `Natural H` using the existing internal order facts. Packet zf's object-arithmetic patch leaves this theorem unchanged.

### After all earlier proposals are assumed applied

Packet x supplies the ordered-semiring laws, and zf supplies the successor-bound interface. Under the user's requested baseline, the remaining quotient-gap witness can also be removed: `q<q'` gives `q+1<=q'`; multiplication by nonnegative `d` gives `(q+1)*d<=q'*d`. Rewriting `add_mul` and `one_mul` starts the same interval sandwich. `quotient_not_lt_ordered` checks this version abstractly. Its order/discreteness prerequisites are assumed-applied earlier work, not newly credited innovations. The only new operation is using them to replace the untouched internal division-uniqueness witness argument.

### Adoption and magnitude

`ObjectDivision-interval.patch` is a candidate replacement confined to this private theorem. It adds no production helper and preserves all public theorem signatures. The corresponding arbitrary-semiring proof skeleton is kernel checked. The full `ObjectDivision` module and its downstream clients were not rebuilt. The source reduction is small; its principal benefit is an ordinary interval argument with fewer manufactured witnesses. Do not describe the standalone explanatory kernel as free helper code or claim a large net LOC gain.

No conclusion here identifies `Natural H` with external Nat, equips it with an externally well-founded order, or extends internal induction to arbitrary external predicates.

## Artifacts

- `SourceGuardRecovery.lean`, `SourceGuardClient.lean`: main new core and literal source clients.
- `DivisionInterval.lean`: generic ordered-semiring validation of the internal argument.
- `ObjectDivision-interval.patch`, `ObjectDivision.candidate.lean`: candidate production replacement; integration build not performed.
- `beta_call_sites.txt`: observed migration surface.
- `kernel-validation.json`, `client-validation.json`, corresponding `.log` files: exact scopes, hashes, commands, exits.
- `division-patch-status.json`: local source counts and integration status.

Generated `.olean` objects are local build products and need not be shipped.
