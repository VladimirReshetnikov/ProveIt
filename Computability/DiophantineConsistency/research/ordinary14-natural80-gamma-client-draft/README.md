# Natural 80 gamma positivity: source-only composition

`Natural80GammaClient.lean` proposes a source-level composition from a
natural-80 own zero to positivity of its gamma coordinate. It is
**unelaborated**: no Lean build, axiom audit, iPRA derivation, PDF binding,
or physical coefficient binding has been performed. All imported graph,
partial-valuation, J-positivity, unit, guard-gap, main-pair, and narrow
gamma drafts remain unelaborated dependencies. The checker pins their source
interfaces and tests 500 finite radix/rank instances; it does not prove the
unbounded model statement.

The proposed `gamma_pos_of_80_zero` explicitly assumes representations

```
(p 0 : DiffRing V)=ι beta, (p 1 : DiffRing V)=ι K,
(p 2 : DiffRing V)=ι MC,   (p 3 : DiffRing V)=ι MF,
0<beta, 0<K, MC<beta, MF<2*beta,
```

and an 80 `InternalZero`. These are model elements of an `IΣ₁` model; no
positive-gamma premise is assumed. Applying this client at the selected
symbolic ports still requires source-proved representations and bounds for
all four ports, including strict symbolic K0 positivity.

The source proposes to obtain positive J and the shifted F, alpha, w, s,
eta, and zeta; elementary radix bounds; the 74 factor units and guard gap;
the literal main magnitude norm; a main Pell quotient; and the first Pell
norm. It then invokes the fact-level two-norm lower bound, the rank-window
theorem, the size implications, and the narrow contradiction at gamma zero.

The exact `simp`/`ring` normalization connecting the 80 main-pair
definitions to `DirectMainNorm.direct_main_orientation`, the natural
subtraction simplification `q−1=J*beta` in the rank expression, casts of
symbolic ports, and ordered-semiring power bounds are **unverified proof
obligations**, not evidence that these source tactics elaborate. Likewise,
all source-only dependencies must be individually elaborated before the
client can be used. The two `#print axioms` commands are present but have
not been executed. Semantic-to-syntactic iPRA conversion, physical bytes,
and the displayed PDF remain separate endpoint obligations.

An [independent source and mathematical review](../../reviews/ordinary14-natural80-gamma-client-independent/README.md)
checks the stated assumptions, source interfaces and algebraic rearrangements;
it does not elaborate the client or establish its model conclusion.

```
python3 -I -S -B research/ordinary14-natural80-gamma-client-draft/check_source.py > /tmp/natural80-gamma-client.json
cmp /tmp/natural80-gamma-client.json research/ordinary14-natural80-gamma-client-draft/result.json
```
