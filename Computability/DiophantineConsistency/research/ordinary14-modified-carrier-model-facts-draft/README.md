# Source-only modified main-carrier model facts

`ModifiedCarrierFacts.lean` is an **unelaborated and uncompiled source proposal** toward the 84↔85 model bridge. All carrier, index and port hypotheses are explicit fact-level premises. It does not extract them from a literal graph zero, prove an endpoint, authenticate a provider route or identify external PDF/JSON/gzip bytes.

* `modified_main_parts_positive` specializes the existing internal `ArithmeticAdaptiveMainOrientation2011.main_parts_positive` to dummy q=0, eliminating its old `X*Y*q` term. It assumes positive U, Y≥8 and k>0 and makes no old-gamma or graph-zero assumption.
* `q4_from_modified_balance` derives `q⁴ | magnitude(R+1,k)` directly from the **modified** oriented natural balance, `U=q⁵*s`, q>0 and `q³|Y`. It applies the existing internal `ArithmeticAdaptiveFactorThree2011.cancel_factor_three`, including cases where 3 divides q; it does not silently insert the old `X*Y*q` term. A separate graph client must construct the natural balance and all premises.
* `modified_carrier_mod` combines that natural balance with the explicit recurrence `k=R+1+U*W` and positive U,H to get `d mod H=(X+a*c) mod H`. Its proof keeps the equality `d+H*W=X+a*c+H*gamma`; it never defines or assumes positivity of the natural difference gamma−W.
* `modified_carrier_power` proposes a fact-level application of `P72Power.power_of_mod` with all size, Pell coordinate and index hypotheses stated. It does not apply an old literal-zero wrapper. In particular, its X≥16 and index hypotheses are not consequences of the balance alone.
* `mersenne_divides_X` applies the existing internal `ArithmeticAdaptiveMersenne2011.cancel_three` to explicit Mersenne, `X=Exp.exp R` and `q|3X` premises. `compact_beta_divides_X` proposes the symbolic compact beta specialization via `CompactFixedBeta.beta_identity`; it does not prove the preceding power, divisibility or physical-byte association. Mere `q|3X` with X a power of two is insufficient without the Mersenne condition.

These source proofs, `simp`/`ring`/modular rewriting, coercions, `P72Power` interface and typeclass/provider compatibility have not been checked by Lean. The checker exercises finite balances including gamma<W and a q=3 case losing one factor of 3, plus the counterexample to unqualified cancellation. Finite controls are not model proofs or a Lean preflight.

To build the actual 84↔85 client, one must still bind the modified graph's five residuals and signed natural main pair; obtain the positive oriented main quotient; derive U=q⁵*s, the balance, the q⁴ window, and every `P72Exact.indices_ordinary` hypothesis with mu=q⁴ and i_prime=i; prove the size and Pell hypotheses used here and the graph-specific `q|3X` and X power relations. The reverse witness also needs an internal **lower bound** on the Pell projection quotient, not merely `ArithmeticPellPowerRecovery.projection_quotient`, to prove gamma-prime>w; the exact slot updates, all-positive graph equivalence, 85↔86 and other parent model clients, coherent direct/transitive source/object/Init providers, port casts, disk/resource guard, exclusive allocation and iPRA endpoint remain open.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary14-modified-carrier-model-facts-draft/check_source.py > /tmp/modified-carrier-model-source.json
cmp /tmp/modified-carrier-model-source.json research/ordinary14-modified-carrier-model-facts-draft/observation.json
```

Independent source review is recorded in
`../../reviews/ordinary14-modified-carrier-model-facts-draft-independent/`.
