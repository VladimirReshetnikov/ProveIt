# Trace75 first Pell classification

`Trace75Pell.first_and_doubled` is checked in every `IΣ₁` model for arbitrary
natural ports with beta positive and a positive witness valuation whose
trace75 ring value is zero. With the **unscaled** first parameter
`P = X*(Y*Y)`, it derives positive `tau,f0,n,I`, `n≤k`, the two graph
radical roots, and

```
xcoord n (2*(P-1)+1) = tau,
2*ycoord n (2*(P-1)+1) = k,
I = 2*U*tau*f0,  (1+2*Delta*U²*E)² = 1+Delta*I²,
Delta*(4*a*(1+a)) = (Delta*I)²,  c² ∣ I,
```
where `a = Delta*U²*E`. It does not show `n≥2`, connect this first index
to the separately recovered odd main index, prove machine halting, or give an
iPRA theorem. The retained JSON and fixed payload remain externally bound.

Accepted source `Trace75Pell.lean` SHA-256
`12f96bfb5569590729f55f1cfca03d9a7d6a848062fcc517363caf6cc720572f`;
`run-pell.py` accepted `observations/pell-attempt01/`, object
`/tmp/trace75-pell-79kzmzfi/Trace75Pell.olean` SHA-256
`cea9dcd9cc72467aa28113a65178cb7763170960ef0a4b215153537fb77bfbb9`.
`#print axioms` reports `[propext, Classical.choice, Quot.sound]`.
Selected direct providers are pinned; project and package transitive,
historical source/object and dynamic ancestry remain inherited.
