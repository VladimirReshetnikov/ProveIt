# Numerical corroboration

The computations here are high-precision diagnostics, not certified error bounds and not substitutes for the proofs.

`verify.py` uses the exact recurrence

n a_n=Σ_{j=1}^n c_j a_{n−j},  c_j=Σ_{k|j} k d(k)^2 (−1)^{j/k−1},

with a_0=1, and computes all coefficients through n=3000 as arbitrary-size integers. Its first 36 terms match the independently retrieved OEIS entry. The coefficients are strictly increasing from n=1 through n=3000; global monotonicity is proved separately rather than inferred from that experiment.

For n=3000:

- a_n/A_0(n)−1 = −0.00098816677910001951644...
- a_n/A_0(n)−E_1 = −0.00000072849387638940350...
- a_n/A_0(n)−E_2 = −0.00000000127318814604387...

The data for n=100,300,1000,3000 are in `verification.json`.

The constants in the cubic Mellin polynomial are

B_1=2.9947551683590766976366327517251138636...
B_2=−2.7196023942402089668402118860410246135...
B_3=13.658493990592261163611365834114438763...

Their sizes explain very slow convergence of the bare inverse-log expansions. For example L=log(1/t) at n=3000 is only about 2.54, smaller than B_1. The asymptotic coefficient −9/4 in (E_1−1)M is therefore not numerically close at these moderate n, although the exact-cumulant correction itself is very accurate.

The observed values f(t)−P(log(1/t))/t are close to −0.086. This is not grounds for claiming that subtracting a constant creates a multiplicative equivalent at all n. The Mellin integrand has a residue −log2/8 at zero, but further continuation also encounters potential ζ-zero contributions. None of those sectors has been proved harmless at arbitrarily small t.

`verify_log_series.py` performs exact symbolic reversion in abstract constants B_1,B_2,B_3, verifies the first two displayed corrections, and outputs a third correction for each direction. It avoids fitting coefficients to integer data.
