# Exact certificate for the BB core (3,7,0)

`proof.md` gives the unbounded-population reduction and the mathematical
meaning of the five coefficient regions. It uses actual integer populations,
rank-three Rayleigh inequalities, concavity of an exact Schur complement,
and nonnegative Bernstein coefficients. It does not infer a theorem from
sampling finite populations.

The sources require Python 3 and SymPy. They read only files in this
directory and write their named JSON verification records. No producer
module, precomputed R inverse or random graph sample is imported.

Run the exact identities and five regions with:

```
python -O derive_scalar.py
python -O check_support_counts.py
python -O check_zero_overlap.py zero
python -O check_regions.py zero
python -O check_zero_overlap.py h
python -O check_regions.py g
python -O check_regions.py h
```

The last region is the longest: the initial sparse reconstruction took
about twelve minutes. Every correctness test is an explicit exception and
remains active under `python -O`. A failure is recorded as such and causes
a nonzero exit status.

`schur.txt` and `cross.json` are frozen exact rational identities, verified
against freshly reconstructed support matrices by the first command.
`check_support_counts.py` independently verifies 47 endpoint-set polynomial
identities from injective coordinate assignments and binomial population
weights. The last five commands reconstruct all region coefficients and
record canonical hashes omitting zero coefficients. No coefficient sign is
decided using floating-point arithmetic.

All five primary and independent coefficient hashes now agree, and the
separate full seven-by-seven scalar reconstruction passes. The manifest
records the completed mathematical and exact-reconstruction status.
