# Internal square divisibility: independent replay

29 October 2026. I read the complete proof and checks and the executed driver,
verified all 35 author evidence files, and independently rebuilt the current
gcd prerequisite and both new leaves. All three source, object and complete
log hashes match; the axiom report uses only `propext`, `Classical.choice`,
and `Quot.sound`. The existing Foundation and package providers were reused,
not fully rebuilt. The [root replay](arithmetic-square-divisibility-root-replay/)
and [author receipt](arithmetic-square-divisibility-author.md) retain the
provider inventory, logs, timings and earlier failure.

For arbitrary elements of any IΣ1 model, `0 < m` and `m*m ∣ z*z` imply
`m ∣ z`, including `z = 0`. The proof uses an internal Bézout gcd certificate,
cancels its positive square, and derives that the normalized scale is one;
it assumes neither standardness nor prime factorization. Application to the
adaptive Pell equations is a separate client.
