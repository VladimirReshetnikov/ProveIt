# A 66-operation rational evaluator of the current2011 degree-106 polynomial

The complete 67-operation, degree-106 integer polynomial from
`../fourteen-normalized-product106/` has an evaluator with **66 binary
operations when fixed rational constants are free leaves**. Its 14 inputs
are the same strictly positive integers, and its output is exactly the
same integer polynomial for every input. This is an evaluation tradeoff,
not a 66-operation integer-leaf Diophantine equation; it does not replace
the maintained 65-operation, degree-150 equation or its PDF.

For the fixed current2011 ports beta, K0, MC and MF (where MF is the
source-shifted high mask), the four runtime leaves are

```
beta, K0, Urank = MF / beta, Wrank = MC - MF.
```

The two derived leaves depend only on fixed ports, not on any witness.
The coherent tuple has `beta > 0` and `beta < MF < 2*beta`; the reduced
`Urank` is nonintegral. The current2011 raw integer source tuple occupies
47,313 magnitude bytes. If each of the four evaluator leaves is instead
stored separately by raw unsigned numerator/denominator magnitudes and a
signed-magnitude Wrank, the five magnitudes occupy 53,223 bytes; this
counts the denominator independently of the beta leaf and excludes sign,
framing and format overhead. Constructing and storing fixed rational
leaves is not charged by the 66-operation metric.

With `q = beta*J + 1` and `G = beta*J*(q-F)+alpha`, the five-row new rank
tail computes

```
R = (q*q-1)*(G+Urank) + J*Wrank.
```

Because `q*q-1 = beta*J*(q+1)`, substitution gives exactly the parent
rank `(q*q-1)*G + (MC+q*MF)*J`. `check.py` verifies this identity as an
exact sparse Laurent-polynomial identity, rejects an incorrect denominator,
and checks the **entire** unchanged 28-row prefix, five-versus-six-row rank
tail and unchanged 33-row suffix. All 66 rows and all 14+4 inputs are live:
37 multiplications, 16 additions and 13 subtractions. One hundred modular
full-graph evaluations are supplementary controls, not the identity proof.

The parent degree-106 certificate was reproduced in an isolated
historical-input replay under `../normalized106-historical-finite-replay/`.
The parent graph and the captured 67/106 Lean syntax were separately bound
by `../normalized106-graph-syntax-binding/`; the existing all-model/iPRA
endpoint was rechecked on its coherent historical provider in
`../normalized106-historical-endpoint-client/`. Exact polynomial equality
transfers the parent degree and external zero set, but this new 66-row
presentation has not yet received a Lean full-output binding or a new
internal iPRA sentence. No minimum or current-source rebuild is claimed.

The graph builder refuses to overwrite an existing `polynomial.json`.
The read-only checker ran with exit 0, no Lean process, and can be rerun
from the repository root:

```
python3 -I -S -B Computability/DiophantineConsistency/research/normalized106-rational66/check.py
```

| Artifact | SHA-256 |
| --- | --- |
| `build.py` | `6e3158fa8da206e677a3a4a9f9819520066bddf180a4bea54662dbe1f7c092e0` |
| `polynomial.json` | `61784a1cdc3594174c3e321712322cebdffff20be51ef7f2bc0feb3b8f9498a4` |
| `check.py` | `c4d0b01fc847fb4c76e9df90a1783baab0608355a86bbeb1d52e77e8389ae835` |
| `result.json` | `082d6634b57ed71f8c61a466a05a0dc09bf8577685a45747b4e4249ff259836a` |
| `outer-terminal.json` | `ede299f578e43719e4e673307fd95b7626a05298b8e96e717f25746ec03234f3` |
