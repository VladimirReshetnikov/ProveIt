# Uniqueness of the first Pell index in a shared scale interval

`FreeMainFirstOrdinateUnique.first_index_unique` proves in every IΣ₁ model
that two first Pell indices n,n' and ordinates k,k' are equal if they use the
same Pell base B, the same positive scale Y and value c, and

```
c=kY+eta=k'Y+eta',
0<eta<k, 0<eta'<k',
k=2*ycoord n B, k'=2*ycoord n' B, 1≤Y.
```

The strict-growth helper works even at index 0: a strict increase in index
makes the later ordinate exceed twice the earlier one. The shared narrow
scale interval rules out such a factor-two separation. This generic theorem
has not yet been applied to actual graph zeros or to a 76Y target, and it does
not establish existence or the 72-to-76 reverse implication.

Attempt02 passed with Lean exit 0, stable direct guards, no warnings or
`sorryAx`, and three expected `[propext, Classical.choice, Quot.sound]` axiom
reports. The source's unchecked-draft header predates the check. The direct
provider is the captured `ArithmeticPellPowerRecovery` object. Transitive and
dynamic ancestry and sampled resource monitoring are inherited; this is not
a source-only rebuild.

| Artifact | SHA-256 |
| --- | --- |
| `FreeMainFirstOrdinateUnique.lean` | `7650676de99166ec6927d10f1ae351e0f0d4ee0ba919314cb5d74eb97241dd27` |
| `check02.py` | `7016cdb7ed9174895ce1ab2e033ad009c27276a01257d7992e2e6ede6e0d5de7` |
| `observations/attempt02/compile.log` | `951fcd8b74c75fc55c13fd6c292925128ceeb1c09f4050165b67659a6af65272` |
| `observations/attempt02/result.json` | `a3a0dfd6435a23732fe3a0fd54bb9fa901d73251a42e75534ffe1378e9f01af7` |
| `/tmp/p64-qcube72-first-ordinate-unique-priority-check02/FreeMainFirstOrdinateUnique.olean` | `04dda4bb8fa0ee5b7d1b118a0bafc3364b68767809e3bcaa5828f819a50e23e3` |

The run used a 2,400 MiB Lean limit, 120-second timeout, sampled 3.5 GiB
process-group RSS limit, minimum 10 GiB available memory, and low CPU/I/O
priority. Attempt01 failed on an unsolved coefficient inequality and a
layout error; its source, runner, log and receipt are preserved in
`observations/attempt01/`, and the affected reports contain `sorryAx`.
