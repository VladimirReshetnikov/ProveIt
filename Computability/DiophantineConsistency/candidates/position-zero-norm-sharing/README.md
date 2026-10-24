# One fewer operation in the position-zero nine-positive equations

| Whole tuple / majorant | Positive variables | Live binary operations | Exact degree |
|---|---:|---:|---:|
| original31 / simple | 9 | **419** | 1,472,168 |
| original31 / complete radical | 9 | **1,056** | 997,810 |
| compact54-sharp / simple | 9 | **427** | 1,626,248 |

Each complete JSON is one polynomial arithmetic DAG. The exact identity
`(t²-s(a+b))²-4s²ab=(t²+s(a-b))²-4sat²` saves one multiplication in
the norm tail while preserving the entire polynomial. `PROOF.md` explains
the complete prefix and degree argument. Parents and incoming ZIPs remain
unchanged. No Lean or historical native/H10 emitter is executed.

From the repository root:

```sh
python3 -B Computability/DiophantineConsistency/tools/build_position_zero_norm_sharing.py --check
python3 -O -B Computability/DiophantineConsistency/tools/build_position_zero_norm_sharing.py --check
python3 -B Computability/DiophantineConsistency/candidates/position-zero-norm-sharing/check.py
python3 -O -B Computability/DiophantineConsistency/candidates/position-zero-norm-sharing/check.py
```

The checker imports no producer or transformation code. It proves the
complete tail identity and every retained node correspondence, checks all
nodes live, and recomputes every signed fixed value from the unchanged
whole tuple. The large payloads are read directly from the pinned incoming
archive, so these commands need the repository's archive and prior tuple
files. `CHECK.json` and `CHECK_OPTIMIZED.json` retain all three rejection
controls per circuit and 60 actual-coefficient assignments per circuit.

The ordinary nine-positive source/refutation interpretation is inherited
from the accepted position-zero parents. A new Lean/internal-ZFC proof
and global minimality are not claimed.
