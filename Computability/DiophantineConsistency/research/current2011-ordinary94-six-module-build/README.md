# Fresh-base 67/94 six-module build

This packet records five sequential bounded source checks after the separately retained [`Carrier94Syntax` check](../current2011-ordinary67-94-syntax-fresh/README.md). The private overlay links existing fresh current14-plus-106 project files and contains copies of the six newly compiled objects. Each stage's runner pins its source, explicit direct imports and direct companion/shadow slots; it samples process-group RSS and available host memory, records the child exit and stores the actual outer session exit separately. No single all-transitive dynamic load trace or independently rebuilt base is claimed.

| Module | Actual outer session | Output SHA-256 |
| --- | ---: | --- |
| `Carrier94Syntax` | 63168 | `b0a4f82738eb22627c3631b0cfc48053b8051682fb7ed5c2b958281a7e29c76b` |
| `Carrier94Value` | 85683 | `a9c320a8e69a693aa869dbb7b272fe642e1bf76420e2602e580abbdfff52e887` |
| `ArithmeticPellResidueAux` | 84629 | `822ff3a7319d4e56cab509034489ec8a984816078630cb3d7fdb01a4df00df29` |
| `ArithmeticCarrier94Indices` | 61025 | `e61314249a1cebf8cf30f800a884ad2299eed69ec4946d42d3e23eb36264d951` |
| `ArithmeticCarrier94Soundness` | 40735 | `85330b0536024a0afa6dcb693dfc11afe8c7a9469e0a86c65bae59d8cb788bf0` |
| `ArithmeticCarrier94Extraction` | 7791 | `51fb88739bbd625ce47e33a9fca193d962f4165186eca7ad6017bcd20f1b22ac` |

All six listed outer and Lean exits were 0, and their accepted logs were empty. The first extraction attempt, outer session 9401, had Lean exit 0 but guard exit 1 due to two unused-simp warnings. It is retained in `attempt05-failed/`. The successful extraction object was built from the private source snapshot SHA-256 `415e74a23218889f43159a8e96915be93ca54446b3dd3ad69927ac492b16a83d`, not the unmodified workspace source SHA-256 `5e7ef8c7983af9a713b30a02616f00f81c3654b75574fecae944fee369c862f6`. The retained diff removes only the two warned unused simp arguments.

Each Lean invocation used `-M2800`, one worker, nice 19, idle I/O, a 120-second bound, a sampled 3.5-GiB process-group RSS stop and a 10-GiB host available-memory stop. `prepare_overlay.py` made the private overlay without overwriting base files. The first five-module runner used the live source survey; later runners use the byte-identical snapshot `survey-result-snapshot.json` SHA-256 `d923d399d157acadabe033138791583b34b52c2f992e0800b04e652bb05ce821`. The earlier fresh 106 extension's own final-client failure is distinct from its separately successful corrected client, whose provider guards are inherited.

The separate [endpoint client](../current2011-ordinary94-fresh-endpoint/README.md) imports these objects. In particular, this build alone is not the no-zero theorem or a same-valuation reverse equivalence.
