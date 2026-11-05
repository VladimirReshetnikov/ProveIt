# Symbolic-port ranked-main result

`FreeMainSymbolicPortRankedMain.q_lower` proves `33≤b*J+1` in an IΣ₁ model
from `b+1=exp(590069)` and `0<J`. It compares the symbolic exponential with
`exp(6)=64`; no huge natural numeral is evaluated. The `main_at_rank` theorem
then applies the checked ranked-main bridge to variable ports
`(beta,K,L,beta+H)` assuming that identity and the two inequalities
`L<beta` and `beta+H<2beta`. Its conclusion identifies the main Pell
coordinates at the graph's actual rank for any positive 72-graph zero.
Existing `CompactSymbolicMaskData.data` states the three assumptions for the
intended compact masks. Applying it to the concrete port tuple is a separate
step, not proved by this packet. Neither reverse existence nor an iPRA
endpoint is established here.

Attempt03 passed with Lean exit 0, both expected axiom reports
`[propext, Classical.choice, Quot.sound]`, no warnings or `sorryAx`, and stable
direct guards. The historical source header says “Source-only draft” but this
is the status of those exact source bytes:

| Artifact | SHA-256 |
| --- | --- |
| `FreeMainSymbolicPortRankedMain.lean` | `24b2bee0a06395d800ffd99746ddc511ea08a6545c3574986d8d415abd73709d` |
| `check03.py` | `a114656bbaea7aed2603ce8ab30dd1fd751b57974b8b90a162b19adf436c232c` |
| `observations/attempt03/compile.log` | `2b4f96a55761c3ba1e0b6a6a6aac1a024da660afbf5d9327b53ab65eaf018d52` |
| `observations/attempt03/result.json` | `2a912a0311acb1c7568d315573f588db5aa9597a0d2e073137ca93fac9fd2ce1` |
| `/tmp/p64-qcube72-symbolic-port-ranked-main-priority-check03/FreeMainSymbolicPortRankedMain.olean` | `f5676747b761614f746b9dc6861c329b17f146520f229b6838b729a4d2fc009f` |

The runner guards the source, Lean executable, and direct ranked-main bridge,
`CompactSymbolicPorts`, and `ArithmeticStandardCasts` provider objects. It
uses a 2,400 MiB Lean limit, 120-second timeout, sampled process-group RSS
limit of 3.5 GiB, minimum 10 GiB host available memory, and low CPU and I/O
priority. It inherits transitive and dynamic provider ancestry and samples
resource use; this is not a source-only rebuild.

Attempt01 failed because `linarith` did not derive the simple order chain.
Attempt02 made the chain explicit but failed on the order of addition in a
library inequality. Neither produced an object; both report `sorryAx` from
the errors. Their exact sources, runners, logs, and receipts are retained in
`observations/attempt01/` and `observations/attempt02/`.
