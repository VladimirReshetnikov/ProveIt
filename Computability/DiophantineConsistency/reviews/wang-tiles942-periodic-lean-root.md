# Exact marked-word geometry on the actual Wang table

Date: 2026-10-26. Independent complete source/check review and fresh replay:
ROOT. See the [author receipt](wang-tiles942-periodic-author.md).

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| WangTiles942Periodic.lean (128 lines) | b426e06571ddc25095a0573784d2f289f116cb976468f826da128a4bb9713d53 |
| WangTiles942PeriodicChecks.lean (68 lines) | c8c5ffdd60b4510a573012a3e3688cc1bc80676733c813ec7a0888db6b75e7f6 |

ROOT read both complete sources before fresh direct `lake env lean
-M6000 -j1` executions. Main output was a separate temporary object;
checks imported the frozen author-built object. Both passed; the main
log is empty and all eleven theorem-axiom audits are standard-only.
No full ancestor or umbrella rebuild is claimed.

MarkedWord N s a has exactly three fields: a0=0, East(i)=West(i-1),
South(i)=North(i-s), with the actual942-index table and arbitrary integer
shift s. There is no run, unique-Start, rectangle, reduced-shift,
divisibility or coprimality premise, and this module does not assert such
a word exists.

The pullback uses the full signed address cast(-x-s*t) in ZModN. Its
matching is west(x+1,t)=east(x,t), north(x,t+1)=south(x,t). The origin
is the literal Start and every tile belongs to the exact Allowed families.
The independent periods(N,0),(0,N) and the additional period(-s,1) are
identities of this same pullback for every s, without least-period claims.
Focused checks distinguish both subtraction signs from addition and use
negative shifts/coordinates as well as a noncoprime unreduced shift14
at modulus6.

This closes the generic periodic geometry step. Producing the marked word
from original polynomial Facts and proving the actual tiling/machine
language equivalence remain separate obligations. The maintained decimal
page and equation metrics are unchanged.
