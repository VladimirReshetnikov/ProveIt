# Bit obstruction to a direct no-carry condition

For the [fixed-payload scalar boundary assignment](../trace74-fixed-bfs-scalar-boundary/README.md), `J=1`, `F=3`, `C=q-3` and the guard holds at equality. This exact external checker verifies the compressed/raw beta and MC payload hashes, `q=2^(67*8807)`, and `MC mod 2^67=2^67-2`. Consequently binary bit 2 is one in both `C-1=q-4` and `MC*J+1=MC+1`, so `NoCarry(C-1,MC*J+1)` fails for this scalar assignment.

This rules out the scalar assignment if that no-carry fact is proved necessary for a 74 zero. It does **not** prove that implication: the existing 75 saturation proof assumes the reverse guard. The checker evaluates no full graph output and does not establish or refute a fixed-port zero. The connection between the retained fixed payload and Lean's symbolic port remains external here.

Run `python3 -I -S -B research/trace74-fixed-bfs-nocarry-obstruction/check.py` from `Computability/DiophantineConsistency`. Script SHA-256 `60aa48d0493825856a00d34053730e0208c4aff19e74c6e4febd30d1fc0802f8`; observation SHA-256 `502788636f540fcaadbd8a4ca080afc198724eea044deb228ff1cf7334d69087`.

The [independent audit](../../reviews/trace74-fixed-bfs-nocarry-obstruction-independent/README.md) verified both payloads and the shared bit; it does not derive no-carry from a graph zero.
