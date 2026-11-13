# Concrete CRT certificate assessment

The six difference-ring Bézout assumptions in
[`Trace74CRTNaturalTuple.exists_updated_carrier`](../trace74-crt-natural-tuple/Trace74CRTNaturalTuple.lean)
have **not** been proved in Lean for the symbolic candidate. For the
[scalar candidate and its exact parameter definitions](../trace74-symbolic-carrier-crt/README.md),
write `B=590069`, `r=3056651345`, `q=2^B`, `h=q−1`, `U=q²−1`,
`X=2^r`, `Y=q³`, `D=XY`, `W=K0+X/q`, and `c` for the main Pell
ordinate. The certificates are pairwise coprimality of `D,c,h`, plus
coprimality of `U` with each of `D,c` and of `W` with `h`.

Two arithmetic checks are the expensive substantive inputs:

* `gcd(c,U)=1` is computed by the external
  [`pell-gcd.c`](../trace74-symbolic-pell-projection-obstruction/pell-gcd.c)
  using a modular Pell doubling recurrence. `U=2^1180138−1` has
  1,180,138 bits, or 147,518 bytes when packed. The computed ordinate
  residue has 1,180,134 bits, and its gcd with `U` is 1. The program does
  not materialize the ordinate. With this index and base, the ordinate
  has on the order of `9.35×10^18` bits; evaluating it as a numeral is
  not a practical Lean strategy.
* `gcd(W,h)=1` is checked by
  [`check.py`](../trace74-symbolic-carrier-crt/check.py), reducing `X/q`
  modulo `h` to `2^93925`. The hash-pinned external `K0` payload has
  592,884 significant bits, or 74,111 packed bytes; `h` has 590,069 bits,
  or 73,759 packed bytes. Binding that external payload to the Lean graph
  port remains a separate proof obligation.

The other four certificates have structural reductions: `D` is a power
of two, `h` and `U` are odd, and the Pell ordinate is odd at this odd
index. Also `h ∣ U`, so the `c,h` coprimality follows from `c,U`
coprimality. These reductions, parity at the specific index, and transfer
of natural gcd certificates to the model difference ring still need
Lean proofs. The structural facts rely on the candidate's power and
Pell-coordinate bindings, not on the CRT construction alone. The
separately computed `gcd(H,hD)` is not needed for the sufficient carrier
divisibility theorem.

The 2026-11-04 external checks were:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/trace74-symbolic-carrier-crt/check.py
gcc -O2 -Wall -Wextra Computability/DiophantineConsistency/research/trace74-symbolic-pell-projection-obstruction/pell-gcd.c -lgmp -o /tmp/trace74-crt-pell-gcd
/tmp/trace74-crt-pell-gcd
```

Both exited 0; the latter reported `residue_bits=1180134 gcd=1`. These
GMP/Python computations are evidence only, not Lean certificates, and
they do not prove an actual graph zero or any iPRA endpoint.

The local [`ArithmeticPellRecurrence.addition`](../../Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean)
and [`ArithmeticPellPeriodicity.double_x` / `double_y`](../../Lean/DiophantineConsistency/ArithmeticPellPeriodicity.lean)
already hold at arbitrary internal indices. A verified binary modular
checker can use those formulas and modular-reduction lemmas to verify
the 32-bit index without materializing the ordinate. The checker must
still bridge the actual base to its residue, verify the final finite gcd
or Bézout certificate in Lean, and avoid silently trusting an external
computation. Whether the resulting million-bit kernel checks fit the
available resource limits is not yet established.

## Bounded certificate experiment

A concrete next experiment is to generate a deterministic trace of the
32 modular coordinate pairs and signed Bézout coefficients, treating all
generated values as untrusted candidates. A Lean checker would verify
every transition and the final identity in the kernel, retaining source
and trace hashes, diagnostics, and the axiom report. An external GMP
result or `native_decide` should not be presented as a kernel-reduced
proof of this certificate.

Start with scaled examples such as `B=17,257,4097`, each in an isolated
run capped at 30 seconds and 2 GB. Increase scale or limits only after
examining results; these scaled examples do not establish the actual
candidate. At the real modulus size, 32 pairs of reduced coordinates
occupy at most 9,441,152 packed bytes, excluding coefficients and
metadata. Lean's numeral encodings, proof terms and kernel computation
may use substantially more; full-size feasibility is unknown. No
full-size Lean evaluation has been launched under this plan.

The finite standard certificate must also be transferred to the
represented model computation, with proofs of the actual symbolic q,
modulus, power and Pell-base bindings. These obligations, the separate
external payload binding, and the `gcd(W,h)=1` certificate remain open.

The [scaled runs](../trace74-scaled-kernel-certificate/README.md) passed for
`B=17,257,4097`. A [separate B=65537 attempt](../trace74-next-scale-kernel-certificate/README.md)
timed out after 30 seconds without a completed theorem, while four
[isolated declarations](../trace74-next-scale-transition-bench/README.md)
from that same certificate passed individually. This does not identify
why the combined check timed out, verify its other 29 transitions or their
chain, or establish feasibility at the full candidate modulus.
