# Independent companion-matrix gcd computation

This check computes one finite arithmetic fact needed by the scalar
construction: for `B=590069`, `q=2^B`, `r=3056651345`,
`Y=q³`, `X=2^r`, and `c=y_r(2Y(X+1)+2)`, the gcd

```text
gcd(c,q²−1) = 1.
```

It does not evaluate the full ordinate `c`. It works modulo
`M=q²−1`, where `q³≡q` and `2^r=2^(r mod 2B)`. The code raises the
companion matrix `[[z,−1],[1,0]]` modulo `M` by ordinary binary matrix
multiplication; its lower-left entry is `y_r(z) mod M`, with
`z=2q(X+1)+2`. This algorithm is independent of the separate doubling
implementation, although both runs use the same host and GMP library.

Compile and run from the repository root:

```text
cc -O2 -Wall -Wextra -Werror -o /tmp/trace74_matrix_gcd \
  Computability/DiophantineConsistency/reviews/trace74-symbolic-pell-gcd-matrix/matrix_gcd.c -lgmp
/tmp/trace74_matrix_gcd --toy
timeout 120 /usr/bin/time -f 'elapsed_seconds=%e max_rss_kib=%M' /tmp/trace74_matrix_gcd
```

The compilation exited 0. The toy command exited 0 with
`B=7 r=77 residue_bits=14 gcd=1`; a separate exact Python recurrence
also found residue bit length 14 and gcd 1. Actual symbolic tool session
85579 exited 0 and printed
`B=590069 r=3056651345 residue_bits=1180134 gcd=1`, with elapsed 4.25 s
and maximum RSS 5600 KiB. `matrix_gcd.c` SHA-256 is
`75c8f5803f0aa072759e0dfea5d6691973a0155d9f115ec0d2d59d1b5b9c3899`;
the locally compiled binary SHA-256 was
`ccfd02a492e688f3acdebdc05f554f086be09c732db7e2d13c8e78e50fce455a`.
Compiler: Ubuntu GCC 11.4.0; GMP runtime/development packages:
`2:6.2.1+dfsg-3ubuntu1`.

This is an executable finite computation relying on the compiler and GMP,
not a Lean-kernel-checked gcd theorem or authentication of all toolchain
inputs. It does not establish a graph zero, the remaining graph factors,
external fixed-port binding, or an iPRA endpoint.
