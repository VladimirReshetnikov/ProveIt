# Natural-input shift of the positive 74 graph: 14 inputs, 88 operations

This explicit **external straight-line program** represents the reviewed
[all-positive 74-operation graph](../ordinary14-positive-guard74/) on
nonnegative integer inputs. Its natural inputs are `n_J, n_F, n_alpha, n_f,
n_i, n_T, n_w, n_s, n_r, n_eta, n_zeta, n_y, n_gamma, n_h`. The first
fourteen gates compute each original input as `x=n_x+1`; the remaining 74 gates
are the reviewed parent rows, unchanged and in the same order. The four ports
remain `[beta,K0,MC,MF]` and the output is `out`. Every one of the 88 listed
operations, every natural input and every port is live.

For arbitrary integer ports, the candidate's output at any signed integer
assignment is exactly the parent's output after substituting `x=n_x+1` in all
fourteen inputs. The checker proves this syntactically for **every parent
gate** using exact hash-consed node identities: the shifted input node is the
literal sum of the corresponding new input and one, then the same operation
and operands are replayed. It does not rely on probabilistic hash equality or
polynomial expansion. Additional 250 signed and 250 nonnegative assignments
exercise all parent intermediate values. Restricting the new inputs to
nonnegative integers yields a bijection with the parent's positive inputs,
with inverse `n_x=x−1`; hence their zero-existence is exactly equivalent for
every fixed integer port tuple.

The 88 count is the size of this explicit program and therefore an **upper
bound** on the operation count achievable by this representation. It is not a
claim of a minimum, an independent iPRA theorem, or a proof that Lean's
`positiveShift` syntax has exactly 88 operations or preserves this sharing.
The source declaration of `positiveShift` performs the same per-variable
substitution, but a formal connection from that syntax to this JSON graph has
not been established.

## Degree at the authenticated external ports

At the P72/P115 fixed port bytes, the specialized output has exact total degree
**107** in the 14 natural inputs. A naive gate-by-gate degree bound is 111;
the checker verifies the following exact cancellation rather than treating
that loose bound as 107. Put `P=U*X+H*shift` and `B=U*a*c`. The literal rows
make `Dstar=P+B` and `Delta=H+a²`, so

```
A1 = P² + 2*P*B − U²*(1+H*c²).
```

An exact sparse-integer polynomial calculation checks that identity. The gate
degree bounds give `deg(P)≤13`, `deg(B)≤17`, and `deg(A1)≤30`. The other
factor bounds are `deg(F0)≤22`, `deg(Fa)≤30`, `deg(Fs)≤22` and
`deg(guard)≤3`, giving `deg(out)≤107`. The full graph specialized at the
actual authenticated P72 payloads and `n_i=t` has degree 107 and leading
coefficient 419359493 modulo 1,000,000,007, so its integer total degree is at
least 107. P72 raw/gzip SHA-256 hashes are checked against the P115 binding.
This external byte check is not a Lean theorem connecting the symbolic ports
to the payloads, and it does not bind a PDF or rendered equation.

Run from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary14-root74-natural-shift88/check.py | cmp - research/ordinary14-root74-natural-shift88/result.json
```

The source-only root74 `PositiveModelBridge` and its iPRA adapters remain
unelaborated; this packet does not assert Lean provider compatibility, an
established consistency equivalence, an all-integer zero equivalence, or
global optimality.

Independent external review: [natural shift 88](../../reviews/ordinary14-root74-natural-shift88-independent/README.md).
