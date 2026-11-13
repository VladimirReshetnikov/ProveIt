# Negative-beta counterexample to unconditional positive `w`

The 79-operation graph can have a zero with `w=0` when beta is an arbitrary **signed** port. Thus the beta representation hypothesis in the [proposed beta-only zero-w proof](../ordinary14-natural79-beta-only-zero-w-draft/README.md) cannot simply be removed for all integer ports. This is a concrete arithmetic counterexample for a different port tuple; it says nothing about a zero at the fixed compact ports or about ZFC consistency.

Take the integer ports and 14 natural input slots, in the exact graph order, to be

```text
[beta, K0, MC, MF] = [-1, 0, 3, 0]
[n_J, n_F, n_alpha, n_f, n_i, n_T, n_w, n_s,
 n_r, n_eta, n_zeta, n_y, n_gamma, n_h]
  = [1, 0, 0, 2, 2, 0, 0, 0, 1, 0, 0, 1, 0, 1].
```

Then `n_w=0` and `q=1+1*(-1)=0`; consequently `X=Y=U=a=0`, `H=Delta=3` and `c=1`. The graph has `R=1`, `Dstar=0` and `V=-1`. Its five factors `F0`, `F1`, `Fa`, `Fs` and `guard` each equal one, so its literal output is `1*1*1*1*1-1=0`. Every input slot is nonnegative; the only violated premise is that the beta port be represented by a model-natural value. Here beta is `-1`.

The checker pins the 79 candidate JSON and Lean source, independently compares all 79 literal rows and the input/output aliases, and evaluates this vector exactly with integer arithmetic. It does not run Lean, establish a model theorem, change the equation, or assert that the arbitrary signed port example belongs to the fixed positive-beta family.

An [independent review](../../reviews/ordinary14-natural79-negative-beta-obstruction-independent/README.md)
checks the graph and natural-pair evaluations without running Lean.

From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary14-natural79-negative-beta-obstruction/check.py | cmp - Computability/DiophantineConsistency/research/ordinary14-natural79-negative-beta-obstruction/result.json
```
