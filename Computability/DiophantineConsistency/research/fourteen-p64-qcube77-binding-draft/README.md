# 77-to-78 unit-product graph binding

The first five theorems state that the actual generated 77 and 78 graph
expressions have the same `A1`, `M`, `W`, `Na`, and `Lt` residuals. The
`output_shape` theorem identifies the 77 output expression as
`(A1*Na−1)^2+M²+W²+Lt²`. `output_eval` proves that same formula over an
arbitrary commutative ring, with the residuals evaluated from the 78 graph.
The two full output polynomials are not generally equal. This is not a
zero-existence equivalence or iPRA endpoint.

On 2026-11-04 Lean exited 0 with seven `[propext]` axiom reports and no
warnings or `sorryAx`. A subsequent [bounded guarded replay](lean-replay.json)
also exited 0, produced exactly the same reports and a byte-identical object,
and recorded [complete output](lean-replay.log), command, and before/after
hashes of the source, Lean executable and both direct graph objects. The
[runner](check_lean.py) refuses to overwrite outputs; a repeat needs fresh
paths in a copy.

| Artifact | SHA-256 |
| --- | --- |
| `P64QCube77Binding.lean` | `f3e0fdd02ca04440ada8b7027be095cc9611f69c7e8beb63d5048c72e01d1cc5` |
| `/tmp/P64QCube77Binding.olean` | `550873ad2b0074bfb3265c1f828957b697787806cf367383ecf7d6d8b8275c3d` |
| `/tmp/P64QCube77.olean` | `daa0b689982287a74991a14c588a23d64f7bc1b5959a2528d000a6f64c0bc99d` |
| `/tmp/P64QCube78.olean` | `112e4979a76e241719cbb1b682e98c8cebabb3150c3349055dd6964ed12be0f5` |
| `check_lean.py` | `dc8ca3b44540b993d8a4876773708c70ec7863fc0f848c751c6f47c1a2e75dc0` |
| `lean-replay.json` | `cdac83a5bcb6a5ac3b6a32974ea92ab700493f9265526ecfe06cdaed738c9b57` |
| `lean-replay.log` | `0dbc5a9acca0555254d45e8ebc2133c96d0f5992d0efae3f3c8f959027455112` |

The captured provider's full project-source/object, package-transitive,
dynamic-loading and search-path ancestry remains inherited, not authenticated
by the direct input guards.
