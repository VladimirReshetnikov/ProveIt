# Model-natural gamma correction to the exact free-J lift

`main_lift_of_model_correction` proves in any `IΣ₁` model that the literal's
actual `Dstar` equals `U·(X+a·c+γ_old(4a+3))` in the model difference ring,
from the same-valuation bindings and model-natural equations

```
X = q·w,              η+ζ = R+1+(Yq²)·t,
γ+w = γ_old+t,        1≤q.
```

The graph's slots 5, 6, 8, 9, 11 must equal `X,Y,η,ζ,γ`, respectively. It
also assumes the **actual** graph β port obeys
`ι(J)·(β:DiffRing V)=ι(q−1)` and the actual graph `rankExpr` evaluates to
`ι(R)` at that same valuation. The proof derives the actual `U=Yq²` and
`k−R−1=(Yq²)t` identities in the difference ring and applies the checked
literal adaptive-lift identity. The β and rank bindings are assumptions, not
fixed-coefficient calibration theorems.

The theorem assumes the natural corrections and does not construct `γ` or
prove its positivity; it can consume the separate positive-gamma seed theorem
once its witnesses and graph valuation have been bound. It does not establish
the first carrier, third factor, a positive graph solution, or an iPRA proof.

Bounded author attempt 02 exited 0 in 6.309 seconds with no warning or
`sorryAx`. Source SHA-256 was
`8bd4e0799f035428846e8e189f7c338682ba7f0b42ad4d1c5c1f3e1c22fbfa93`;
object `/tmp/free-j-model-lift-binding-author-dzx6ibbe/FreeJModelLiftBinding.olean`
had SHA-256
`ae490c40293d372ef0aaed826996bdfe16dfbe338a238a54fad04325ad69ddb1`.
All three selected provider overlaps were compared byte-for-byte; 1,181 live
provider files and direct/named transitive bridge companions were unchanged.
The run is single-author and does not independently audit inherited provider,
package-transitive, or dynamic ancestry. Lean reports `propext`,
`Classical.choice` and `Quot.sound` as metatheoretic dependencies.

Attempt 01 failed locally because a natural power had not been mapped into the
difference ring. Its source and log are retained; attempt 02 fixes that map
without weakening the theorem.
