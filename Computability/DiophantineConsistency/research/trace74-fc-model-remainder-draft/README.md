# F/C residue as a model remainder

`Trace74FCModelRemainder.mod_eq_of_signed_dvd` transfers `ι d ∣ ι x−ι y` in the model difference ring to `x%d=y%d` in the underlying arithmetic model, assuming d>0. It splits the signed quotient into positive and negative embedded model representatives, uses embedding injectivity, and applies model remainder arithmetic. The graph client applies this bridge to the audited F/C q² residue for the same first-Pell n≥3:

```
(C+MC·J+q(F+MF·J)+1) % q² = (2n) % q².
```

The graph statement retains the same positive 74 zero, beta/valuation and arithmetic-model hypotheses, and `q≥4`. It is a model remainder equality, not an individual F/C bound or reverse guard.

Reviewed retry passed in actual session 83454, outer exit 0, with both named axiom reports clean. Terminal `observations/attempt02/terminal.json` SHA-256 `f256915085d98cc98c790eb646f599170dc6c97b03a85c875194db079730b037`; object `/tmp/trace74-fc-model-remainder-psk1pwjm/lib/Trace74FCModelRemainder.olean` SHA-256 `4f8fa3d893e01f7d9627f92d1fa1b00bfdcf73511f62a4789b3608203a8e5753`. Independent [result audit](../../reviews/trace74-fc-model-remainder-result-independent/README.md) passed, SHA-256 `0d0d8c8ce42b782bcbabd4610e16ddabbe3b6daa637ec978374c6573dc7dda8d`. Direct-pin/search-path and inherited project/package/dynamic ancestry limits remain. Attempt01 was rejected for cast normalization and graph `sorryAx`; the retry corrected the cast.

[Source review](../../reviews/trace74-fc-model-remainder-source-independent/README.md), [prelaunch](../../reviews/trace74-fc-model-remainder-prelaunch-independent/README.md) and [retry review](../../reviews/trace74-fc-model-remainder-retry-independent/README.md) are separately recorded.
