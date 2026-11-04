# Fifth Pell ordinate growth

In the stated arithmetic models, `Trace74N2FifthGrowth.ordinate_five` proves

```
y₅(b) = 16(b+1)⁴+64(b+1)³+84(b+1)²+40(b+1)+5.
```

For positive X,Y, `ordinate_five_exceeds_small_k` proves `(8XY²+4)(Y+1)<y₅(Y(X+1)−1)`. This generic result is a component of the proposed n=2 exclusion; it asserts no graph-zero or iPRA conclusion.

The reviewed retry passed in actual session 28123, outer exit 0, with two clean named axiom reports. Its terminal `observations/attempt02/terminal.json` SHA-256 is `8191707c6ced991f0fa886052f4e1d56851387284f73daf45bd6bcc4de2aaf0b`; object `/tmp/trace74-n2-fifth-growth-ndmy3hdn/lib/Trace74N2FifthGrowth.olean` SHA-256 is `defa084264b6fdccc0af1130947d29cf187be6010dfb2851cf2a8ef687ff649a`. Independent [result audit](../../reviews/trace74-n2-fifth-growth-result-independent/README.md) passed, SHA-256 `019cab26aba4e1611ea36adae982ea07e4822eaa90eb8d496348f4b681135946`. Direct-pin/search-path and inherited project/package/dynamic ancestry limits remain. Attempt01 was rejected for recurrence simplifier recursion and final positivity elaboration errors; both reports contained `sorryAx`. Attempt02 used explicit recurrence stages and a positive remainder.

Independent [source review](../../reviews/trace74-n2-fifth-growth-source-independent/README.md), [prelaunch review](../../reviews/trace74-n2-fifth-growth-prelaunch-independent/README.md), and [retry review](../../reviews/trace74-n2-fifth-growth-retry-independent/README.md) are recorded separately.
