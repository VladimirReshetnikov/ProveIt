# R9 bounded-quotient obstruction: Lean-checked conditional lemma

In a discrete ordered commutative ring, `impossible_of_bounded_quotient` assumes h>0, y>0, 0<j<y, 128h<y and

`h*(4y-1)*(2052y-1)*(511y-128) = (4y*(x+1)-1)*j`.

It derives `y | j-128h`, obtains j=128h from the strict bounds, and derives `4y | 3y`, a contradiction. These are explicit arithmetic hypotheses; no graph or size condition follows from this generic theorem alone.

The controlled Lean check passed in actual outer session 14864, exit 0; terminal SHA-256 `dd4e68228db884ca4ba2a1d58fc61742724fa9857cd48dbd3a09fe2b4837b9c1`. The [independent result audit](../../reviews/trace74-r9-quotient-obstruction-result-independent/README.md) verified 35 recorded direct pins, object, log and both named reports. Full historical project/package/dynamic ancestry and ongoing search-path selection remain outside this evidence.
