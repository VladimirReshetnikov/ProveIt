# Independent review of the fixed-main auxiliary exclusion

The [auxiliary-exclusion argument](../../research/p64-qcube72-partial-aux-exclusion/README.md) is a valid source-level specialization, over the standard natural numbers, of the displayed `signed_half_index_of_facts` interface. It rules out **all positive `f,i,T,y`** satisfying both `W=0` and `Na=1` for the particular fixed main Pell data `a=189`, `c=ycoord 4020619 a`, `g`, and `R=41`. No new Lean specialization or compiled client was run. Existing provider ancestry is not newly authenticated by this review.

The theorem's inputs are instantiated as follows:

- Its `a,c,d,m` are the fixed `189,c,g,4020619`, and `delta a=(a+1)(a+3)=36480`. The referenced `xcoord/ycoord` successor equations are precisely multiplication of pairs by `(191,1)` for that discriminant, so the displayed Pell power supplies `ycoord m a=c` and `g²=1+delta a*c²`.
- Its `rp,rn` are `41,0`, giving `absdiff rp rn=41`. The certified interval `c>27k` and first Pell recurrence `k≥2·2446738` give `2·41<c`. All required `c,i,f,m,y` positivity hypotheses are present; the theorem does not require a sign choice for the auxiliary expression.
- For the large-c hypothesis, `m>6` and the positive Pell recurrence make `ycoord m a≥ycoord 6 a`; the separately stated sixth-coordinate identity gives `ycoord 6 a=32(a+2)delta²+32(a+2)delta+6(a+2)>(a+2)delta²`.
- With `I=i*c²`, `W=0` gives the theorem's natural equality `I²+delta=delta*f²`. The signed graph expression is `V=f²(Tc−R)−c`; the theorem's `z=absdiff(f²(Tc+0), f²R+c)` is `|V|`. Consequently `Na=1` together with `W=0` rearranges exactly to `I²z²+y²=1+I²y²`, for either sign of `V`.

The theorem would therefore give `4020619=absdiff 41 0=41`, a contradiction. This excludes completing that **fixed partial tuple** by changing only `f,i,T,y`; it does not exclude other main coordinates or rank, an actual compact44 zero, an alternative existence equivalence, or establish an iPRA endpoint.

The [checker](check.py) pins the author packet and exact theorem, recurrence, sixth-coordinate and `absdiff` sources; reproduces the bounded author controls; independently computes the sixth Pell coefficient and numerical inequalities; and checks 700 finite signed-square identities covering both signs. The finite cases are controls for the algebra, not a replacement for the theorem or a new kernel-checked proof of this specialization.

```
python3 -I -S -B path/to/p64-qcube72-partial-aux-exclusion-independent/check.py
```

The deterministic result is frozen in `result.json`.
