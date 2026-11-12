# Independent source review: auxiliary norms-to-bounds composition

**Source review passes; not elaborated.** The proposed composition's natural
main norm and c definition match the separately drafted k=2 exclusion; eta,
zeta>0 give k≥2, so the exclusion supplies k>2. Its natural first norm and
`X,Y>0` then match the proposed Pell-descent bound. The resulting
`k≥8XY²+4`, positive Y and eta, and the exact natural Delta identity match
the geometry draft, giving `c>1` and `0<Delta<c³`.

The source casts those natural inequalities and the strong norm through the
injective difference-ring embedding, while explicitly assuming the signed
bindings `Q=(ιi·ιc²)²` and `z+ιc=(ιf)²t`. These are precisely the inputs of
the proposed strong-Q and signed-gap lemmas, yielding `1<Q` and `1<z²`.
The multiplier t is a difference-ring element; the source does not assert a
natural predecessor or assume its sign. These strict conclusions are the
premises of the separately uncompiled auxiliary witness bridge.

The checker pins all three component source files and their separately
reproduced independent review receipts, checks the explicit composition
interfaces, replays the author inventory, and constructs a nonvacuous exact
integer instance of all first/main/strong and signed-binding premises. The
instance uses a finite Pell-unit power to obtain a strong witness; it does
not prove the universal model claim. No Lean process is run. Elaboration,
the actual graph's norm and signed-expression extraction, provider ancestry,
graph witness maps, and the iPRA endpoint remain unverified.

From `Computability/DiophantineConsistency`, run:

```
python3 -I -S -B reviews/ordinary14-aux-norms-to-bounds-draft-independent/check.py
```

Compare stdout with `result.json`.
