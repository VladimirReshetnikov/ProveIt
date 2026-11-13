# Independent review: eta-natural strong/auxiliary adapter

The adapter's fact-level equations, strict-bound premises, positive-offset
interface and absdiff target agree with the pinned source declarations. No
hidden positive-eta premise or arithmetic mismatch was found. These are
unelaborated source interfaces: this review does not prove the relevant
model embeddings, extract a graph zero, build providers, or establish an
iPRA endpoint.

The strong bridge starts with the signed equality
`(ι(c²*i))²=ιDelta*((ιf)²−1)` and uses injectivity of the model embedding
to obtain `(i*c²)²+Delta=Delta*f²`. With the separately stated `Delta>0`,
that natural identity rules out `f=0`. The strict-bounds theorem assumes
`c>1`, `i≥1`, `0<Delta<c³`, and this exact natural strong identity. It
sets `A=f²*(T*c)`, `B=f²*R+c`, `z=ιA−ιB`, and
`Q=ιDelta*((ιf)²−1)`. The signed identities `z+ιc=f²*(T*c−R)` and
`Q=(ιi*ιc²)²` match the pinned `aux_strict_bounds` interface. That
interface proposes `Q>1` and `z²>1`; neither is assumed by this strict-bound
theorem. Its natural c, i, Delta, f, T and R and all their graph bindings
remain explicit inputs.

The offset theorem independently requires `f>0`, `Q>1`, `z²>1`, and the
exact signed direct auxiliary equation. It does not assume positive natural
y or u. The pinned offset source proposes a positive natural u with
`z+ιu=ιy`, from the same signed z and Q. Consequently
`ι(A+u)−ιB=ιy`. The two cited `P72Root.ι_magnitude_sq` instances turn the
squares of these signed differences into the corresponding natural
`absdiff` squares; the pinned `absdiff` is `(A−B)+(B−A)` in model-natural
truncated subtraction. The separately derived `1≤f²` justifies the
`ι_tsub` rewrite needed to represent `Delta*(f²−1)`. Reflecting the signed
auxiliary equation then gives exactly the index target's two absdiff
arguments. To instantiate that target, a client must additionally prove
`Delta=(3+4a)+a²` and bind the same c, f, T and natural R to its graph;
the target does not follow from a signed rank with no natural representation.

Neither adapter theorem mentions eta. The separately pinned large-k and
geometry drafts allow eta zero under their own explicit first/main norm and
positive-zeta assumptions; this packet neither proves nor invokes those
conditions from a graph zero. Natural and signed casts, common witnesses,
first/main Pell indices, rank bounds, provider closure and zero maps remain
separate.

From this directory reproduce the independent receipt with

```
python3 -I -S -B check.py > /tmp/eta-strong-aux-independent.json
cmp result.json /tmp/eta-strong-aux-independent.json
```

The checker pins the adapter and its key interfaces and performs 1,600
bounded strong-gap and 40 direct-unit positive-offset controls. The finite
controls are not an all-model proof and do not validate Lean tactics. No
reviewed source was modified.
