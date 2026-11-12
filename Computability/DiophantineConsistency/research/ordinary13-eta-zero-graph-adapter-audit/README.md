# Eta-zero graph adapter: source and structural audit

`prototype.json` is a **structural experiment**, generated from the pinned
13-input natural 86-row graph by using `n_eta` directly wherever that graph
used `eta=n_eta+1`. It is not accompanied by a proof that eta-zero solutions
are impossible, two zero maps, a Lean graph theorem, or an iPRA endpoint. It
is not proposed as a proved smaller equation. The existing equation display
is unchanged.

The exact row substitution is checked mechanically. For every valuation of
the original graph, the prototype has the same output when its `n_eta` is the
original `n_eta+1` and all other inputs/ports are unchanged: the generator
verifies every row of that syntactic correspondence; 100 modular controls
only supplement it. This is the forward valuation correspondence, **not**
the missing converse on zeros. For a prototype zero with `n_eta=0`, the
eta-zero contradiction draft would apply only after the graph-specific
adapter obligations below have been supplied.

## Literal values and units to extract

Write all signed quantities in the model difference ring and all declared
input coordinates as model naturals. The prototype's `n_eta` is eta;
`zeta=n_zeta+1>0`, `k=eta+zeta`, `c=eta+Y*k`. Its concrete wiring gives

```
b=J*beta, q=1+b, X=q*n_w, s=n_s+1, Y=q³*s,
U=Y*q², E=X*Y, a=E+Y, H=3+4a, Delta=a²+H,
ell=E*Y*k, C=q−F−alpha, Bt=C*(X+K0)−F,
Z=b*(ell+k+r−k*Bt)−Bt,
R=(alpha+(q−F)*b)*(q²−1)+J*(MC+MF*q),
Dstar=U*(X+a*c)+H*(U*gamma+R+1−k),
I=i*c², Q=Delta*(f²−1), V=f²*(T*c−R)−c.
```

Here `J=n_J`, `r=n_r`, `gamma=n_gamma`, `f=n_f`, `y=n_y`, while
`F=n_F+1`, `alpha=n_alpha+1`, `i=n_i+1`, `T=n_T+1`. The graph's
`kbase=eta+n_zeta` is `k−1`; its subtraction is signed, not truncated model
subtraction. The graph's main carrier has **no extra `E*q` term**.

At output zero, the adapter must first prove the four factors are all `+1`
in the intended model:

```
(1 + Z²−b²*(1+ell*(ell+k)))
* (1 + Dstar²−U²*(1+Delta*c²))
* (y²−Q*(y²−V²))
* (1 + I²−Q) = 1.
```

The reviewed integer modulo-four argument provides a clear route, but the
adapter needs its own exact product-zero/units and modulo-four proof in the
model difference ring. The factors are signed; a sum-of-squares elimination
or an already-checked theorem for a different graph is not a substitute.
The resulting exact equations are first and main signed squared norms,
`I²=Q`, and `y²−Q*(y²−V²)=1`.

## Positivity, norms and rank

1. Bind beta, K0, MC and MF to the intended compact ports as represented
   model naturals, with the needed beta lower bound, `K0≥0`, `MC<beta`, and
   `MF<2*beta`. Establish the actual fixed-port facts and source/provider
   provenance separately. No port or integer-to-model cast is supplied here.
2. Derive `J>0` from the first norm at `J=0` using the still-shifted F and
   alpha and `K0≥0`. Then `q≥2`; derive `X>0` using the first and main
   norms at `X=0`, the exact `Dstar` shape, `Y≥q³`, and the signed-root
   divisibility argument. These are model-level obligations; prior
   external standard-integer proofs or a graph-90 zero wrapper do not
   automatically establish them for this graph.
3. Use the first norm with `b>0` to obtain a natural first root tau satisfying
   `tau²=1+(X*Y²)*(X*Y²+1)*k²`. Use `U>0` and the exact main signed norm
   to obtain a natural main root g satisfying `g²=1+Delta*c²`. The
   signed-magnitude, exact quotient and cast bridges must be supplied; the
   `Residue90SignedNorms` facts are source drafts at a different graph
   boundary and need an exact fact-level application.
4. Show `Bt>0` by the first norm, and hence `C>0` using `F>0` and `X+K0>0`.
   This gives `F+alpha<q` and allows the natural rank representation. With
   the port bounds, `ArithmeticAdaptiveRankWindow2011.scalar_rank_window`
   supplies its stated rank window, conditional on matching the graph rank.
   The contradiction draft also needs `R≥26`, stronger than that theorem's
   stated `R≥24`; derive it separately, for example from the positive gap,
   the retained F/alpha increments and a sufficient bound on q. Show
   `R+1<q⁴` from the stated window. All inequalities and natural
   subtraction rewrites must be justified in the model.

## Exact-index and auxiliary obligations

* Set the index theorem's `y0` to graph `s`; distinguish its existential
  first-index coefficient `s` from this graph input. Construct `n`, its
  first-Pell coordinate `2*ycoord(n,2*(X*Y²−1)+1)=k`, and
  `k=2n+4*(X*Y²)*s_index`, from the natural first norm. The model predecessor
  `X*Y²−1` is justified by `X,Y>0`.
* Prove a **graph-specific** early congruence. A possible route is to orient
  `Dstar` using the exact natural R, `U>0`, `Y≥8`, `k>0`, and the norm;
  reduce its actual balance modulo `U=q⁵*s`; and adapt the existing
  `cancel_factor_three` fact to obtain `q⁴ ∣ |k−(R+1)|`. The first-index
  equation and `q³∣Y` yield `k≡2n (mod q⁴)`, after which the rank window
  gives the draft's `mu=q⁴`, `R+1<mu`, and `(2n)%mu=R+1`. This is an
  obligation, not a proved adapter. In particular, `P72Early.early` has an
  explicit extra premise `q=3*t+2` and a different displayed carrier; it
  cannot be invoked here without proving those exact hypotheses. The
  existing `FreeJMainOrientation` graph wrapper uses another literal
  carrier containing `E*q`, so it too needs an actual fact-level adaptation.
* Classify the same main root g to produce a main index m with
  `ycoord(m,a)=c`, while retaining its norm. The corresponding actual signed
  root and index must not be silently replaced by unrelated witnesses.
* Use `I²=Q` to obtain the strong natural norm
  `(i*c²)²+Delta=Delta*f²` and prove `f>0`; obtain `i>0` from its shift.
  The eta-natural norm/geometry drafts propose `k>2`, the large-k bound,
  `c>1`, and `Delta<c³`, conditional on their explicit first/main norms.
* Apply the separate signed auxiliary bounds draft to the exact `V`, `Q`,
  strong norm and identity `V+c=f²*(T*c−R)`. It proposes `Q>1`, `V²>1`,
  and, using the direct auxiliary equation with natural y, a positive
  natural offset `u` satisfying `V+ιu=ιy`. Translate the signed equation
  into the **exact absdiff equation** in `EtaZeroIndexParity` with the
  original `T,c,R,f`; this signed-to-natural representation is an
  additional obligation. Do not assume `f>0`, `y>0`, or `u>0` before the
  corresponding derivation.

Finally instantiate the eta-zero contradiction draft with all these facts,
then build and check both graph-zero directions, domain/port association,
and the desired iPRA translation. The draft index, parity, auxiliary and
model graph interfaces are unelaborated, and none of those later steps is
established by this audit.

## Reproduction

From this directory run

```
python3 -I -S -B check.py > /tmp/eta-zero-graph-adapter.json
cmp result.json /tmp/eta-zero-graph-adapter.json
```

The checker pins the parent graph, contradiction source and selected
fact-level interfaces; confirms the exact graph edit and topological order;
and evaluates the structural shift identity at 100 modular controls. It does
not verify the displayed algebra, source theorems, model transport, or a zero
map. `--write` regenerates the inert prototype.
