# Bounded target-free height probe (not a promoted result)

This is a read-only follow-up to the frozen endpoint projection. It does not alter that packet, introduce a maintained public compiler, or update the repository's bounds. The [small probe](three_mass_target_free_height_probe.py) authenticates the endpoint trio, reads its saved complete circuits, and emits four further trial sources in [its receipt](three_mass_target_free_height_probe.json). Independent review has not been performed.

## Literal paid delta

The endpoint source still computes its height in four additions:

```
u = n_initial + target
v = u + eta
w = v + K
h = w + T
```

All three intermediate results and `eta` are private to this chain. Replace it by

```
v = n_initial + eta
h = v + T
```

Every target producer, native comparison, clock comparison and complete nineteen-square finalizer remains paid. This deletes **two additions**, not one: the target addition and the constant-K addition both disappear. The actual trial totals are 592/467/465/468, with M/A pairs235/357,180/287,178/287,185/283. Witness counts58/56/56/56 and nineteen comparisons are unchanged. Actual degree propagation remains2344/1192/1192/1192. These are probe ledgers, not newly established published bounds.

## Changed witness relation

The new height is

\[
 h=n_0+T+\eta,\qquad \eta>0.
\]

The all-value substitution into the endpoint parent is

\[
 \eta_{endpoint}=\eta-Ky-q_h.
\]

Into the earlier coefficient-transfer parent it is

\[
 F=y,\qquad \eta_{coefficient}=\eta-n_f,
 \qquad n_f=K(y-1)+q_h.
\]

Both are signed polynomial pullbacks, with every other coordinate unchanged. Neither is an unconditional map into positive witnesses. The private-height cut plus the full retained DAG proves equality of the complete substituted polynomials.

A genuine nop outer fixture is

```
x=40, y=41, T=7880, n_initial=201, target=202,
h=8192, eta=111.
```

Its coefficient-parent slack would be−91, and its endpoint-parent slack−96. The trial fixture satisfies the three actual outer comparisons and the full joined AND with positive hats/slacks. Native Pell witnesses are not materialized. Thus a positivity-preserving same-coordinate restoration cannot simply be assumed; the proper conclusion needs separate soundness and fresh-height completeness.

## Bootstrap check

Natural `x,T` and positive `eta` give `h>=2`, `0<n_0<h`, and `0<=T<h`. The inherited proof used `h>=3` as a convenient lower bound, but its actual inequalities still hold here:

* `B=C h²` is positive and much larger than `h`, with the unchanged fixed dyadic multiplier `C>=max(4,m+1,1+max(a_s+d_s),2384m+2)`.
* All selector and quotient hats unhat to nonnegative words. The global bound excludes `J=0` as before and bounds every joined lane coefficient below `P`. The range mask `(h−1)J` is nonnegative and below `P`; all padded native inputs and prescribed scale are positive. No positivity of the target is used.
* Native typing forces dyadic `B,P,h` and `P=B^t`, with `t>=1`. Typed current/next digits lie in `[1,B)`. The exact transport equation `BN+n_0=C_w+B^t n_f` gives the whole chronological path and `n_f=last_next_digit>0` by low-digit cancellation. This does not need `n_f<h` or a prior sign assumption. In particular it still rejects `y=0`.
* The accepted path ends at first halt; its current encoded states are distinct and bounded by `mh`. Hence `t<=mh` and the unchanged tick bound gives total time at most`2384mh²<B−1`. Also `T<h<B−1`; the same clock congruence forces exact time.

Completeness can choose a dyadic `h` larger than `n_0+T` and all actual trajectory quotients. All next values then fit the unchanged radix because each is `a_s q_s+d_s` with `q_s<h`. Global slack remains positive: using disjoint selected classes,

\[
 \beta\ge(B-2h)J-g=(C h^2-2h)J-g>0,
\]

where `J>=1`, `g<=m−1`, `h>=2`, and `C>=m+1`. The clock quotient and all native witnesses can be rebuilt at the new height and scale. This gives a plausible complete proof of the same represented raw `(x,y,T)` relation, rather than an immediate-parent positive-zero bijection. The parent source's fixed-program, natural/positive domain and ordinary-input limitations remain unchanged.

## Finite evidence and boundary

The probe reads no historical Python. It checks exact private consumers, four complete source identities after the affine height substitution, all76 retained comparison operands, full liveness and ledgers,64 signed complete evaluations,21 genuine finite outer histories and four explicit `h=2,y=0` pretyping assignments. All pass. The small-height assignments are off-zero domain checks, not accepting histories.

Run:

```sh
python /tmp/three_mass_target_free_height_probe.py --root /tmp \
  --output /tmp/three_mass_target_free_height_probe.json
```

The pinned endpoint trio must be in `--root`. The receipt includes the probe's source hash and all four complete trial circuits. No endpoint author/reviewer artifact was modified, no repository edit accompanies this scout, and no new global or ordinary universal bound is claimed.
