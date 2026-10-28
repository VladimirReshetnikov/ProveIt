# Internal common-unit setup and represented composition

27 October 2026. Read-only proposal for one new
`ArithmeticPellCommonUnit.lean` and focused Checks. No Lean source, private
overlay, compiler invocation or dependency refresh has been created for
this proposal. GcdNormalization is author-frozen but still provisional
pending ROOT's independent acceptance at the time of this inventory.

Use exactly these imports:

```lean
import DiophantineConsistency.ArithmeticGcdNormalization
import DiophantineConsistency.ArithmeticPellKnownUnit
```

All quantities below belong to arbitrary internal `V` with
`[ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]`. The existing represented
coordinates are `ArithmeticPellRecurrence.xcoord` and `ycoord`, with
`delta a=(a+1)*(a+3)`, so `(a+2)^2=1+delta a`. No standard-index
assumption, external fundamental unit, squarefree factorization, given gcd,
given minimality or desired-index premise is allowed at the public endpoint.

## Proposed endpoint

The additive actual norm is the primary interface, with a literal truncated
adapter as in the frozen gcd construction:

```lean
theorem common_unit_setup (a R f : V) (hR : 0<R) (hf : 0<f)
    (hn : R*R+delta a=delta a*(f*f)) :
    ∃ b e n S : V, 0<e ∧ 0<n ∧ 0<S ∧ S<a+2 ∧
      S=ycoord e b ∧ a+2=xcoord e b ∧ f=xcoord n b ∧
      delta a=delta b*S*S ∧ R=delta b*S*ycoord n b

theorem common_unit_composition (a R f : V) (hR : 0<R) (hf : 0<f)
    (hn : R*R+delta a=delta a*(f*f)) :
    ∃ b e n S : V, 0<e ∧ 0<n ∧ 0<S ∧ S<a+2 ∧
      S=ycoord e b ∧ a+2=xcoord e b ∧ f=xcoord n b ∧
      delta a=delta b*S*S ∧ R=delta b*S*ycoord n b ∧
      ∀ p : V, xcoord p a=xcoord (e*p) b ∧
        ycoord p a*S=ycoord (e*p) b
```

A truncated wrapper has premise `R*R=delta a*(f*f-1)` with the same
positive R,f. It first justifies `f*f-1+1=f*f` from `f>0`; it supplies
no additional Pell or source premise. The additive endpoint can retain
`hf` even if positivity later follows from the equation and R>0.

## Actual common-unit derivation

1. `delta a>0` and `a+2>1` follow from the polynomial parameter. Invoke
   `ArithmeticGcdNormalization.norm_normalization R (delta a) f` on the
   actual norm. Its internally derived positive factors `d,s,t` satisfy
   `delta a=d*d*s`, `R=d*s*t`, `f*f=1+s*t*t`.
2. Put `A=a+2`. The identity `A*A=1+delta a` gives the known positive
   solution `A*A=1+s*d*d`. Call
   `ArithmeticPellKnownUnit.known_unit_classification s A d` **once**.
   It derives a single base b and scale v>0, with
   `(b+2)^2=1+s*v*v`, and classifies every solution at that same b,v.
3. Apply this returned classification separately to `(A,d)` and `(f,t)`.
   It derives internal indices e,n with
   `A=xcoord e b`, `d=v*ycoord e b`, `f=xcoord n b`,
   `t=v*ycoord n b`; the existing theorem also supplies e≤d and n≤t.
   Zero indices contradict d,t>0 using `y_zero`. Thus e,n>0. Set
   `S=ycoord e b`; d>0 and d=v*S imply S>0.
4. Cancel the common additive one in `(b+2)^2=1+s*v*v` and the
   polynomial identity `(b+2)^2=1+delta b` to obtain
   `delta b=s*v*v`. Substitution and ring identities give
   `delta a=delta b*S*S` and `R=delta b*S*ycoord n b`.
   No division, square-root extraction or signed arithmetic is required.
5. `delta b≥1` follows directly from its factors. The accepted recurrence
   norm at e gives `A*A=1+delta b*S*S>S*S`; nonnegative square
   comparison yields S<A. This does not use eventual integrality,
   sequence divisibility, the large-c estimate or a source/index premise.

This replaces the squarefree/fundamental-unit setup in steps 1–4 of the
external `PellRelaxedMain.lean` theorem `Jones1980.relaxed_aux`. That
source was read as a mathematical guide only, not imported. Here the actual
norm supplies both the gcd normalization and the known positive unit.
The two indices are outputs of model-uniform bounded descent.

## Composition at every internal index

Use a reusable helper with a legitimate coordinate hypothesis, then
instantiate it with the derived e at the public endpoint:

```lean
theorem composition (a b e : V) (hA : a+2=xcoord e b) :
    ∀ p : V, xcoord p a=xcoord (e*p) b ∧
      ycoord p a*ycoord e b=ycoord (e*p) b
```

The helper does not assume the desired composition or any equation about
indices. From `hA` and `ArithmeticPellRecurrence.norm e b`, cancel the
additive one to derive `delta a=delta b*(ycoord e b)*(ycoord e b)`.
Let S denote `ycoord e b` locally. The conjunction invariant
`xcoord p a=xcoord(e*p)b ∧ ycoord p a*S=ycoord(e*p)b` is Sigma1 using
the actual represented coordinate instances and polynomial multiplication.
Use `ISigma1.sigma1_succ_induction` on p, not metatheoretic Nat induction.
The p=0 case is `x_zero/y_zero`. For the successor, use
`e*(p+1)=e*p+e` and the accepted addition formulas at `(e*p,e,b)`:

```text
x(ep+e,b) = x(ep,b)*x(e,b) + delta(b)*y(ep,b)*y(e,b)
           = (a+2)*x(p,a) + delta(a)*y(p,a)
           = x(p+1,a),
y(ep+e,b) = x(ep,b)*y(e,b) + y(ep,b)*x(e,b)
           = [x(p,a)+(a+2)*y(p,a)]*S
           = y(p+1,a)*S.
```

All equalities are addition/multiplication identities. There is no new
subtraction to justify and no cancellation by S in composition. The
structural helper needs neither e>0 nor S>0; the public actual-norm theorem
derives both. Its p=0 case remains included.

Focused Checks should retain the full setup+composition endpoint, the
literal truncated input, p=0, arbitrary internal p, the generic helper,
and the same b,e,n,S simultaneously in both coordinate formulas. Axiom
reports cover the public setup, generic composition and final wrappers.

## Source and cache pins

The actual contracts fully read for this proposal are GcdNormalization
(main201) and KnownUnit (main206), plus the complete Recurrence and
Classification sources. Main source pins:

- GcdNormalization: `488783700b1663f66b4caee71e7121eb6c50ab4efe04b39f30d63727cc6c8627`.
- KnownUnit: `c676e7c29719fbedf87aea549cefd57bee1df8844ef443a72a9d87467a9e3cb9`.
- The exact Recurrence and Classification source/object pins are inherited
  from the unchanged Classification inventory and listed in the new JSON.
- External ordinary proof guide `PellRelaxedMain.lean`:
  `8a18a6a953b8c529c35362c394e67065e943bbe17c2c22348d64d5eecbd898a4`.

The cache auditor is new and was fully read before its read-only execution.
It authenticates the full reachable header/import DAG, all selected source
and object bytes, both supplementary evidence manifests and records, and
all actual external first providers, including implicit Init. It performed
2,159 comparisons across 702 pinned paths. It writes only the inventory;
there is no overlay or compiler. The exact plan selects **99 custom modules,
95 Foundation, 384 custom artifacts, 38 boundary names and 114 total
boundary artifacts (38 primary plus 76 companion), zero refresh**.
Thus 498 artifacts would be linked/resolved for the future leaf pair.

The old 97-module Classification inventory is unchanged, SHA256
`a5182706264e4a28a0ff58f2a97cf32a2860e7246ff3c04d76a163a9e83f8f99`.
KnownUnit is added from ROOT-accepted commit eecfc7f4e2 and provider
`/tmp/arithmetic-pell-known-unit-root-rha8oka_/lib`; exact object
`efbe7eed7d2ec64cbcfbbce9e65812a489886be7ceed6f05c34aacb018c60cf8`,
ROOT packet `90388696ad3351ddf58943a02bc9557579b05fd93bd63127f6f841c77aa8c493`.
GcdNormalization is provisionally added from
`/tmp/arithmetic-gcd-normalization-author-dk1v4fv5/lib`; exact object
`517c17d6efc7aa6ef20c4f269c082252daf9c77051e402ddbbf5f085cd4ea0c7`,
author packet `a8ec6e58844265a43a250e513c31ff173ca8254097663e8542aba0f47254568b`.
Its pending ROOT acceptance must be recorded explicitly before any future
compile; the current inventory does not mislabel it as accepted. No Checks
module is a dependency. No additional Foundation or external boundary is
introduced. Existing package/trace provenance qualifications are retained.

New inventory `arithmetic-pell-common-unit-cache-plan.json` SHA256:
`7081d8c2bc515ea333aadb90fd3d6506643b09c26a5686f1f049c000438a0942`.
The proposed later two-leaf run retains pinned Lean4.32, `-M6000 -j1`,
`-DElab.async=false`, fresh regular outputs and a 512MiB reserve. No such
run is authorized by this read-only proposal itself.

## Remaining substantive gap

This completes only common-unit setup and sequence composition if proved.
It does not yield `e*p∣n`, the relaxed source index, `c∣m`, or full
Jones integrality. The later argument still needs internal sequence strong
divisibility/gcd and the growth estimate forcing index divisibility, then
the cubic-modulus expansion/cancellation. Qh signed recurrence and cofinal
witness construction remain separate. The current gcd graph provides
arithmetic infrastructure, not a sequence-gcd theorem. No final source,
polynomial, PA/HA equivalence or endpoint is claimed here.
