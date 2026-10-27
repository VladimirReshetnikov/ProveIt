# Next internal Pell checkpoint: complete first-coordinate residue classes

27 October 2026. Read-only proposal by complemented47_review. No Lean source,
compiler invocation, overlay, dependency refresh, or accepted-source edit has
been made for this checkpoint. The proposed pair is
`ArithmeticPellResidueClasses.lean` and `ArithmeticPellResidueClassesChecks.lean`,
with sole main import `DiophantineConsistency.ArithmeticPellPeriodicity`.

This is a concrete missing part of the main-index proof. It does not yet prove
the strong-norm integrality theorem, `p=R`, `2*n=R+1`, a cofinal witness theorem,
power recovery, or an equation theorem in PA or HA.

## Exact internal interface

All variables below belong to the arithmetic model, including every index,
quotient and remainder. The context is the existing
`[ORingStructure V] [V↓[ℒₒᵣ] ⊧* IΣ1]`. Write `x t=xcoord t b`,
`y t=ycoord t b`, `A=b+2`, and `delta b=(b+1)*(b+3)`. Thus `A≥2` is
derived from the natural arithmetic domain, not an extra carrier premise.
The proposed signatures, in the existing notation, are:

```lean
theorem x_residue_classes (b i j n : V)
    (hi : 0 < i) (hin : i ≤ n)
    (h : xcoord j b % xcoord n b = xcoord i b % xcoord n b) :
    j % (4*n) = i ∨ (j+i) % (4*n) = 0

theorem doubled_step_down (b m p t : V)
    (hp : 0 < p) (hpm : 2*p ≤ m)
    (h : xcoord (2*t) b % xcoord m b =
          xcoord (2*p) b % xcoord m b ∨
      (xcoord (2*t) b + xcoord (2*p) b) % xcoord m b = 0) :
    t % m = p % m ∨ (t+p) % m = 0

theorem odd_index_of_base_dvd (b j : V)
    (h : b+2 ∣ xcoord j b) : j % 2 = 1
```

The last theorem can additionally expose `∃h:V,j=2*h+1` using the actual
quotient `j/2`. The forward full-class theorem is the required endpoint;
an iff is optional only if its converse follows immediately from the same
proved periods/reflections. There is no premise asserting either output
residue, a supplied fundamental-unit classification, or a standard-natural
index surrogate. Natural remainders express both signs without introducing
an unrepresented integer sort or treating truncated subtraction as signed.

## Finite proof decomposition, including the exceptional boundary

1. Derive strict monotonicity of `x` from accepted `addition`, `one_le_x`,
   `time_le_y`, and `y_lt_x`. For an internal positive difference `d`,
   `x d>y d≥d≥1`, so the addition formula gives `x(i+d)>x i`.
   This needs no new order induction over standard naturals.
2. Derive the exact additive reflection
   `x(l+2*r)+x l=2*x(l+r)*x r`. Expand by `addition`,
   `double_x_add_one` and `double_y`; the accepted norm supplies the ring
   identity. With `m≤n`, recover
   `x(n+m)+x(n-m)=2*x n*x m`, using guarded natural subtraction.
3. The same identity with `(l,r)=(t,n)` proves the explicit antiperiod
   quotient `x(2*n+t)+x t=x n*(2*x(n+t))`. Reflection also gives
   `(x(2*n-j)+x j)%x n=0` for `j≤2*n`: use `j≤n` directly and
   otherwise swap `j` with `2*n-j`. Combining these two identities gives
   `x(4*n-j)%x n=x j%x n` for `j≤2*n`.
4. Prove the strict gap `2*x(n-1)<x n` only for `2≤n`.
   The actual recurrence is
   `x n=A*x(n-1)+delta b*y(n-1)`; its last summand is positive because
   `n-1≥1`, `time_le_y`, and `delta b≥3`. This is false at `A=2,n=1`,
   so the proof must not silently use it there.
5. Establish the local window lemma: if `0<i≤n`, `j≤2*n`, and the
   two x residues agree, then `j=i`. When both indices are below `n`,
   their residues are their positive actual x values, so monotonicity
   identifies them. Index `n` alone has residue zero in this window.
   For `n<j≤2*n`, put `r=2*n-j<n`; reflection gives the canonical
   residue `x n-x r`, strictly between zero and `x n`. If `i<n`,
   then `0<i<n` forces `n≥2`, and
   `x i+x r≤2*x(n-1)<x n` excludes equality. If `i=n`, its zero
   residue already excludes this case. Thus `n=1` never uses the gap:
   its only permitted target is `i=1`, with zero residue. The excluded
   Mathlib collision `A=2,n=1,i=0,j=2` is genuinely outside `hi`.
6. Set `j0=j%(4*n)`. Here `n>0` follows from `hi` and `hin`.
   `div_add_mod` and accepted `period_mod (j/(4*n)) n j0 b`
   reduce the arbitrary internal index to `j0<4*n`. If `j0≤2*n`,
   use the local window lemma. Otherwise reflect to `4*n-j0<2*n`.
   The resulting equalities are `j0=i` or `j0+i=4*n`, exactly the
   two proposed residue classes. All large-time work is carried by the
   already proved internal Sigma1 period induction.
7. For doubled step-down, the equality branch applies the class theorem
   at `i=2*p,j=2*t,n=m`. For the opposite-sign branch, antiperiodicity
   turns it into equality at `j=2*m+2*t`. In either case reduce first
   modulo `2*m` and then cancel the positive literal factor 2 by actual
   quotient/remainder equations to obtain the displayed output modulo m.
   The endpoint `2*p=m` is retained: both original signs are residue
   zero and the two output sign classes coincide modulo m. No strict
   inequality replaces `hpm`.
8. Apply full classes with `i=n=1` to `A∣x j`, using `x 1=A`.
   The two classes modulo 4 imply `j%2=1`. This supplies the internal
   counterpart of `SignedPellResidue.odd_index_of_base_dvd`.

The modest missing arithmetic helpers are additive cancellation of equal
remainders, canonical negative residues, and cancellation of the factor 2
after quotient identities. They must be proved inside the leaf from actual
`div_add_mod`, `mod_add`, `mod_mul`, `mod_eq_zero_iff_dvd`,
`mod_eq_self_of_lt`, and `mod_add_mul'`. No existing Foundation additive
mod-cancellation theorem was found during this audit. This is implementation
work, not a supplied assumption. The accepted period theorem avoids any
additional represented sequence or complicated induction invariant.

Focused checks should cover the `A=2,n=1,i=1` boundary, `i=n`, the signed
endpoint `2*p=m`, the odd-index consequence, and nonstandard arbitrary
internal indices. A check may exhibit the excluded `i=0` collision; it must
not weaken `hi`. Axiom audits and the usual capped fresh pair follow only
after separate implementation authorization.

## Where this enters the actual carrier dependency chain

`NativePellFirstIndex.first_index_exact` (line 16) is a final window argument:
it assumes `E∣2Q`, `R+1<E`, `n<R`, `k=2*yn_(2Q+1)(n)`, and
`k=1+R+E*h`. The actual congruence gives `2*n≡R+1 (mod E)`; the
difference lies strictly between `-E` and `E`, hence is zero. It does not
require both integers separately to be below E. Internalizing just that
arithmetic with supplied `n<R` would leave the main carrier gap untouched.

Its source wrapper derives `n<R` from the main index already being R,
base separation, and `k<c`. `NativePellBootstrap.source_first_classification`
(line 266) is the external first-norm classification now replaced locally
by accepted `ArithmeticPellFirstNorm`; its positive-parameter wrapper and
residue quotients still do not identify the first index with `(R+1)/2`.

The substantive chain for `p=R` is:

- `NativePellBootstrap.source_bootstrap_of_portBox` derives main/first
  classification and size bounds from the actual rows and port bounds.
  The internal rank window, cross-base comparison, and large-c estimates
  still need their own source-bound derivation.
- `NativePellStepDown.source_index_of_strong` (line 164) invokes
  `Jones1980.relaxed_aux` with positive i,f,p and
  `c=yn_A p`, `(i*c²)²=(A²-1)*(f²-1)`,
  `A*(A²-1)²<c`. It produces `f=xn_A m`, `c∣m`, and an exact
  ordinate relation. This is not ordinary norm classification: the proof
  in `PellRelaxedMain.lean` uses squarefree decomposition, an arbitrary
  fundamental unit, composition of Pell sequences, and gcd identities.
  None is supplied by the proposed residue-class leaf; importing that
  standard-Nat result would not internalize it.
- `NativePellStepDown.index_residues` additionally classifies the auxiliary
  norm with parameter I, proves its index odd, and uses the odd polynomial
  `Qh` at `I²≡1-A² (mod f)` and `I²≡0 (mod c)`. The exact missing
  internal counterparts of `Qh_modEq`, `Qh_eval_one_sub_sq`, and
  `Qh_eval_zero` are substantive later work. The new odd-index client
  removes only the parity step.
- Equality of squared ordinates gives equality of x coordinates at doubled
  indices. The proposed `doubled_step_down` replaces exactly the external
  `Jones1980.step_down` call, currently in `PellDoubled.lean:58`.
  Together with `c∣m` it yields the two main-index residues modulo c.
- `NativePellStepDown.eq_of_residues` uses positivity of p,R and
  `2*p<c`, `2*R<c` to conclude `p=R`. This final short argument must
  follow the derived residues; it cannot be an index premise.

After those gaps close, the first-index window yields `2*n=R+1` and oddness.
`NativePellPower.lean` then still requires the internal doubled-ratio growth
bound, the actual congruence at `4*a+3`, and strict range bounds to obtain
the exponential coordinate. Simultaneous cofinal Pell seeds and the literal
canonical converse remain separate. Nothing in this proposal substitutes a
standard index, an external fundamental-unit oracle, or desired source/rank
identities for those obligations.

## Source and cache authentication

The new read-only auditor was fully read before execution. It completed
without a compiler or overlay: **99 selected custom modules, 95 Foundation,
384 cached artifacts, 38 explicit external boundaries including Init,
114 boundary companions, zero refreshed prerequisites**. It rehashed 672
distinct paths, checked every selected current source header and exact
reachable DAG, and checked all external first artifact providers in the
accepted ordered boundary paths. Existing source/object provenance remains
the accepted package boundary; this audit is not a fresh Foundation replay.

The delta is one accepted Periodicity object added to its own 98-module
cache plan. Its source is `716f0cfe35685b2ac2351be6cb5b5aca5b32c51afa27fff1529857eeb3198819`,
object `827d160b7682437da1d2378c415125268d851119507e3211599ee0ee58c2dc7c`,
accepted at commit `b4f140c632`, provider
`/tmp/arithmetic-pell-periodicity-controller-peer-hepovkab/lib`.
FirstNorm is now accepted at `ad92d07c8a`; it is a pinned reference, not a
required import of this pair. Thus no premature unaccepted-provider selection
or unnecessary first-norm object is hidden in the closure.

The full inventory includes exact native/Jones/Mathlib reference hashes as
`references_only`, separate from selected imports. Native FirstIndex,
StepDown, Bootstrap and Power, the complete relaxed-aux proof, and relevant
doubled/odd-polynomial contracts were read. The Mathlib residue proof was
inspected as mathematics only. Root and controller independently challenged
the quarter/gap idea; controller specifically noted the n=1 gap exception
and the `2*p=m` endpoint. Neither challenge is a future Lean proof/replay.

- Auditor: `arithmetic-pell-residue-classes-cache-audit.py`, SHA256
  `f9cdd21834032ce09c5e67fdd2d1004e7d8ae553e5fe5360577fdcc29fb7b354`.
- Inventory: `arithmetic-pell-residue-classes-cache-plan.json`, SHA256
  `542ca22a1f4f3a26ea5c987ae0c4b915d7be71275c560df8405786b97846c388`.
- Audit command: `python3 research/arithmetic-pell-residue-classes-cache-audit.py`
  from the DiophantineConsistency directory; its complete stdout is retained
  in `arithmetic-pell-residue-classes-cache-audit.log`.

Any authorized implementation should preserve these providers, pin final
new sources and driver, and execute only the new main and Checks with
Lean4.32, `-M6000 -j1 -DElab.async=false`, regular fresh outputs and at least
512MiB free space. No such execution has occurred in this planning packet.
