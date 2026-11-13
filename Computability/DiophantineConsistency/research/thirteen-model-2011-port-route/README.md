# A distinct 2011-port instance of the thirteen-coordinate graph

This is a proposal, not a checked equation or a completed proof. The existing
69-gate research graph binds the full phase-split2471 tuple; replacing its four
ports by the fixed `CurrentWindowCarry2011.ports` creates a **different**
equation. Its literal, all four complete coefficient values, 69-operation
schedule and exact degree must be constructed and checked separately. No
calibration theorem for the 2471 tuple follows from this route.

## Exact 2011 data already available

* `CurrentMasks2011.radix=2^47`, `width=47*2011=94517`,
  `beta=radix^2011-1=2^94517-1`, and `lowPort`, `highPort` are fixed by
  `CurrentMaskData2011.lean`. The actual port ordering is
  `![beta,K,lowPort,highPort+beta]`, with K supplied by the exact
  `CurrentWindowCarry2011.ports`; the high port is already shifted once.
* `ArithmeticRankForcing2011.lowPort_four_nat` proves
  `CurrentMasks2011.lowPort % 4 = 2`; `lowPort_mod_four` transports that
  statement to every `IΣ₁` model. `ArithmeticCarrierSoundness2011.current_bounds`
  supplies the model inequalities beta>=15, lowPort<beta and
  highPort+beta<2*beta; `ModelCarrierCurrent.beta_pos` provides the positive
  port in the ring of differences. These do not alone establish all the
  original standard-ℤ `NativeSourceMask.Interface` fields or the desired
  model converse.
* `ModelCarrierCurrent.evalRing_expressionAt65` identifies the maintained
  14-variable current expression with `Carrier65.value` in any commutative
  ring. `ModelCarrierCurrent.currentBridge` supplies the existing 2011
  all-model no-zero/checker bridge for the positive-shifted 14-variable
  expression. It is tied to the 2011 tuple and its own replay provenance.

## Sufficient but currently unproved all-model criterion

Build an `Expr (Fin 13)` whose ring evaluation is exactly
`ThirteenCarrier.value69` at the 2011 ports, and prove in every `IΣ₁` model
that there exists a positive 13-coordinate zero iff there exists a positive
14-coordinate `Carrier65.value` zero at those same four ports. The two
witness directions may change all coordinates; a same-valuation theorem is
neither available nor required. For the 13-to-14 direction,
`ModelThirteenRestoration.restores_positive_zero69` is an available generic
ordered-ring restoration with its signed-residue, positivity, and positive
beta hypotheses; `modelSignedResidue` specializes the residue to model
difference rings. Its expression binding, positivity extraction back to
model naturals, and source-current coherent replay still need checking.

For the 14-to-13 direction, prove the model analogues of
`ThirteenCarrierComplete.outer_facts` and its fresh private-seed composition.
The former must extract the actual model rank R, prove `R%4=3` and
`c=ycoord R a`, and prove the retained transport G is positive and divisible
by `b=beta*J`. It is not valid to use `Int.toNat` or standard-ℤ Pell
classification on arbitrary model elements. In particular, the original
`NativeSourceMask.Interface` is a standard-natural interface, not an
arbitrary-model proof.

The model seed components now have paired but separately qualified evidence:
`ModelBSeed.strong_seed_with_multiplier` supplies the b*c² ordinate in every
model for b,c>0; `ModelBAuxiliary.auxiliary_seed_with_multiplier` constructs
f,i,T,u,y given b>0 and R%4=3. A signed ordinate residue and a proof that
its m-coordinate is positive must still be composed with the retained
carrier facts. `ModelThirteenRestoration`'s generic `auxiliary_estimates`
and `affine_carrier_pos` may apply after all its difference-ring and sign
hypotheses are supplied. Existing ordinary-ℤ completeness is not an
all-model theorem.

Once the existence equivalence and both exact expression-to-ring bindings
are actually proved, the single positive-domain shifts and model-natural
representatives must be handled explicitly. Then
`HAExpressionNoZeroEquiv.bridge` transports the 14-variable
`PolynomialBridge` across different arities, and
`IPRAExpressionNative.equivalence_of_bridge` yields the selected native iPRA
equivalence. The standard presentation follows from
`IPRAStandardTheory.provable_iff`. This is a conditional proof route, not an
assertion that these hypotheses have been discharged.

## Concrete rank-phase route to investigate

For a positive zero of the actual 2011 14-variable expression,
`ArithmeticCarrierSoundness2011.current_equations` provides five scalar
equations; `ArithmeticPellFirstIndex.maintained_first_indices`, applied with
`current_bounds` and the positive coordinates, gives `c=ycoord R a`, `R>0`
and size facts using the parent’s existing strong/auxiliary factors. These
parent hypotheses are present in the input zero; using them here is not the
circular act of assuming the *new* private seed to construct itself.

`ArithmeticHalfBinomial2011.current_population_lower` and
`ArithmeticCarrierRadix2011.current_radix` recover the positive block count,
`q=2^(94517*L)` and population lower bound. The proof of
`ArithmeticWindowInterface.window_of_equations` combines them with
`ArithmeticSaturation.four_block` and `saturation` to extract the two
whole-word no-carry mask tests. It then decodes `C=q-F-alpha` and obtains
origin `dig 47 C 0=1`; the required consequence `(C-1)%4=0` still needs an
explicit all-model lemma. The proof also constructs the internal repunit
identity `J=rep width L`. Applying
`ArithmeticRankForcing2011.current_rank_forcing` to these *actual*
quantities, including its no-carry and `C-1` hypotheses, would give
`rank%4=3`. Some ingredients are currently local inside
`window_of_equations` and need to be exposed or rederived; no such bridge is
claimed yet. Alternatively derive the rank residue directly from the window
origin and `ArithmeticRankForcing.fourBlocks_mod_four`, after proving all
truncated-subtraction and repunit rewrites.

The positive divisible G should be derived from the parent transport factor,
as in `ThirteenCarrierComplete.outer_facts`, but inside the difference ring;
the formal signs, positivity and divisibility witnesses need their own proof.
These model obligations, exact coefficient identification and current-source
closure replay remain open.
