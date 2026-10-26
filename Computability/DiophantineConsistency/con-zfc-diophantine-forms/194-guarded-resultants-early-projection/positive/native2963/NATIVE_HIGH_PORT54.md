# Exact compact54 high-mask word

`NativeHighPort54.lean` defines the complete native MF recipe as31
nonzero radix digits: origin4; the literal clause mask at2409 and3015;
unit tests at528–537,585–595,1203,1807; four87-bit padding digits at
4823–4826; and one38-bit padding digit at4827. The source fourth port
is `beta + highPort radix`, with the shift applied once.

`highPort_recipe` proves equality with the one-page geometric-sum formula.
`highPort_lt`, `highPort_mod_eight` and `highPort_population` prove the
native mask bound, residue4 modulo8, and exact binary population520.
The population proof uses the new generic `NativeWordPopulation` theorem
for an injectively placed finite table; it does not evaluate the entire
429959-bit mask or normalize a4831-element digit list.

`mask_word` proves the complete repeated high-mask identity
`word(maskDigits) = MF × repunit(429959,N) − 1`. The decrement changes
only the origin digit from4 to3; it creates no borrow. At residues2409
and3015, `maskDigits` equals the literal local `clauseMask`.

`source_clause_masks` composes these identities with the checked sparse
source/convolution calculation. The high-mask array, its radix bound and
its word identity are now outputs of the construction rather than
hypotheses. The arithmetic coefficient Interface and exact K/rawWord
binding remain explicit. The temporal contribution remains explicitly
added to each clause sum; phase alignment is not asserted here.

The two generic population APIs and all21 public high-mask APIs have
matching dedicated axiom checks. They pass with only `propext`,
`Classical.choice`, and `Quot.sound` or subsets. The high-mask main has one
benign warning that a symbolic4831st power is left unevaluated. No new
axiom, `sorry`, accepted-tableau hypothesis or internal ZFC claim is used.
