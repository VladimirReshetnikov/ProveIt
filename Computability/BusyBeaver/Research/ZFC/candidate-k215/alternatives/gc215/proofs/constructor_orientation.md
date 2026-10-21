# Independent constructor orientations preserve the calibrated calculus

Date: 2026-10-21. All-natural proof for a family of sixteen formula encodings. The stack/proof-list Cantor codec may remain unchanged.

**Prior-work attribution.** The general method of an all-raw-code constructor isomorphism followed by a separate dominated-certificate comparison already appears in the pinned repository's `candidate-k215/alternatives/zero-spare-transfer/report.tex`, section "Prefix recoding has a complete logical calibration." That report also records the same structural leaf census. The present note specializes and independently rechecks that method for the sixteen operand orientations. It is not a claim that the general constructor-transport method is new.

## 1. The sixteen constructors

Let `P(a,b)=(a+b)(a+b+1)/2+b`. The accepted formula constructors are

```
J_r(a,b)=4P(a,b)+r,          r in {0,1,2,3}.
```

Their tags respectively encode implication, membership, universal quantification and equality. For each tag choose independently a bit e_r. Define

```
J^e_r(a,b)=J_r(a,b)         if e_r=0;
J^e_r(a,b)=J_r(b,a)         if e_r=1.
```

Truth remains0 and falsity remains1. A universal quantifier still has a numerical binder as its first *abstract* argument, even if its physical pairing order is reversed. All native schemas must consistently use the selected constructor for their corresponding tag, including constructor-valued numerical labels.

**Encoding theorem.** For every bit vector e there is an effective permutation F_e of all natural numbers such that

```
F_e(0)=0; F_e(1)=1;
F_e(J_r(a,b)) = J^e_r(F_e(a),F_e(b))
```

for every r,a,b. The map is a primitive-recursive involution, not merely a bijection between well-formed formula codes. Consequently the unrestricted native theorem sets satisfy

```
C proves n  iff  C_e proves F_e(n).
```

In particular their native falsity derivabilities are equivalent.

## 2. Explicit all-natural map and proof

Set F_e(0)=0. For n>0 write uniquely `n=4P(a,b)+r`, with 0<=r<4. If e_r=0 set

```
F_e(n)=4P(F_e(a),F_e(b))+r;
```

otherwise set

```
F_e(n)=4P(F_e(b),F_e(a))+r.
```

Both a and b are strictly less than n. For n=1,2,3 they are0; for n>=4 the quotient is at most n/4 and Cantor pairing dominates both arguments. Thus course-of-values recursion defines F_e on every natural input and gives a primitive-recursive function. The positive output need not be bounded by its input, and no such bound is assumed.

The displayed constructor identity follows from the definition whenever the constructor input is nonzero. In the unique zero case, r=0 and a=b=0, both sides equal0. This handles the real alias `J_0(0,0)=0` explicitly. It also proves F_e(1)=1 because `1=J_1(0,0)`.

Prove `F_e(F_e(n))=n` by strong induction on n. For either orientation, apply the already proved constructor identity twice to n's pair decomposition. The tag's swap occurs twice, and the induction hypotheses give `F_e(F_e(a))=a` and `F_e(F_e(b))=b`. The result is the original `4P(a,b)+r`. The n=0 case is immediate. Thus F_e is its own inverse and is bijective, including on raw codes not used by a conventional syntax encoder.

No numerical-order preservation is claimed. For example, with only implication reversed, `4=J_0(1,0)` maps to8, while `8=J_0(0,1)` maps to4. This matters for the dominated eighth row below.

## 3. Exact native proof transport

Transform every natural formula code and every numerical schema parameter by F_e. Each unrestricted native axiom transforms into exactly the same abstract axiom schema formed with J^e. This follows by structural induction through its displayed constructors. In particular, a quantifier binder is transformed too; the theorem is not based on treating an arbitrary natural label as an unchanged atomic symbol.

The full gated bundle is preserved. Its enabling inequalities `C!=A` and `C!=B` are equivalent to the corresponding inequalities after F_e because F_e is injective. Repeated parameters, constructor-valued binders and the literal falsity1 are also preserved. No conjunct of the original bundle is removed.

Numerical MP is transported exactly: the premises a and `J_0(a,b)` become `F_e(a)` and `J^e_0(F_e(a),F_e(b))`, whose native MP conclusion is `F_e(b)`. The theorem-only GEN rule transports in the same way using the transformed binder. Truth0 remains truth0. Induction on a finite proof yields the forward implication; apply the involution to get the reverse.

This argument applies to the unrestricted native calculus, whose only schema-side inequalities here are inequality gates. It deliberately does not transport the arithmetic condition U<=A directly.

## 4. Why the dominated sampler still suffices

Let D_e use the oriented constructors but only eighth-row instances with the ordinary numerical bound U<=A. Every D_e axiom is an instance of C_e, so `D_e proves1` implies `C_e proves1`.

For the converse, use the accepted finite dominated-eighth-row certificate. Its only numerical requirements on implication are

```
I(0,0)=0;       I(a,b)>=a;       I(a,b)>=b.
```

Every dominated axiom leaf in that certificate has its fourth parameter either literally truth0 or a syntactic implication subterm of its first parameter. The pinned certificate contains1,260 such leaves:224 with fourth parameter0,164 with it equal to the entire first parameter, and872 with it a proper implication subterm. The latter have depths1,2,3,4 with counts755,112,3,2. Uniform instantiation preserves this structural relation, and the code inequalities then prove the required numerical bound. Each exact MP step uses only the constructor equations and the zero normalization `I(0,0)=0`.

Both orientations of implication obey those three requirements: `4P(a,b)` and `4P(b,a)` dominate both arguments and have the same unique zero case. Therefore the same finite certificate, interpreted using `I_e`, recovers every unrestricted eighth-row instance in D_e. All other row and bundle families already agree with C_e. Thus D_e and C_e have exactly the same theorem codes, and

```
D_e proves1 iff C_e proves1 iff C proves1 iff ZFC has a finite refutation.
```

The final comparison is the inherited accepted native-calculus calibration. The specialization establishes invariance under all sixteen independently chosen formula-constructor orientations, including the dominated numerical sampler. No order invariance of F_e is required or used.

## 5. Consequences for source experiments

The proof justifies reversing implication alone, quantification alone, or any subset of the four constructor builders. It does not require changing the stack pairing, proof-list pairing, integer fields, or candidate enumeration. At the command level, use the selected constructors consistently in MP and the full AX output; the original strong compiler works because tags, constructor zero cases, and the dominated sampler's completeness still hold. Arithmetic label offsets may remain the usual `U=d,A=d+x,B=h+y`.

An actual source edit must still establish the selected oriented constructor at every macro call, including shared stack/formula arithmetic code. Merely reversing a generic pairing helper could also reverse stack encoding or change the operand order of only some formula occurrences. Those would be different interfaces requiring separate verification. No source DAG cost, allocated state count, binary runtime or blank-start claim follows from this encoding theorem alone.

## Pinned proof data

The dominated certificate referenced above is
`Computability/BusyBeaver/Research/ZFC/k225-formal/lean217/dominated_rho8_full_certificate.json`
at repository commit `34b63b3b197b0a5f285a229d91bc163fcc42ab93`.
It has 3,728 proof nodes and 5,160 shared term nodes. The new standalone reader `check_orientation_certificate.py` independently checks every proof step, simultaneous substitution, bijective schema-variable renaming, exact I/K/Peirce/B/S/full-rho8 root, and each structural bound witness. It contains no numerical Cantor operation. Its PASS receipt is `orientation_certificate_receipt.json`; the input certificate SHA-256 is `3cf18a5fe9f187b50b79d97b84535ce9bf776305728b0cdfe17285e94f028452`. The accompanying all-natural argument explains why the generic checked certificate validates every selected constructor orientation.
