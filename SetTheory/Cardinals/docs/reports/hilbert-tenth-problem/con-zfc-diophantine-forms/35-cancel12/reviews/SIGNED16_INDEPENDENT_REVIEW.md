# Independent review of the sixteen-integer construction

## Verdict and scope

I independently read the new signed section and emitter, the frozen package-29 signed17 proof, and the complete relevant proofs in `Master3.lean`, `NineReduce.lean`, and `NineRatio.lean`. I find the new scaled-square restriction and smaller signed separator mathematically sound relative to the explicitly inherited Jones, parent-quartic/compiler, and K215 theorems. This is an ordinary mathematical review, not a new kernel-checked theorem or an endorsement by an external reviewer.

The test receipt separately records finite diagnostics. The code reads the emitted DAG as inert JSON and does not import the signed generator. It verifies the 16 distinct variables, absence of the old epsilon variable and y-index fixed leaf, presence of the radix-root variable and b-scale fixed leaf, DAG liveness/topological order, 1865 binary operations, and the advertised total-degree upper bound. It also compares the abstract finalizer with a full rank-eight multiquadratic conjugate product on 300 assignments with arbitrary signed radicands, and checks 300 guard stacks. Those tests corroborate definitions; the arguments below establish the universal points.

## 1. Scaled-square radix: soundness and cofinal completeness

The proof does not assume that a generic signed choice of the new variable e makes b a power of two. It only initially uses e nonzero to obtain b=b_scale e² >= b_scale > y_index. Hence epsilon=b-y_index-1 is nonnegative and all literal source expressions agree with their old definitions. The source ratio soundness theorem itself recovers b=2^k (`NineRatio.ratio_sound`), as required by `NineReduce.mem_of_reduced`. This is the correct order of implications.

For completeness, the relevant statement is stronger than the bare existential conclusion of `Master3.USys_of_mem`, but it follows from its displayed construction. Given a fixed quartic witness z_i, choose any integer v >= x*y_index + sum(z_i)+1 and b=2^v. The construction needs v>=1, x*y_index<b, z_i<b, and the positive power-of-two hypothesis. The first three follow from v<2^v and the chosen bound. Later steps construct q, lambda, theta, polynomial digits e,l,g, divisibility witnesses m,t, and the positive slack alpha=(b-x*y_index)q²-e*l*g². Their proofs use these inequalities, index bounds, and the unchanged power-of-two condition; none requires the initial exponent to be the smallest chosen value.

I checked the rest of the construction, rather than relying only on absence of a textual reference to the equality, because Lean automation can use hypotheses implicitly. In particular the strict slack estimate uses b-x*y_index>=1 and e*l*g²<q², which persist for all sufficiently large powers of two. The normalization argument giving g>0 is independent of the exponent choice.

`NineReduce.reduced_of_mem` preserves the chosen b: it explicitly introduces epsilon=b-x*y_index-1 and rewrites the already-constructed witness in that coordinate. `NineRatio.ratio_complete` then takes b as a parameter and returns h,s,w,phi,i,j without changing it. Therefore restricting v to the arithmetic progression kappa+2t, with b_scale=2^kappa and e=2^t, preserves completeness. This progression is cofinal, and its members satisfy b=b_scale e². The strengthened cofinal result has not been compiled as a new Lean theorem in this work; the ordinary constructive proof is sufficient for the stated ZFC-formalizable theorem.

## 2. The coefficient b_scale genuinely dominates y_index

The index certificate provides z_index>|c_alpha|+1. Thus all digits z_index+c_alpha are integers strictly between one and 2*z_index. Their exponents are distinct by base-five uniqueness, lie between zero and L, and the exponent L is present. Viewing omitted exponent positions as zero digits shows

    2*(2*z_index)^L <= y_index < (2*z_index)^(L+1)=b_scale.

Consequently the new fixed b_scale is a fully specified coefficient sufficient to derive the old epsilon coordinate in soundness, even though y_index itself is absent from the final DAG. The source index remains mathematically specified by its finite recipe.

## 3. Order of nonvanishing, guards, and signed separation

The denominator Ddiv=J*F is nonzero at every signed assignment. The proof J=4A-5 !=0 is immediate. If F=0, then (1-A²)E²=1 forces A=0 and E=+-1, but E=i*J*D*C² would be divisible by five. Thus this exceptional case is genuinely excluded before any positivity or squarehood is recovered.

The homogenized intersective polynomial Tmerge is then nonzero because its dehomogenization at the rational Tdiv/Ddiv+residue is `(t³-t-1)(t²+23)`, which has no rational root. If Smerge=0, the eight-factor finalizer specializes exactly to Tmerge^8 !=0. Every zero therefore has i, e, and all six guard variables nonzero.

Only now is the smaller separator used. For each guard stage, d=3x+2 or 3m-1 is a nonzero integer, the previous product is nonzero, and z is nonzero. Hence B=1+4d*Cprev²*z² is 1 modulo 4 and has |B|>=3. Therefore |Cstar|>=3^6, even before Cstar has been proved positive or square. In particular |Cstar|>sqrt(|Cstar|), validating w1=Cstar with either sign.

The universal estimate

    sqrt(abs((P²-1)K²+1)) <= P²+K²+1

gives |w2|>sqrt(|Cstar|)+|w1|sqrt(|a0|) for w2=Cstar(P²+K²+2). Thus the largest nonzero root flipped by a Galois automorphism dominates every earlier contribution, regardless of the signs of the radicands or weights. A nonzero square root of an integer radicand has modulus at least one; zero roots need no recovery. This deals correctly with dependent square classes as well as negative candidate radicands. A rational signed sum therefore forces each root rational and hence integral.

This proves Cstar,a0,a1 are integer squares and Smerge divides Tmerge. Only after those conclusions is the coprime Pell guard used to obtain nonnegative base variables and positive margin. There is no circular appeal to positivity in the signed-separator argument.

## 4. Divisibility recovery and completeness

The valuation argument for the homogeneous intersective polynomial is valid for every prime, including 2 and 23: if v_p(Ddiv)=alpha>beta=v_p(Tdiv), then Tdiv+Ddiv*residue has valuation beta. Its cubic factor has unique lowest valuation 3beta, and its quadratic factor has unique lowest valuation 2beta. Therefore Tmerge has valuation 5beta<5alpha, contradicting Ddiv^5|Tmerge. Thus Ddiv|Tdiv. The factor Z also imposes all intended nonzero requirements because Tmerge never vanishes.

For completeness the intersective polynomial has a root modulo every nonzero modulus. At odd primes other than 23, either the cubic has a simple root or irreducibility makes its discriminant -23 a square, producing a simple quadratic root. At 23 the cubic root 3 is simple; at 2 the quadratic has roots at every power because -23 is 1 modulo 8. Hensel lifting and CRT give the claim. After Ddiv|Tdiv, select the residue coordinate to make the polynomial divisible by Z, so that Smerge|Tmerge. Integral square roots then make the last variable an integer.

The two unguarded coordinates are treated exactly as in the older signed17 proof. The margin first gives K nonzero and a bound on g, which implies R positive; then C>0 and the margin force K>0. If h<=0, the square a0 lies strictly between consecutive squares, except K=1, which is excluded by its congruence. Hence h>=1. The nonzero i can be replaced by |i| because the relevant expressions use it only through a square. The recovered old eight nonnegative coordinates therefore satisfy the literal Jones interface.

## 5. No blocking issue found

The construction is new in the supplied repository family, but its statement remains an explicit fixed-instance result with inherited semantic dependencies. It is not a claim of a new best universal variable bound, a proof of Con(ZFC), or a new end-to-end Lean/Rocq formalization. The supplied proof correctly keeps these distinctions.
