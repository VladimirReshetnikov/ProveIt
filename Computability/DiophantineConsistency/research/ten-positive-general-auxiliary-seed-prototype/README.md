# Auxiliary Pell seed for a supplied strong root

`TenPositiveGeneralAuxiliarySeed.auxiliary_of_strong` generalizes the
existing phase-three seed to a supplied strong root. In any IΣ₁ model, it
assumes explicitly `R % 4 = 3`, `c = ycoord(R,a) > 0`, `I≥2`, `f>0`,
`I²+delta(a)=delta(a)*f²`, `c ∣ I`, and `f²=1+c*H`. It constructs positive
T,u,y satisfying the exact Pell auxiliary norm and the literal T identity
`f²*c*T=u+c+f²*R`. The proof uses both phase-three residue lemmas and the
existing quotient constructor. The equality `c=ycoord(R,a)` is essential
and remains an explicit hypothesis; the retained first attempt failed
because that hypothesis was omitted.

This is an abstract reverse-construction ingredient. It does not yet bind a
scaled strong root to an 80 graph, construct the 80 carrier, prove a model
graph implication, or show an iPRA derivation exists.

Accepted guarded check `observations/aux-attempt02/` produced
`/tmp/general-auxiliary-seed-7wza13pi/GeneralAuxiliarySeed.olean`, SHA-256
`938a6e719dc971910a0ba5a4abc008db196f89e4a91e9de692b2a4e85fcade22`.
Its sole source-direct import is resolved, explicitly pinned and rechecked;
full transitive source-object, project/package and dynamic-library coverage
remains inherited.
