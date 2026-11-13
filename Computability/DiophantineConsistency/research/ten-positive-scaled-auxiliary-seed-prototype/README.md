# Scaled strong and auxiliary Pell witnesses

`TenPositiveScaledAuxiliarySeed.scaled_auxiliary` constructs one coherent
strong and auxiliary tuple in every IΣ₁ model. Given `R%4=3`, positive τ,
an arbitrary internal bound L, and `c=ycoord(R,a)`, it obtains m>L, f>L and
positive i,T,u,y. With `D=delta(a)`, `U=i*c²`, `A=D*U²*τ²`,
`F=1+2A`, and `I=D*U*(2τf)`, the theorem proves

    f² = 1+A,
    xcoord(2m,a) = F,  ycoord(2m,a) = U*(2τf),
    F²*c*T = u+c+F²*R,
    I²*u²+y² = 1+I²*y².

The same f and i occur in the strong and auxiliary equations; f can be
chosen above any supplied L. The proof applies the arbitrary-bound strong
seed and the separately checked generalized auxiliary seed, checking the
necessary norm and divisibility assumptions without assuming a graph zero.
It does not yet construct the 80 carrier coordinate or prove a 90→80 graph
implication, external tuple binding, or iPRA endpoint.

Accepted guarded check `observations/auxjoin-attempt02/` produced
`/tmp/scaled-auxiliary-seed-sax3cafk/ScaledAuxiliarySeed.olean`, SHA-256
`c6f3f4c9da7cbbf712d41d021af204e1fc7ef243838fa4c5f21d30370a152c82`.
Attempt01 failed on algebraic grouping. Both direct imports are resolved and
checked against explicit selected paths/hashes before and after the run;
full transitive source-object, project/package and dynamic-library boundaries
remain inherited.
