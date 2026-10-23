# Independent review of the square-cofinal radix substitution

Source: ProveIt8c6eec9d19ef80538c8e61ff6e0180040583446a,
Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Master3.lean,
USys_of_mem, and NineReduce.lean, reduced_of_mem.

The source picks w=xy+sum(zs)+1 and b=2^w. Inspection of the rest of
USys_of_mem shows that the special equality for w is used only initially
to obtain w>=1, xy<b, and each zs_i<b. All subsequent uses of w are
through positivity and b=2^w. Therefore the same mathematical proof works
with any larger exponent. This is proof inspection, not a newly compiled
Lean generalization.

For a power-of-two Jones index z=2^s, set B0=(2z)^(L+1), also a power
of two. The digit bound 0<z+c_alpha<2z and distinct exponents from0toL
imply y=e(2z)<(2z)^(L+1)=B0. Replace the usual b=y+1+epsilon by
b=B0*t^2, where t ranges over unrestricted integers and is constrained
nonzero by the existing intersective divisibility merger. Soundness:
b>=B0>y, hence b=y+1+epsilon for a nonnegative integer epsilon, and all
old polynomial definitions agree. The new expression need not be a power
of two for soundness; the Jones ratio conditions recover that property.

Completeness: choose r large enough that w=log2(B0)+2r exceeds the bound
in USys_of_mem. Set t=2^r. The constructed b=2^w equals B0*t^2.
NineReduce.reduced_of_mem preserves this b through its subsequent
eliminations (the epsilon in its conclusion is simply b-xy-1), and the
ratio completion takes this same b as input. Thus the existential
Jones ratio characterization remains valid on this cofinal square-scaled
subfamily. One positivity guard, its Pell witness, is removed.

This argument is specialized to the fixed input x=1. If x is allowed
to vary, the bound B0>y does not alone imply b>xy for soundness.
