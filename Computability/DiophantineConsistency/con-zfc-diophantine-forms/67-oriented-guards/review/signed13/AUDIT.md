# Independent review of the split108 thirteen-integer Jones variant

## Source changes

The globally negated two-shear split108 source has the same common zero set as the authenticated 31-positive parent. Positive leading coefficients (2,2,beta_native), kernel degrees (1939,1842,1738), and the large complete coefficient tuple are used coherently. The pad B^1946 has exponent 2*1842−1738, so the completed-square correction is exactly at the needed degree. Since beta_native>10,

D1(B)^2/(2D2(B)) < 9 B^1946/(2(beta_native−1)) < B^1946/2.

Thus G+B^1946 is positive for every signed g, not merely after g's interval has been recovered. For integer Uc, the lower bound N0 D2 Uc²+Uc is nonnegative, making Sc positive for all signed g. With Tc positive this gives R>L² before the guard/spectator recovery. That unconditional estimate is essential to exclude the zero-spectator branch of the retained finalizer.

The pad is above all targets (1946>1939) but below the total source height1954. It does not alter any target coefficient, and carries propagate only upward. The revised bounded-source range remains valid with N0=B^109 and L=B^2064. Source signs and parity restrictions retain the old whole tuple; none is substituted componentwise.

## Threshold calculation

With b=2 epsilon², B=a b², a=2^kappa, kappa=2134940, the signed polynomial threshold must be

Nhat=2^(17 kappa/2−9) epsilon³ B^1089.

Its square is exactly 2^(−21) a^17 b³ B^2178, with the displayed negative exponent only a proof-side rational identity; the actual coefficient exponent17 kappa/2−9 is a positive integer. Hence Nhat²<B^2195<L², while |Nhat|>=c=b B^108 and >=8. The circuit uses Nhat only through its square, so replacing it by its absolute value in the proof introduces no operation or unknown.

After recovery b=2^k, k is odd. The actual mask population is131 nu−31k−22 and L=2^(2064nu). Therefore the required exponent is2195nu−31k−21. This agrees identically with

2(17 kappa/2−9+1089nu)+3(k−1),

where nu=kappa+2k. The old linear-epsilon threshold would be incorrect; the cubic correction in the emitted source is necessary and correct. Cofinal b=2^(1+2r) both represents every sufficiently large scale and makes the Jones canonical omega a square as required.

## Retained finalizer and scope

The CRT H reparameterization, interval guard, coprime spectator stack and rational two-root recovery are unchanged from the identified previous Jones-only construction. Their proof order remains valid with the new unconditional R>L² bound and |Nhat|>=b,c. In particular, a1=0 is not excluded prematurely: the first two guards plus the unconditional source bound force positive A,C,D,F,I before deriving a1>0 and the third guard.

No mathematical incompatibility was found under the explicitly inherited Jones/compiler interfaces. This is a degree/operation tradeoff, not a simultaneous improvement: 10,461,744/519 versus11,543,632/518. The construction does not import the new Sun reduction, and no new end-to-end kernel certificate is asserted.

Fresh normal and optimized replay outputs and a separate topology/liveness/degree/square-only-threshold receipt accompany this review. Source snapshots preserve the reviewed files. The two minor prose corrections are now resolved: the artifact filename is consistent and the B/8 bound explicitly applies to the unnormalized polynomial coefficients, not to normalized base-B digits after borrowing. The circuit is unchanged.
