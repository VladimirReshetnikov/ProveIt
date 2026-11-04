# Independent N5/R7 large-q arithmetic audit

PASS for the stated ordinary-integer conditional argument. README `da7510d29cbce2536295c194e24b0d769acda5211e5529cae986d60605ff9418`, checker `6153034ce57133384094fea5b42949dde1a6d8560449c9db51da624b6614aef2`, receipt `624ab8370cf5436d6ed7e3aead57bd60c661480d76c76c722f79e9eaf418c271`, stdout `a45f96cc885fe4f965b34e4fd1c2371251568ea39fc9e13c522b4456f2d48f9e`; stderr empty. Prescribed independent rerun matched, no flags / -O / -OO reject.

For X≥32,Y≥q³≥1, t=2Y, the recurrence gives y5(u+2)=u⁴+8u³+21u²+20u+5 and z⁶−y7(z)=(z²−1)(5z²−1)≥0 at z=t(X+1)+2. An independent polynomial expansion checks all seven coefficients of 2(32+u)⁶−(34+u)⁶ are positive. Therefore t y5(Xt²+2)<y7(z) yields X²>4Y³. Since q≥2³⁰ and 4·2³⁰>65532², Y≥q³ and h=q−1<q imply X²>(65532hY)²; all terms are positive, so X>65532hY.

An independent sparse polynomial calculation verifies the projection reduction P(MX)−P(1−M)=H·quotient and P(1−M)=−4(4Y−1)(516Y−1)(127Y−32), M=4Y,H=M(X+1)−1. Odd H cancels 4. For S=h times that product, positivity, the strict X bound, and 4·516·127=262128 give 0<j=S/H<Y whenever H|S; also 0<32h<Y. Reducing modulo Y gives j≡32h and hence j=32h. Cancelling h>0 then reducing modulo 4Y gives 4Y|3Y, impossible for Y>0. The asserted polynomial remainders and strict inequality directions were independently verified.

This is ordinary-integer conditional arithmetic requiring the explicit scalar inequality and weighted projection; it is not yet a Lean graph binding, N5/R7 graph exclusion, fixed-BFS theorem, reverse guard or iPRA result. No Lean was run in this audit.
