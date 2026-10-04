# Optional exact physical clock

This supplements PROOF.md. All identities follow from the proven primitive formulas, without executing a trajectory.

- L_z(u) duration: 2(1+u)z (second target hit is at time 2z+uz, then return distance uz)
- H_z(v) duration: 2z (messenger travels from anchor to reflector and back at unit speed)
- T_z(c), starting target x: 2(2-c)x/(1-c)+2z

The upper shear A, consisting of two pairs T_y(-1/4),T_d(1/6), has duration

    t_A(x,y,d)=16x-y/5+16d/3.

The reflected middle shear, in r=d-y,s=d-x coordinates, has duration

    t_B(r,s,d)=(1016/57)r+(2972/285)s+(1388/855)d.

The two anchor transfers contribute 2d. Substituting the affine shear outputs into the next block's time gives the 114-event rotation duration

    ℓ_R=(222/5)d+(30512/1425)x-(9942/475)y.

The final ordered homothety takes 3(x_R+y_R+d). The complete 138-event macro duration is

    ℓ=(247/5)d+(36497/1425)x-(10227/475)y
      =(37264/855)d+(36497/1425)ξ-(10227/475)η,

where ξ=x-d/3, η=y-2d/3. On the exact valid cone this is positive, as the sum of strictly positive primitive flights.

The centered return matrix is diag(1/2,R/2). Summing the convergent matrix series gives

    T=(74528/855)d+(53102/3705)ξ-(144302/3705)η
     =(1204366/11115)d+(53102/3705)x-(144302/3705)y.

This formula applies conditional on infinite validity. In particular all rational valid inputs have rational accumulation time, consistent with Theorem C of the at-most-four-signal packet. The stationary left anchor has limiting position 0; all other marker positions converge to 0 because d halves each macro, and the messenger stays between the anchors. Thus every signal accumulates at space-time (0,T).
