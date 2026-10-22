# Independent exact degree-295 calculation

Write

\[
Q_0=(B-1)J,\quad k_0=\eta+\zeta,\quad
H_0=Q_0-F-2Z-\alpha,\quad
T_2=w(Q_0-F-Z-\alpha)-tQ_0.
\]

Every supplied witness has degree one; all fixed compiler coefficients
have degree zero. No equation is imposed in this calculation.

The top homogeneous parts of the common abbreviations are

\[
a_0=wsQ_0^4,\quad c_0=k_0sQ_0^3,\quad
\Delta_0=w^2s^2Q_0^8,\quad R_0=Q_0^3(Q_0-F).
\]

For the eliminated-root block

\[
Q=(\Delta i c^2)^2,\quad D_*=1+\Delta i^2c^4,\quad
b_*=c+RD_*,\quad v_*=cT,
\]

one obtains

\[
\begin{array}{c|c|l}
\text{quantity}&\text{degree}&\text{leading homogeneous part}\\\hline
Q&46&w^4i^2k_0^4s^8Q_0^{28}\\
D_*&34&w^2i^2k_0^4s^6Q_0^{20}\\
b_*&38&w^2i^2k_0^4s^6Q_0^{23}(Q_0-F)\\
v_*&6&k_0sQ_0^3T
\end{array}
\]

In

\[
A_*=Q(D_*v_*^2+b_*^2)-(Q-1)y^2-1,
\qquad B_*=2Qv_*b_*,
\]

the unique top-degree summand of \(A_*\) is \(Qb_*^2\), of degree122.
Its homogeneous part is

\[
(A_*)_{122}=w^8i^6k_0^{12}s^{20}Q_0^{74}(Q_0-F)^2.
\]

The competing degrees in the local norm
\(K_*=A_*^2-D_*B_*^2\) are244 and214, respectively. Thus

\[
(K_*)_{244}=w^{16}i^{12}k_0^{24}s^{40}Q_0^{148}(Q_0-F)^4.
\]

The outer product \(P=N_{first}N_{main}M N_kN_t\) has degree51.
Using the main norm's exact cancellation, its homogeneous part is

\[
P_{51}=8h\gamma k_0^3w^5s^8Q_0^{29}H_0^2T_2.
\]

Consequently \(P(K_*+1)-1\) has exact degree295 and leading part

\[
\boxed{
8h\gamma i^{12}k_0^{27}w^{21}s^{48}Q_0^{177}
(Q_0-F)^4H_0^2T_2.}
\]

All factors are nonzero polynomials when \(B>1\). More explicitly, the
coefficient of

\[
J^{184}h\gamma i^{12}\eta^{27}w^{21}s^{48}t
\]

is exactly

\[
\boxed{-8(B-1)^{184}.}
\]

Indeed, choose \(\eta^{27}\) from \(k_0^{27}\), \(Q_0^4\) from
\((Q_0-F)^4\), \(Q_0^2\) from \(H_0^2\), and \(-tQ_0\) from
\(T_2\). This is the unique selection yielding the displayed monomial.
Its exponents sum to295. Hence the nonvanishing degree assertion is
uniform for the actual fixed coefficients and does not rely on numerical
sampling or presumed compiler zeros.

