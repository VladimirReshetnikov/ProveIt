# Independent review: AQ17 positive bindings

This read-only review checks the 17-variable, 95-operation, degree-20 positive graph and its 112-operation natural shift. Run `python3 -I -S -B check.py` from any directory and compare with `result.json`. The author's checker and receipt also reproduce. No Lean build, staging, new endpoint or provider audit was performed.

Writing `E=X*Y`, `k=eta+zeta`, `c=eta+Y*k`, and `a=E+Y`, the child substitutes `E*Y*k`, `c²`, and `3+4*a+a²` for the parent variables `ellVariable`, `cSquareVariable`, and `deltaVariable`. The checker independently expands the complete parent after substitution and the complete child output and finds the same 3,598-term polynomial over all 17 inputs and four arbitrary integer ports. All three deleted parent binding residuals expand to zero. All 95 operations, inputs and ports are live; the natural graph is exactly the shared `x=n+1` shift.

The expanded output has degree at most 20 in its inputs, and its input monomial `Y⁸*eta⁸*i⁴` has coefficient 1 with no other port-dependent coefficient on that monomial. Its exact degree is therefore 20 for every integer port tuple, including the fixed current ports.

The deleted bindings are positive for positive model inputs: `E`, `Y`, `k`, and `c` are positive, and the last expression is at least 3. Thus a child zero lifts to a positive parent zero; conversely, any positive parent zero has the three squared binding residuals zero and projects to a child zero. These local maps require no port sign assumption. The earlier 20→22 step separately requires strict positivity and representation of the fixed beta, as recorded in the [independent AQ20 review](../adaptive-aq20-substituted-scales104-independent/README.md).

The 17/95, 20/104 and 22/110 model transports and endpoint clients remain unelaborated; external polynomial identities do not supply an internal iPRA theorem. The historical AQ22 parent replay has inherited provider limits. No formal physical PDF semantics or global minimality is established.
