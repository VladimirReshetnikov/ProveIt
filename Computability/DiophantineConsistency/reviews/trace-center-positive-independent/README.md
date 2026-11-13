# Independent review: generic reverse-center positivity

For arbitrary model-semiring `b,t,rho,kappa,tau,f,y,u,n` in an IΣ₁ model, the checked source assumes `tau>0`, `y>0`, `kappa<f` and the exact balance `n+kappa=tau*f*y+u*u*(b*t)+t+rho`. It derives the strict bound `u*u*(b*t)<n`, hence the positive truncated residual `0<n-u*u*(b*t)`. The proof uses positivity of `tau` and `y` to get `f≤tau*f*y`, then adds the other nonnegative summands and cancels `kappa`.

`check.py` rechecked the theorem statements, accepted source/runner/output, both direct package pins, logs and named `[propext, Classical.choice, Quot.sound]` reports, as well as the rejected first attempt. No independent Lean replay was performed. The packet does not import the reverse-carrier theorem, bind these arbitrary quantities to trace75 graph rows, construct a 73-row equation, or prove graph equivalence or iPRA; package-transitive/dynamic and external-file ancestry remain inherited.
