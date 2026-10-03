# A binary four-particle shuttle with a canonical quartic timing certificate

## Globally defined ordinary NCCA

Use alphabet {0,1}, with numerical mass equal to the number of occupied sites. Split the occupied sites into components by joining consecutive occupied sites at distance at most2. Apply these replacements to every component, up to translation:

    {0,1}   -> {1,2}
    {0,2}   -> {-1,1}
    {0,1,3} -> {-1,1,4}
    {0,2,4} -> {0,3,4}

Leave every other component unchanged. These are respectively a right-moving pair, a left-moving pair, a right bounce that pushes its marker, and a left bounce that leaves its marker fixed.

Each replacement preserves the number of occupied sites. Every output hull lies within one site of the old component hull. Distinct input components are separated by a distance of at least3; their enlarged hulls therefore still have disjoint lattice sites (output separation at least1). The simultaneous replacements have no overlapping output support and conserve mass on every finite configuration. Large unrecognized components stay fixed; they are not silently omitted.

The component description defines a genuine local rule. To recognize one of the four finite patterns, check its exact occupancy and absence of occupied sites within2 beyond each endpoint. The largest input span is4. For an output site, every recognized pattern that can change it has all its sites and endpoint guards within distance6 of that site. Every other site's old value is retained. Thus radius6 suffices. A singleton and the vacuum are fixed.

## Independent exact finite conservation certificate

`binary-radius6-conservation-certificate.json` supplies all8192 values of the binary radius6 rule, and a potential on the4096 binary words of length12. It checks every identity

    f(w_0,...,w_12) - w_6
      = P(w_1,...,w_12) - P(w_0,...,w_11).

The bitstring index is sum_i w_i 2^i, with w_0 at coordinate−6. Summing over every lattice site telescopes; both far boundaries are the all-zero vertex. This is an exact certificate of conservation for arbitrary finite configurations, beyond bounded dense tests.

SHA-256 of the certificate file:

    6c99365818697ddd83bdbf529e17756fffaf2eacd55763b235919523b0041699

The code constructs the local table from the component rule and checks the table against whole-configuration component updates on exhaustive and randomized windows. The radius-six recognition argument above establishes equivalence outside the tested windows.

## Exact return times

Start with occupied sites {0,3,4,d}, d>=7. The right-moving pair travels from {3,4} to {d-3,d-2} in d-6 steps. Its component with the right marker is then {d-3,d-2,d}; the right-bounce rule replaces this by {d-4,d-2,d+1}. The left-moving pair travels to {2,4} in d-6 steps. With the left marker0, the component {0,2,4} is transformed into {0,3,4}. One complete return therefore takes2d-10 steps and increments d by1.

After k returns, the complete configuration is {0,3,4,d+k}. Its return time is

    t_k = sum_{i=0}^{k-1} (2(d+i)-10)
        = k^2 + (2d-11)k,       k>=0.

The anchored binary pattern10011 at sites0,...,4 occurs exactly at these times. During a right flight the adjacent pair is strictly farther right; during a left flight it has gap2, so cannot occupy sites3,4 together. The initial and final left-bounce configurations give the only occurrences.

The successive differences2k+2d-10 are unbounded. Consequently this infinite hit set is not eventually periodic, hence is not Presburger-definable. This counterexample belongs to the ordinary binary subclass, not merely the larger typed-weighted class. It disproves extension of the mass-three fixed-input timed-semilinearity conclusion to mass four, while remaining entirely consistent with untimed decidability.

## A costed unique-witness quartic

Write d=7+x with x a free natural input. For natural x,t, define

    P(x,t;k) = [k^2 + (2x+3)k - t]^2.

This polynomial has total degree4, one squared quadratic residual and one natural witness k. Its natural witness fiber is a singleton exactly when pattern10011 occurs at time t, and is empty otherwise. Indeed P=0 is equivalent over the integers to t=k^2+(2x+3)k, and successive values differ by2k+2x+4>0.

With x,t still natural, the same empty-or-singleton statement holds for nonnegative rational k: any rational root of the monic integer polynomial k^2+(2x+3)k-t is an integer. It fails for nonnegative real witnesses, because the quadratic is strictly increasing from0 to infinity on k>=0, so every natural t has one nonnegative real root, including non-hit times.

The direct straight-line evaluator k(k+2x+3)-t, followed by squaring, uses four additions/subtractions and two multiplications when x,t,k are inputs: x+x, add3, addk, multiply byk, subtractt, square. At fixed gap, absorbing2x+3 into a constant gives two additions/subtractions and two multiplications. These are evaluator costs only; they exclude building the lattice input and do not establish any universal-computation or general finite-fold conclusion.

## Reproducible checks

Run `python test_binary_expanding_shuttle.py` with Python3. The script uses only the standard library and writes `binary-shuttle-test-results.json` and the exact conservation certificate. Its recorded run verifies:

- all8192 de Bruijn identities on4096 vertices
- 262,144 exhaustive width-eighteen conservation cases
- 8,192 component-rule versus radius-table window comparisons
- 10,000 larger random locality and translation comparisons
- 302,400 direct orbit steps for d=7,...,30
- 2,424 predicted return times for k=0,...,100
- 20,000 finite unique-witness checks

Finite orbit and witness checks supplement the displayed exact proofs. They do not validate the general mass-four section compiler or replace its mathematical audit.
