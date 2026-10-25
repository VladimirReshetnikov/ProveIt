# A bounded mixed-radix target field for the indexed fixed seed

This is a code-free mathematical packing proposal, not a new printed
seed, page, native tuple or executable. It preserves every one of the
accepted430 actions and therefore the entire indexed943 tile language
and all four fixed coefficients. It does not change the polynomial,
its unknown count, degree or arithmetic-operation count.

The current436-character base62 literal is the accepted indexed seed,
SHA25670d37d1d62180194bc527f662cd77ccace5eadadccc01c9a82437efb5fa44ba6.
Its target field can instead be bounded by1454 bits rather than1675.
With the same other two fields, the proposed new integer would have
exactly399 base62 digits,37 fewer. No399-digit literal has been computed
or emitted here. The additional decoder notation might outweigh the
shorter numeral on a complete page; that comparison remains open.

## 1. Retained data and the eligible-target invariant

Use the current alphabet0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz.
Let Aold be its entire current436-character integer. Its existing fields
are the fixed integers

    N=Aold mod2^636,
    Told=floor(Aold/2^636) mod2^1675,
    E=floor(Aold/2^2311).

For0<=j<430, let nu_j=bit_j(N), sigma_j=sum_(k<j)nu_k.
The accepted breadth-first target decoder is

    u_j=nu_j*(1+sigma_j)
          +(1-nu_j)*[floor(Told/216^(j-sigma_j)) mod216].

There are214 new-target flags and216 existing-target positions. At an
existing-target position the original target lies in0..sigma_j or is
the distinguished halt215. Inert inspection of the entire existing
target data confirms this eligibility invariant at every position;
the sole halt target is action125. This packing does not change the
state numbering, exception flags, direction flags or initial action.

## 2. Encoder as finite constant arithmetic

For0<=j<430 define

    r_j=(sigma_j+2)^(1-nu_j),
    P_j=product_(0<=k<j)r_k,
    d_j=(1-nu_j)*(u_j+1)*(1-floor(u_j/215)),
    Tmix=sum_(j=0)^429 d_j*P_j.

Empty products are1. All limits and operands are fixed data, not
Diophantine unknowns. Thus every product is finite integer arithmetic.
At a new target, r_j=1 and d_j=0. At any existing target, the halt is
encoded by0 and ordinary targets0..sigma_j by1..sigma_j+1. Therefore

    0<=d_j<r_j

at every position. The standard mixed-radix identity gives

    0<=Tmix<product_(j=0)^429 r_j.

Use the proposed fixed integer

    Anew=N+2^636*Tmix+2^2090*E.

This defines the new packing mathematically from the accepted actions.
An actual future self-contained page would print Anew's entire literal,
not refer to Aold or an external action table.

## 3. Closed inverse and full action identity

Recover the fields from a proposed new literal by

    N=Anew mod2^636,
    Tmix=floor(Anew/2^636) mod2^1454,
    E=floor(Anew/2^2090).

Recover nu_j,sigma_j,r_j,P_j as above, then set

    d_j=floor(Tmix/P_j) mod r_j,
    u_j=nu_j*(1+sigma_j)
        +(1-nu_j)*(d_j-1+216*floor(1/(d_j+1))).

The remainder modulo1 is0. All denominators are positive fixed
integers. The mixed-radix digit equation follows because every prefix
sum is below P_j, while every later term is divisible by P_j*r_j.
When nu_j=1 the second summand vanishes and the old new-target rule is
restored. Otherwise d_j=0 gives215, while d_j>=1 gives d_j-1.
Thus every decoded target equals the original target exactly.

For completeness, retain the original fixed write/direction decoder:

    m_q=bit_(430+q)(N), tau_q=sum_(k<q)m_k,
    F_q=14*(1-m_q)+m_q*[floor(E/16^tau_q) mod16],
    v_j=bit_(2*(j mod2))(F_floor(j/2)),
    direction_j=bit_(2*(j mod2)+1)(F_floor(j/2)).

All430 state/read indices, writes, directions and targets consequently
agree. The accepted indexed tile construction uses exactly those
actions, unchanged signal ranks and unchanged fixed tile families.
Its943 tiles and four coefficient integers therefore agree term for
term. No new color conjugacy, native semantics, controller or Pell
theorem is needed merely to repack the same finite literal.

## 4. Exact bounded size evidence

Inert reads of the accepted fixed seed give

| Item | Exact value |
| --- | ---: |
| Aold bit length |2594|
| Existing target field bit length |1675|
| New-target flags |214|
| Existing-target positions |216|
| Product of proposed radices: bit length |1454|
| Minimum/maximum radix at an existing position |3/216|
| Retained E bit length |283|

No proposed digit stream was constructed for this census. The product
bound above fits Tmix into1454 bits. Since E has283 bits, Anew has
exactly636+1454+283=2373 bits. Direct integer inequalities give

    62^398 < 2^2372 <= Anew < 2^2373 < 62^399.

Thus its eventual base62 literal has exactly399 characters. This is
a theorem about the packing and the pinned data, not a claim that a
new399-character artifact has been generated or checked.

The37-character reduction concerns the numeral alone. The decoder adds
bounded products, mixed-radix digits and a halt escape. The old uniform
base216 decoder is shorter to print. A future complete TeX/PDF comparison
must charge every extra definition, reproduce all430 actions and943 tiles
and every whole native coefficient byte, and prove the entire resulting
page shorter or easier to read. No such comparison or page fit is
accepted here. The current66-page preparation keeps its original copied
constant body and is unaffected.

## 5. Boundary

The selected complete accepted indexed packet remains immutable. This
note retains its whole byte inventory and mathematical calibration;
inert hashing/JSON/constant arithmetic supplied the census above. No
repository application was imported, compiled or run, no TeX/PDF process
ran, and no new seed/equation/source program/data packet was emitted.
Any implementation requires its own full static reviews and explicit
execution release. This proposal claims neither minimum seed length
nor a smaller complete page, and changes no Lean work or maintained PDF.
