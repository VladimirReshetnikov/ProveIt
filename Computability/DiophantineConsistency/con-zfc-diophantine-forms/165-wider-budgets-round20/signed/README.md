# Round 20: signed spheres and power majorants

Every endpoint is one fixed ordinary quartic over unrestricted integers,
exactly the sum of squares of the residuals in its `equation.json`.
Every collected coefficient occurs in `expanded_polynomial.json`.

| Endpoint | Variables | Rows | Degree | Terms | Height |
|---|---:|---:|---:|---:|---:|
| balanced238 | 238 | 175 | 4 | 5236 | 3968 |
| dimension237 | 237 | 174 | 4 | 18569 | 7680 |
| power239 | 239 | 175 | 4 | 5137 | 3968 |
| exposed241 (technical lifting source) | 241 | 178 | 4 | 4913 | 170496 |
| power_exposed242 (technical lifting source) | 242 | 178 | 4 | 4814 | 170496 |

For each equation, the ordinary proofs establish **in ZFC** that an integer
zero exists iff a finite syntactic ZFC refutation exists. Negating this is
integer unsolvability iff Con(ZFC). No consistency assumption or consistency
proof is used. No global simplicity optimum or newly compiled proof-assistant
endpoint is claimed.

`PROOF.md` supplies the complete signed-affine-radix/sphere argument, including
unit and negative radix branches and radius-three-quarters factorial recovery.
`POWER_MAJORANT_PROOF.md` proves the new F=t^t argument at t=16+2h^2 and checks
the generalized-CRT interface. The inherited complete factorial-free report
is `inherited_free/main.tex`; its companion TeX inputs are retained.
The required cofinal odd-square beta completeness argument is retained
verbatim as `inherited_free/ODD_SQUARE_BETA_PROOF.tex`. The
inherited shared-error proof is `inherited_shared/FULL_SOURCE_PROOF.tex`.
These historical proof sources retain their historical endpoint metrics.
The new proof below and our root report state the current endpoint theorem.
The complete retained arithmetic and C222/ZF/ZFC logical closure is `parent252`.

## New source changes

The shared family starts from the authenticated 244-variable shared-error
source. It replaces exactly

    M^2 - 4*(S^2 + sum(R_i^2)) - 1 = G(a,b,c)

by

    M^2 - 2*(S^2 + sum(R_i^2)) = G(a,b,c),
    G(a,b,c)=a^2+b^2+c(c+1).

The proof obtains M!=0 from the already odd nonzero radix before dividing;
it does not incorrectly infer M!=0 from the new sphere. All twelve entries
have magnitude <3|M|/4. The noncircular signed-binomial bootstrap and stronger
nearest-factorial lemma restore the old factorial signs.

The power family first makes exactly two raw-source changes to the incoming
factorial-free construction: t0=h^2 becomes t0=2h^2, while the growth power
base 2t0+34 becomes t0+16. Thus the actual t=t0+16 satisfies t=16+2h^2 and
F=t^t. The full actual-base power frame is regenerated; no required frame
atom is dropped. Its common sphere similarly changes from coefficient4 and
constant1 to coefficient2 and constant0. The accepted canonical digit tails
are <L/32; hence |r-rho|<(3/4+1/32)L<L recovers each digit. Completeness
uses 2 sum(R_i^2)<22M^2/1024<M^2 and the universal G form.

## Exact algebraic maps

The frozen `certificates/*.json` give every operation. In each stage, row
addition f_i <- f_i+k f_j is inverted by coefficient -k. Coordinate
substitution x_j(old)=x_j(new)+k*x_i(new), i!=j, is an integer bijection.
A projection deletes a literal unit row ±(v-f), never divides by a nonunit,
and substitutes its complete integer polynomial f everywhere. For quadratic
f the eliminated v occurs only linearly in every other row; this is checked
before substitution. All residual degrees stay <=2. Compaction is only
renaming of live coordinates in ascending original order.

To recover a source zero, undo stages and operations in reverse order.
Restore a deleted v by its recorded polynomial f, then undo the coordinate
change by evaluating old x_j=new x_j+k new x_i. Row additions do not change
coordinates. Do not set projected variables to zero. Only coordinates listed
as genuinely unused in the raw projection certificate may be filled freely.
Old sign auxiliaries instead receive the ternary witnesses proved to exist.

balanced238 has six unit projections: three affine exposures and the quadratic
coordinates mul.281, add.292, mul.194. dimension237 additionally projects
affine add.380. power239 applies the same six valid projections to its own
source. Every definition is recorded in the frozen certificates in the
coordinate indexing of its stage. The checker verifies exact unit equations,
all inverse shears, all inverse row operations, the full resulting residual
lists and every quartic coefficient.

## Replay offline

Python 3.10+ standard library only, from any working directory:

    python3 -B build.py --check
    python3 -B verify.py
    PYTHONOPTIMIZE=1 python3 -B -O verify.py

The new independent checker imports no producer. It reconstructs the exact
shared raw-source mutation, independently checks 202 integral restorations,
checks the inherited factorial-free raw mutation, checks both new power rows,
replays all Horn/projection/translation maps, and invokes the complete pinned
parent checker. Its explicit tests run identically under -O and reject
malformed coefficients, restorations, noninvertible maps and nonlinear
quadratic substitutions. Exact finite certificates authenticate the literal
objects; they do not replace the unbounded mathematical proofs.

`build.py --check` replays all frozen final maps byte-for-byte without an
optimizer, search for a refutation or network access. The only shared
arithmetic closure is `parent252`; small byte-identical checker prerequisites
are duplicated under `inherited_free/parent` solely for its original relative
path interface, and their identities are pinned. `SOURCE_PINS.json` binds all
inputs and operation certificates. `WHITELIST.json` lists the portable files.

Prepared with AI assistance for the user's ProveIt research. Inherited source
notices and licenses are retained; improvements are attributed to the seven
round-20 inputs and the prior round-19 exact transformation family.
