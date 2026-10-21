# A small transport certificate for CM215

This is an executable finite-certificate prototype, not a new Lean or Rocq theorem. The exact existing CM215 is recommended for the shortest incremental formal endpoint, not as a new construction by this report.

## What is checked

The primary native table is the table already bound to the verified original dense K215. CM215 changes six rows. The control map identifies old176 with new52 and fixes other controls, including halt254. All215 working states remain counted.

Use the state-local invariant:

- At old52, the cell one place left is1.
- At old156, the cell one place right is1.
- At old176 scanning0, the cell one place left is0.

The middle clause removes the need for a history datatype or a separate two-step induction. The initial control0 satisfies this invariant on every tape. An exact finite check proves it is closed under one reference transition, using a five-cell window. There are6880 state/window combinations, of which6840 satisfy the invariant. The same6840 cases verify the reference-to-candidate block: one step normally, three for old52/0 and176/0. The blocks preserve the entire tape and head; the final control is mapped by phi. All strict block interiors are nonhalting.

The prototype also synthesizes a stronger radius-one invariant by finite abstract reachability on state/triples. Each newly exposed exterior bit is nondeterministically0 or1, never silently assumed blank. This finds the same three crucial clauses automatically and reduces accepted windows to4444. Neither version deletes a state; every reference working state and every read row remains abstractly reachable.

Run, with assertions enabled:

    python check_transport.py --certificate evidence/certificate.json

The checker imports no inherited program code and uses only the Python standard library. Literal table hashes identify the inputs. A future kernel implementation must bind its actual machine constants by finite table equality, not treat a hash or this script as a proof oracle.

## The generic theorem still needed in a proof assistant

Let K and M have total one-step functions which leave halted configurations fixed. Let observational equivalence mean equal head, related control, and equal tape reads at every integer position. Do not require equality of the Lean finite-support lists: writing and restoring bits can change list order without changing the tape.

Prove once:

1. A checked finite-window invariant is an inductive invariant of the concrete machine. The local-window proof must account for newly exposed exterior bits.
2. A checked local block has the advertised global tape effect, since it reads and writes only inside the checked window and leaves the exterior untouched.
3. Positive stuttering transports halting in both directions.

For item3, define the simulation clock recursively from the reference run, with increments1 or3 (and increment1 at an already halted reference configuration). Then f(n)>=n and M at f(n) is observationally related to K at n. Reference halting at n yields candidate halting at f(n). Conversely, if M halts at time t, it is still halted at f(t), since halt is absorbing; preservation and reflection of halt through phi implies K is halted at t. Thus no inverse state map, inverse simulation search, or new proof enumerator theorem is needed. Noninjectivity of phi is harmless, but both halt preservation and reflection and strictly positive clock increments are essential.

The desired final endpoint is the existing K215 correctness theorem composed with this transport theorem and the exact native/dense label bridges. It does not need a new70506/95714-step bootstrap proof, a new6209/6176-case unary runtime proof, or a new logical compiler proof. Importing the old endpoint does retain its original dependency closure and checking cost; this simplifies the incremental proof, not the inherited mathematics itself.

## Current verification boundary

The Python checks establish finite obligations and include independent invariant synthesis. The mathematical locality and positive-stuttering argument is supplied above. No Lean/Rocq compiler was available in this execution environment, so no new kernel endpoint or compiled generic theorem is claimed.
