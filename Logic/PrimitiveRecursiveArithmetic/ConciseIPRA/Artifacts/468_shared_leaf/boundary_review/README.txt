TARGETED PROOF-BOUNDARY REVIEW

Reproduce from this directory, supplying the candidate source path:

    python3 boundary_audit.py PATH/TO/checker468.py .

No copy of the candidate is included here. The script reconstructs the two
fixtures, creates deliberately unsound controls in a temporary directory,
and runs each candidate/control pair with and without Python optimization.
The receipt records eight isolated executions and zero failed expectations.
Acceptance is exit status zero with exactly ACCEPT followed by one newline.

The fixture goals are canonical closed guarded formulas and every JSON node
is an exact integer or array. Thus these attacks exercise the actual public
theorem contract, not malformed-input handling.

1. false_parity_goal.json: seven proof packets

The public formula is

    D_(x,y) (I(y,0;u.0) = I(y,0;u.S(0))).

Its zero instance is true and its instance at one is false. The x variable
is unused, so the formula is false in the natural numbers.

The shifted decoder uses even formula depths 2+2p and odd term depths 5+2p.
At a numerical root, coordinate 2 is an alias of zero. At a formula root,
it is outside the retained interval. The parity factor forces its formula
reading to truth rather than allowing it to substitute an arbitrary formula.
Deleting that factor accepts the fixture; the unchanged checker rejects it.

This adapts the existing parity-deletion attack in the ProveIt article and
ipra_whole_json_refinement package to the shifted shared-leaf protocol.
It is a new protocol-specific certificate, not a new obstruction theorem.

2. false_early_floor_goal.json: five proof packets

The public formula is

    D_(x,y) (I(y,0;u.x) = I(y,0;u.y)).

Its zero instance is true. The universal instance would require x=1 and
x=2, so the formula is false in the natural numbers.

Change the retained-coordinate test from k <= a < d to k-1 <= a < d.
At parent floor zero this wrongly admits the future parameter -1, denoted z,
while checking the introduction witness. Supply S(z) as that witness. After
the rule actually allocates z, its supposed progressive step is literally
R=R, where R=I(S(z),0;u.S(z)). Two valid zero-computation leaves and one
equality-transport step prove this reflexivity. The induction premise was
illegally allowed to change its witness with the fresh step variable.

In shifted raw coordinates, set

    R        = [[-1],0,[-1]]
    s        = [0,R,0]
    major    = [s,R]
    template = [5,R]
    goal     = [[[7,0,9],[7,0,7]]]

The JSON stack consists of the following records, with abbreviations expanded:

    [0,0,R,0]
    [0,0,R,0]
    [major,s,R,template]
    [0,0,0,0]
    [0,0,0,[-1]]
    [goal,0]

The last record is the goal/floor header, and records are consumed backwards.
The candidate rejects the unclosed witness before allocating the fresh name.
The modified checker accepts. This five-packet certificate was constructed
for the present review; the future-eigenparameter-capture mechanism is prior
art in the repository's scope audits.

These finite checks establish the behavior of the two controls on the stated
inputs. They support, but do not replace, the universal sorted-decoder proof
of the unchanged candidate. No new Lean or Rocq verification is claimed.
