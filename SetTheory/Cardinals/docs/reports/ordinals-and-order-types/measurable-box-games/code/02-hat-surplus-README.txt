FINITE HAT-GUESSING VERIFICATION
===============================

This is original, independent verification code for the accompanying article.
It requires Python 3.10 or newer and uses only the Python standard library.

Run from this directory:

    python verify_hat_strategy.py

The default command exhaustively checks nine cases:

    r = 1, a = 1, 2, 3, 4, 5;
    r = 2, a = 1, 2, 3;
    r = 3, a = 1.

With t = 2**r - 1 and N = 2*a*t, the largest case has N = 18.
Every one of the 2**N physical hat assignments is enumerated.

To select particular cases:

    python verify_hat_strategy.py --case 2 1 --case 3 1

To write to a different report path:

    python verify_hat_strategy.py --output ../data/my_verification.json

The program writes:

    ../data/verification.json   Detailed exact verification results.
    ../data/examples.json      One good and one bad deterministic example.
    ../data/example_prefix.csv Prefix data for the good example, suitable
                               for plotting a surplus path and reference line.

WHAT IS CHECKED
---------------

* Two independently expressed rules give exactly the same individual guess.
  The first aggregates parity across each entire repeated-column group.
  The second directly reads only other mate-pairs and the player's mate.
* Each player's prediction is unchanged when their own hat is toggled.
  This is checked separately for both implementations, on every input.
* The full syndrome is uniformly distributed over F_2**r.
* If the syndrome is nonzero, exactly N/2+a guesses are correct, giving
  endpoint surplus +a.  If the syndrome is zero, all guesses are wrong,
  giving endpoint surplus -a*t.
* Every player has correctness probability 1/2 under uniform input.
  Every player's prediction is also equally often 0 and 1.
* The expected endpoint surplus is zero; its second moment is a*a*t.
* On every nonzero-syndrome input, every prefix, including the empty prefix,
  obeys |D_u - u/(2*t)| <= 3/2, where D_u = correct(u)-u/2.

All decisions use integer arithmetic or exact fractions.  Decimal fields in
the JSON and CSV are display aids, not inputs to the verification decisions.
The script uses explicit exceptions rather than removable Python assertions.

The report records the actual extrema of prefix errors in each finite case,
including an explicit hat assignment and prefix witnessing the absolute
maximum.  An observed maximum for a finite case is not by itself a theorem
for arbitrary parameters.

BIT AND ORDER CONVENTIONS
-------------------------

Players are ordered by round first, column second, and mate third:

    (0,1,0), (0,1,1), (0,2,0), (0,2,1), ..., (a-1,t,1).

Column labels 1,...,t encode the nonzero vectors of F_2**r.
Addition of these vectors is integer bitwise XOR.
Bit i of an input integer is the hat at physical position i.  In a displayed
hat string, the leftmost character is bit 0; this differs from the usual
printing convention for a binary integer.

MATHEMATICAL SCOPE
------------------

The code provides exhaustive verification only for the explicitly listed
finite cases.  It is not a formalization, and it does not machine-check an
infinite strategy, an almost-sure event, an asymptotic claim, or a statement
for all values of r and a.  Those require the article's mathematical proofs.

The running time grows exponentially with N.  A default limit of N <= 18
prevents accidentally requesting a much larger exhaustive computation;
the --max-n option can explicitly raise that limit.
