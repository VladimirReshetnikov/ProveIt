#!/usr/bin/env python3
"""Small example using the explicit reference solver; standard library only."""
from verify import NFA, Periodic


def main() -> None:
    # Alphabet {0,1}; rows contain destination-state bitsets.
    # Union of the even-length language with 0* and 1* (article Example 9.3).
    automaton = NFA(((2, 2), (1, 1), (4, 0), (0, 8)), initial=13, final=13)
    periodic = Periodic(automaton)
    obstruction = periodic.forbidden()
    print(f"Transient={periodic.t}, period={periodic.p}")
    print(f"Finite stabilization: {obstruction is None}")
    if obstruction is not None:
        residue, phase, word = obstruction
        print(f"Obstruction: residue={residue}, phase={phase}, word={word}")
        for copies in (1, 2, 4):
            target = periodic.pump(obstruction, copies)
            print(f"copies={copies}, length={len(target)}, rank={automaton.rank(target)}")


if __name__ == '__main__':
    main()
