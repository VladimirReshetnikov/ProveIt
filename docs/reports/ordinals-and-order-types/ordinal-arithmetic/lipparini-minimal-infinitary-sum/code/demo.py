#!/usr/bin/env python3
"""Small executable examples; w in the output denotes omega."""
from ordinals import OMEGA, ONE, finite, omega_power, Profile


def main() -> None:
    ww = omega_power(OMEGA)
    examples = [
        ('Cofinal natural-number tail', Profile(OMEGA)),
        ('One omega head over that tail', Profile(OMEGA, (OMEGA,))),
        ('Constant omega', Profile(OMEGA + ONE)),
        ('Constant omega+1', Profile(OMEGA + finite(2))),
        ('Infinite remainder: the leading one is absorbed',
         Profile(OMEGA, (OMEGA.natural_times_finite(2) + finite(3),))),
        ('Cofinal tail below omega^omega', Profile(ww)),
        ('One omega^omega head above that tail', Profile(ww, (ww,))),
        ('Constant omega^omega', Profile(ww + ONE)),
    ]
    for title, p in examples:
        print(title)
        print(' ', p)
        print('  S =', p.lipparini_S())
        print('  N =', p.value())
        print()

if __name__ == '__main__':
    main()
