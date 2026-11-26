"""Enclose n-th zeta zero ordinates in cells [a,a+1]/10^22 with FLINT."""
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path
import sys
from flint import acb, ctx

DIGITS = 22
COUNT = 18000
BLOCK = 75

def get_block(start):
    ctx.prec = 125
    ans = []
    for zero in acb.zeta_zeros(start, min(BLOCK, COUNT - start + 1)):
        assert zero.real == 0.5
        # A unique value of the floor in ball arithmetic encloses the true ordinate.
        cell = (zero.imag * 10**DIGITS).floor().unique_fmpz()
        assert cell is not None
        ans.append(str(cell))
    return ans

if __name__ == '__main__':
    first = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    with ProcessPoolExecutor(5) as pool:
        blocks = pool.map(get_block, range(first, COUNT + 1, BLOCK))
        with Path(__file__).with_name('zero_cells.txt').open('w' if first == 1 else 'a') as f:
            for block in blocks:
                f.write('\n'.join(block) + '\n')
                f.flush()
