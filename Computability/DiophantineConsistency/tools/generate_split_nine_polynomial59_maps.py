#!/usr/bin/env python3
"""Regenerate finite coefficient-map proofs from the checked kernel table.

This reads inert Lean expression text, not executable upstream code. The
emitted finite-case proofs are checked by Lean against the coefficient table.
"""
from pathlib import Path
import hashlib
import re

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'Lean/DiophantineConsistency/SplitKernelData59.lean'
OUTPUT = ROOT / 'Lean/DiophantineConsistency/SplitNinePolynomial59.lean'
START = '-- BEGIN GENERATED COEFFICIENT MAPS\n'
END = '-- END GENERATED COEFFICIENT MAPS\n'


def generate() -> str:
    source = DATA.read_text()
    blocks = [f'-- Kernel table SHA256 {hashlib.sha256(DATA.read_bytes()).hexdigest()}.',
              'set_option linter.unusedSimpArgs false in']
    # Each expression occupies one comma-separated line in the checked table.
    for layer, count in enumerate((7, 39, 43)):
        found = re.search(rf'def coefficients{layer} .*? := !\[(.*?)\]\n', source, re.S)
        if found is None:
            raise ValueError(f'coefficient layer {layer} not found')
        expressions = [part.strip() for part in found.group(1).split(',')]
        if len(expressions) != count:
            raise ValueError((layer, len(expressions), count))
        if layer:
            blocks.append('set_option linter.unusedSimpArgs false in')
        blocks.extend([
            f'theorem map_coefficients{layer} (f : A →+* B) (ports : Fin 4 → A) (i : Fin {count}) :',
            f'    f (coefficients{layer} ports i)=coefficients{layer} (fun j => f (ports j)) i := by',
            f'  fin_cases i <;> dsimp only [coefficients{layer}, Fin.reduceFinMk, Matrix.cons_val]',
            '  all_goals simp only [map_neg, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one, map_zero]'])
        blocks.append('')
    return '\n'.join(blocks).rstrip() + '\n'


def main() -> None:
    content = OUTPUT.read_text()
    before, rest = content.split(START, 1)
    _, after = rest.split(END, 1)
    OUTPUT.write_text(before + START + generate() + END + after)


if __name__ == '__main__':
    main()
