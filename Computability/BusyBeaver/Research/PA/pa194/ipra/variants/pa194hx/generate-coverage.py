"""Generate sequential, kernel-reduced HX finite source coverage chunks."""
from pathlib import Path
import sys
out = Path(sys.argv[1])
out.mkdir(parents=True, exist_ok=True)
pieces = [(start, min(start + 64, 3673)) for start in range(32, 3673, 64)]
for idx, (start, end) in enumerate(pieces):
    name = f'PA194HXCoverage{idx:02}'
    lines = ['import PA194HXCoverageFirstSound', 'set_option autoImplicit false',
             'set_option maxRecDepth 65536', 'set_option maxHeartbeats 0',
             f'namespace {name}']
    blocks = [(j, min(8, end-j)) for j in range(start, end, 8)]
    for base, count in blocks:
        lines.append(f'theorem block{base} : PA194HXCoverageFirst.blockCheck {base} {count} = true := by decide +kernel')
    lines += ['', f'theorem checked (i : Nat) (lo : {start} ≤ i) (hi : i < {end}) :',
              '    PA194HXContracts.checkAt i = true := by']
    for k, (base, count) in enumerate(blocks):
        call = f'PA194HXCoverageFirstSound.block_sound {base} {count} i block{base} (by omega) (by omega)'
        if k < len(blocks) - 1:
            lines += [f'  by_cases e{base} : i < {base+count}', f'  · exact {call}']
        else:
            lines += [f'  exact {call}']
    lines += ['', '#print axioms checked', f'end {name}']
    (out / f'{name}.lean').write_text('\n'.join(lines) + '\n')
imports = ['import PA194HXCoverageFirstSound'] + [f'import PA194HXCoverage{idx:02}' for idx in range(len(pieces))]
lines = imports + ['', 'set_option autoImplicit false', 'set_option maxRecDepth 65536',
                   'namespace PA194HXCoverageAll',
                   'theorem checked (i : Nat) (hi : i < 3673) : PA194HXContracts.checkAt i = true := by',
                   '  by_cases h32 : i < 32',
                   '  · exact PA194HXCoverageFirstSound.allFirst i h32']
for idx, (start, end) in enumerate(pieces):
    call = f'PA194HXCoverage{idx:02}.checked i (by omega) (by omega)'
    if idx < len(pieces) - 1:
        lines += [f'  by_cases h{end} : i < {end}', f'  · exact {call}']
    else:
        lines += [f'  exact {call}']
lines += ['', 'theorem contracts (i : Nat) (hi : i < 3673) :',
          '    ∃ code, M6.Source.resolveAt PA194SourceProgram.sites i = some code ∧',
          '      PA194HXContractSound.Contracts i code :=',
          '  PA194HXContractSound.atSite i (checked i hi)',
          '#print axioms checked', '#print axioms contracts', 'end PA194HXCoverageAll']
(out / 'PA194HXCoverageAll.lean').write_text('\n'.join(lines) + '\n')
print(f'Generated {len(pieces)} chunks, covering 32–3672 inclusive.')
