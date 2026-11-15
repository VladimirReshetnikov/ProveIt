#!/usr/bin/env python3
"""Generate kernel-computed PA194 source-resolution blocks and aggregator."""
from pathlib import Path
import sys
if len(sys.argv) != 2:
    raise SystemExit('usage: generate-resolution.py OUTPUT_DIR')
out = Path(sys.argv[1])
out.mkdir(parents=True,exist_ok=True)
blocks = [(base,min(250,3673-base)) for base in range(0,3673,250)]
for base,count in blocks:
    name=f'PA194Resolve_{base:04d}_{base+count:04d}'
    (out/(name+'.lean')).write_text(f'''import PA194ResolveCheck
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace {name}
theorem verified : PA194ResolveCheck.check {base} {count} = true := by decide +kernel
#print axioms verified
end {name}
''')
lines=['import PA194SourceNoMalformed'] + [f'import PA194Resolve_{b:04d}_{b+c:04d}' for b,c in blocks]
lines += ['set_option maxRecDepth 10000','set_option maxHeartbeats 8000000','namespace PA194ResolvedComplete',
          'theorem allResolved : PA194SourceNoMalformed.AllResolved := by', '  intro i hi']
for idx,(base,count) in enumerate(blocks):
    indent='  '+'  '*idx
    if idx < len(blocks)-1:
        lines.append(f'{indent}by_cases h{idx} : i < {base+count}')
        lines.append(f'{indent}· exact PA194ResolveCheck.block_sound PA194Resolve_{base:04d}_{base+count:04d}.verified (by omega) (by omega)')
        lines.append(f'{indent}·')
    else:
        lines.append(f'{indent}exact PA194ResolveCheck.block_sound PA194Resolve_{base:04d}_{base+count:04d}.verified (by omega) (by omega)')
lines += ['#print axioms allResolved','end PA194ResolvedComplete','']
(out/'PA194ResolvedComplete.lean').write_text('\n'.join(lines))
print('generated',len(blocks),'resolution blocks and aggregator')
