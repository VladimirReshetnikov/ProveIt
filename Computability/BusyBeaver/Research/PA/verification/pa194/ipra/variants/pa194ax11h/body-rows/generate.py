#!/usr/bin/env python3
"""Generate deterministic bounded source-row certificates and their aggregate."""
import sys
from pathlib import Path
root = Path(sys.argv[1])
root.mkdir(parents=True, exist_ok=True)
for block in range(28):
    start = 50 + 128 * block
    count = min(128, 3519 - start)
    name = f'PA194AX11HBodyRows{block:03d}'
    (root / f'{name}.lean').write_text(f'''import PA194AX11HBodyRowCommon
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace {name}
open PA194AX11HBodyRowCommon

theorem same : newChunk {start} {count} = oldChunk {start} {count} := by decide +kernel
#print axioms same
end {name}
''', encoding='utf-8')
s = ''.join(f'import PA194AX11HBodyRows{i:03d}\n' for i in range(28))
s += '''set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194AX11HBodyRowsAll
open PA194AX11HBodyRowCommon PA194AX11HBodyCopy

theorem agreement : BodyRowsAgree := by
  intro i hlo hhi
'''
for i in range(28):
    start = 50 + 128 * i
    count = min(128, 3519 - start)
    if i < 27:
        s += f'  by_cases h{i:03d} : i < {start+count}\n  ·\n'
    indent = '    ' if i < 27 else '  '
    s += f'{indent}have he : {start} + (i-{start}) = i := by omega\n'
    s += f'{indent}have hc := chunkRow {start} {count} (i-{start}) (by decide) (by omega) PA194AX11HBodyRows{i:03d}.same\n'
    s += f'{indent}simpa only [he,PA194ModelMPDrain.row] using hc\n'
s += '''#print axioms agreement
end PA194AX11HBodyRowsAll
'''
(root / 'PA194AX11HBodyRowsAll.lean').write_text(s, encoding='utf-8')
