"""Generate the first 128-row Wang-table split pilot from a pinned source."""
from pathlib import Path
import hashlib,json,os
root=Path(__file__).resolve().parents[2]
src=root/'Lean/DiophantineConsistency/ArithmeticWangTable.lean'
base=Path(os.environ.get('WANG_CHUNK_SRC','/tmp/adaptive-wang-chunk-pilot-src'))
out=base/'DiophantineConsistency'
raw=src.read_bytes()
if hashlib.sha256(raw).hexdigest()!='8bf620443a3ed74892efba1aeaa6f8c14add5feaff4954dda001a6acf5e36ff2':
 raise RuntimeError('WangTable source pin changed')
s=raw.decode();key='theorem rows_goodA :'
if s.count(key)!=1:raise RuntimeError('unexpected source marker')
out.mkdir(parents=True,exist_ok=True)
(out/'ArithmeticWangTableChunkCore.lean').write_text(s[:s.index(key)]+'end DiophantineConsistency.ArithmeticWangTable\n')
for kind in 'ABC':
 t=f'''import DiophantineConsistency.ArithmeticWangTableChunkCore
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace DiophantineConsistency.ArithmeticWangTable
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open WangTiles942
/-- Exploratory first 128-row chunk of the original Good{kind} predicate. -/
theorem rows_good{kind}_chunk0 : ∀ row ∈ orderedRows.take 128, Good{kind} row.2 := by decide +kernel
end DiophantineConsistency.ArithmeticWangTable
'''
 (out/f'ArithmeticWangTableChunk{kind}0.lean').write_text(t)
(base/'generation.json').write_text(json.dumps({'original':str(src),'original_sha256':hashlib.sha256(raw).hexdigest(),'prefix_end':'before theorem rows_goodA','chunk_range':'orderedRows.take 128','scope':'exploratory three-chunk pilot; no full coverage, interface comparison or current WangTable build'},indent=2)+'\n')
(base/'original-snapshot.lean').write_bytes(raw)
