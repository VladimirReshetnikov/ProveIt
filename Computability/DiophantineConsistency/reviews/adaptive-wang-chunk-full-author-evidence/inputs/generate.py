"""Generate an isolated complete chunked Wang-table predicate draft."""
from pathlib import Path
import hashlib,json,os
root=Path(__file__).resolve().parents[2];src=root/'Lean/DiophantineConsistency/ArithmeticWangTable.lean';base=Path(os.environ.get('WANG_CHUNK_FULL_SRC','/tmp/adaptive-wang-chunk-full-src'));out=base/'DiophantineConsistency';raw=src.read_bytes()
if hashlib.sha256(raw).hexdigest()!='8bf620443a3ed74892efba1aeaa6f8c14add5feaff4954dda001a6acf5e36ff2':raise RuntimeError('WangTable source pin changed')
s=raw.decode();key='theorem rows_goodA :'
if s.count(key)!=1:raise RuntimeError('unexpected source marker')
out.mkdir(parents=True,exist_ok=True);(out/'ArithmeticWangTableChunkCore.lean').write_text(s[:s.index(key)]+'end DiophantineConsistency.ArithmeticWangTable\n')
names=[]
for kind in 'ABC':
 for i in range(8):
  name=f'ArithmeticWangTableChunk{kind}{i}';names.append(name)
  segment='orderedRows.take 128' if i==0 else (f'(orderedRows.drop {128*i}).take 128' if i<7 else 'orderedRows.drop 896')
  t=f'''import DiophantineConsistency.ArithmeticWangTableChunkCore
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace DiophantineConsistency.ArithmeticWangTable
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open WangTiles942
/-- One finite chunk of the original Good{kind} predicate. -/
theorem rows_good{kind}_chunk{i} : ∀ row ∈ {segment}, Good{kind} row.2 := by decide +kernel
end DiophantineConsistency.ArithmeticWangTable
''';(out/f'{name}.lean').write_text(t)
lines=[*(f'import DiophantineConsistency.{n}' for n in names),'','set_option autoImplicit false','set_option Elab.async false','namespace DiophantineConsistency.ArithmeticWangTable','open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC','open WangTiles942','','private theorem combine {α : Type*} (P : α → Prop) (xs : List α)','    (hfirst : ∀ x ∈ xs.take 128, P x) (hrest : ∀ x ∈ xs.drop 128, P x) :','    ∀ x ∈ xs, P x := by','  intro x hx','  have h : x ∈ xs.take 128 ++ xs.drop 128 := by simpa only [List.take_append_drop] using hx','  rcases List.mem_append.mp h with h | h','  · exact hfirst x h','  · exact hrest x h','']
for kind in 'ABC':
 lines += [f'theorem rows_good{kind} : ∀ row ∈ orderedRows, Good{kind} row.2 := by',f'  have h7 : ∀ row ∈ orderedRows.drop 896, Good{kind} row.2 := rows_good{kind}_chunk7']
 for i in range(6,0,-1):
  start=128*i;lines += [f'  have h{i} : ∀ row ∈ orderedRows.drop {start}, Good{kind} row.2 := by',f'    apply combine (fun row => Good{kind} row.2) (orderedRows.drop {start})',f'    · exact rows_good{kind}_chunk{i}',f'    · simpa only [List.drop_drop, Nat.reduceAdd] using h{i+1}']
 lines += [f'  apply combine (fun row => Good{kind} row.2) orderedRows',f'  · exact rows_good{kind}_chunk0',f'  · exact h1','']
lines += ['end DiophantineConsistency.ArithmeticWangTable',''];(out/'ArithmeticWangTableChunkFacts.lean').write_text('\n'.join(lines));(base/'generation.json').write_text(json.dumps({'original':str(src),'original_sha256':hashlib.sha256(raw).hexdigest(),'prefix_end':'before theorem rows_goodA','ranges':'take 128, then drop 128*i take 128 for i=1..6, then drop 896','scope':'exploratory full finite-predicate chunks and take/drop assembly; no original WangTable rebuild or interface comparison'},indent=2)+'\n');(base/'original-snapshot.lean').write_bytes(raw)
