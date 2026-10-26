from pathlib import Path
import difflib, json, hashlib, re
ROOT=Path(__file__).resolve().parent
SRC=ROOT.parent/'sources/Computability/DiophantineConsistency/Lean/DiophantineConsistency'
changes={
'WangTiles942TraceCycle.lean':[
('''  rw [cycleTile_north,cycleTile_south]
  by_cases h0 : k.val = 0
  · have hn : (nextIndex (by omega) k).val = 1 := by
      rw [nextIndex_val_of_lt (by omega) k (by omega),h0]
    simp only [h0,hn,Nat.one_ne_zero,↓reduceIte,show 1+1 ≠ H by omega]
  · by_cases hlast : k.val+1 = H
    · have hn := nextIndex_val_of_last (by omega) k hlast
      simp only [h0,hlast,hn,↓reduceIte]
    · have hn := nextIndex_val_of_lt (by omega) k (by have hk := k.isLt; omega)
      have hn0 : k.val+1 ≠ 0 := by omega
      by_cases hfinish : k.val+2 = H
      · simp only [h0,hlast,hfinish,hn,hn0,↓reduceIte]
      · simp only [h0,hlast,hfinish,hn,hn0,↓reduceIte]
''',
'''  rw [cycleTile_north,cycleTile_south]
  by_cases hlast : k.val+1 = H
  · rw [nextIndex_val_of_last (by omega) k hlast]
    simp only [if_pos rfl,if_neg (show k.val ≠ 0 by omega),if_pos hlast]
  · rw [nextIndex_val_of_lt (by omega) k (by have hk := k.isLt; omega)]
    have hsucc : k.val+1 ≠ 0 := by omega
    by_cases h0 : k.val = 0
    · simp only [h0,hsucc,hlast,Nat.zero_add,↓reduceIte,show 2 ≠ H by omega]
    · simp only [h0,hsucc,hlast,↓reduceIte,Nat.add_assoc]
''')],
'WangTiles942FinishConstruction.lean':[
('''theorem passTile_allowed (cfg : Config 215) (hh : cfg.state = none) (x : ℤ) :
    Allowed (passTile cfg x) := by
  unfold passTile
  by_cases hx : x = cfg.head
  · subst x
    rw [color_at_head,hh,halted_head_color]
    exact Allowed.pass (1 : Fin 2)
      ⟨(Tape.read cfg.tape cfg.head).toNat, by have h := bit_le_one (Tape.read cfg.tape cfg.head); omega⟩
  · rw [color_of_ne_head cfg x hx]
    simpa only [Fin.val_zero, Nat.mul_zero, zero_add] using
      Allowed.pass (0 : Fin 2)
        ⟨(Tape.read cfg.tape x).toNat, by have h := bit_le_one (Tape.read cfg.tape x); omega⟩

theorem finishTile_allowed (cfg : Config 215) (hh : cfg.state = none) (x : ℤ) :
    Allowed (finishTile cfg x) := by
  unfold finishTile
  by_cases hx : x = cfg.head
  · subst x
    rw [color_at_head,hh,halted_head_color]
    exact Allowed.finish (1 : Fin 2)
      ⟨(Tape.read cfg.tape cfg.head).toNat, by have h := bit_le_one (Tape.read cfg.tape cfg.head); omega⟩
  · rw [color_of_ne_head cfg x hx]
    simpa only [Fin.val_zero, Nat.mul_zero, zero_add] using
      Allowed.finish (0 : Fin 2)
        ⟨(Tape.read cfg.tape x).toNat, by have h := bit_le_one (Tape.read cfg.tape x); omega⟩
''',
'''/-- The halted color is derived once for the two literal closing constructors. -/
private theorem halted_tiles_allowed (cfg : Config 215) (hh : cfg.state = none) (x : ℤ) :
    Allowed (passTile cfg x) ∧ Allowed (finishTile cfg x) := by
  let b : Fin 2 := ⟨(Tape.read cfg.tape x).toNat, by
    have h := bit_le_one (Tape.read cfg.tape x); omega⟩
  simp only [passTile,finishTile,color,hh,halted_head_color]
  split_ifs
  · exact ⟨Allowed.pass (1 : Fin 2) b,Allowed.finish (1 : Fin 2) b⟩
  · simpa only [Fin.val_zero,Nat.mul_zero,zero_add] using
      And.intro (Allowed.pass (0 : Fin 2) b) (Allowed.finish (0 : Fin 2) b)

theorem passTile_allowed (cfg : Config 215) (hh : cfg.state = none) (x : ℤ) :
    Allowed (passTile cfg x) := (halted_tiles_allowed cfg hh x).1

theorem finishTile_allowed (cfg : Config 215) (hh : cfg.state = none) (x : ℤ) :
    Allowed (finishTile cfg x) := (halted_tiles_allowed cfg hh x).2
''')]
}

def count(s):
 return {'physical_lines':len(s.splitlines()),'nonblank_lines':sum(bool(t.strip()) for t in s.splitlines()),'bytes':len(s.encode()),'by_cases':len(re.findall(r'\bby_cases\b',s)),'split_ifs':len(re.findall(r'\bsplit_ifs\b',s))}
rows=[]
for name, replacements in changes.items():
 old=(SRC/name).read_text(); new=old
 for before,after in replacements:
  assert new.count(before)==1,(name,new.count(before))
  new=new.replace(before,after)
 (ROOT/'candidate'/name).write_text(new)
 relative='Computability/DiophantineConsistency/Lean/DiophantineConsistency/'+name
 (ROOT/'patches'/(name+'.patch')).write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+relative,tofile='b/'+relative)))
 rows.append({'file':name,'source':count(old),'candidate':count(new),'removed_physical_lines':len(old.splitlines())-len(new.splitlines()),'source_sha256':hashlib.sha256(old.encode()).hexdigest(),'candidate_sha256':hashlib.sha256(new.encode()).hexdigest(),'status':'source-derived; NOT LEAN COMPILED; no original definition or public theorem statement edited'})
(ROOT/'validation/metrics.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(rows,indent=2))
