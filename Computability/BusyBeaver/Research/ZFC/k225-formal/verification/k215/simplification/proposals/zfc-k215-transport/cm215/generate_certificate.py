#!/usr/bin/env python3
"""Generate bounded Lean kernel checks for exact native K215/CM215 tables."""
from pathlib import Path
import argparse,json,hashlib
from table_data import PIN,HASHES,parse,array

def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--inputs',type=Path,default=Path(__file__).resolve().parent/'inputs')
 p.add_argument('--out',type=Path,default=Path(__file__).resolve().parent/'lean')
 p.add_argument('--chunk-size',type=int,default=16)
 a=p.parse_args();a.out.mkdir(parents=True,exist_ok=True)
 old=parse(a.inputs/'k215.native.tm'); new=parse(a.inputs/'marker215.native.tm')
 base='''import FiniteMarkerCertificate
namespace CM215Certificate
open MarkerTransport
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
'''+array('parent',old)+'\n'+array('marker',new)+'''
def stateCheck (q : State) : Bool :=
  FiniteMarkerCertificate.checkRow parentTable markerTable q false &&
  FiniteMarkerCertificate.checkRow parentTable markerTable q true

def liveCount (table : Table) (qs : List State) : Nat :=
  (qs.filter fun q => (table q false).isSome).length

def changes (qs : List State) : Nat :=
  (qs.flatMap fun q => [false, true].filter fun b =>
    decide (parentTable q b ≠ markerTable q b)).length

theorem liveCount_append (t : Table) (a b : List State) :
    liveCount t (a ++ b) = liveCount t a + liveCount t b := by
  simp [liveCount, List.filter_append]

theorem changes_append (a b : List State) : changes (a ++ b) = changes a + changes b := by
  simp [changes, List.flatMap_append]
'''
 chunks=[list(range(i,min(303,i+a.chunk_size))) for i in range(0,303,a.chunk_size)]
 for i,qs in enumerate(chunks):base+=f'\ndef chunk{i:02} : List State := ['+', '.join(map(str,qs))+']\n'
 join=' ++ '.join(f'chunk{i:02}' for i in range(len(chunks)))
 base+='\ntheorem partition : List.finRange 303 = '+join+' := by decide\nend CM215Certificate\n'
 (a.out/'CM215Tables.lean').write_text(base)
 for i,qs in enumerate(chunks):
  oc=sum((q,0) in old for q in qs); nc=sum((q,0) in new for q in qs)
  ch=sum(old.get((q,b))!=new.get((q,b)) for q in qs for b in (0,1))
  s=f'''import CM215Tables
namespace CM215Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
 theorem check{i:02} : chunk{i:02}.all stateCheck = true := by decide +kernel
 theorem oldCount{i:02} : liveCount parentTable chunk{i:02} = {oc} := by decide +kernel
 theorem newCount{i:02} : liveCount markerTable chunk{i:02} = {nc} := by decide +kernel
 theorem changed{i:02} : changes chunk{i:02} = {ch} := by decide +kernel
end CM215Certificate
'''
  (a.out/f'CM215Check{i:02}.lean').write_text(s)
 imports='\n'.join(f'import CM215Check{i:02}' for i in range(len(chunks)))
 checks=', '.join(f'check{i:02}' for i in range(len(chunks)))
 olds=', '.join(f'oldCount{i:02}' for i in range(len(chunks)))
 news=', '.join(f'newCount{i:02}' for i in range(len(chunks)))
 changes=', '.join(f'changed{i:02}' for i in range(len(chunks)))
 facade=imports+'''
namespace CM215Certificate
open MarkerTransport
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem table_check : FiniteMarkerCertificate.check parentTable markerTable = true := by
  change (List.finRange 303).all stateCheck = true
  rw [partition]
  simp only [List.all_append, '''+checks+''', Bool.and_self]

theorem localRows : FiniteMarkerCertificate.LocalRows parentTable markerTable where
  old52zero := rfl
  old52one := rfl
  old176zero := rfl
  old176one := rfl
  new52zero := rfl
  new52one := rfl
  new176zero := rfl
  new176one := rfl
  new185zero := rfl
  new129zero := rfl

theorem certificate : Certificate parentTable markerTable :=
  FiniteMarkerCertificate.certificate _ _ table_check localRows

theorem all_tape_halts_iff (h : Int) (t : Tape) :
    PositiveStuttering.Halts (step parentTable) ⟨0, h, t⟩ ↔
    PositiveStuttering.Halts (step markerTable) ⟨0, h, t⟩ :=
  MarkerTransport.all_tape_halts_iff certificate h t

theorem blank_halts_iff :
    PositiveStuttering.Halts (step parentTable) ⟨0, 0, fun _ => false⟩ ↔
    PositiveStuttering.Halts (step markerTable) ⟨0, 0, fun _ => false⟩ :=
  all_tape_halts_iff _ _

theorem parent_working_states : liveCount parentTable (List.finRange 303) = 215 := by
  rw [partition]
  simp only [liveCount_append, '''+olds+''']

theorem marker_working_states : liveCount markerTable (List.finRange 303) = 215 := by
  rw [partition]
  simp only [liveCount_append, '''+news+''']

theorem exactly_six_changed_rows : changes (List.finRange 303) = 6 := by
  rw [partition]
  simp only [changes_append, '''+changes+''']

#print axioms table_check
#print axioms certificate
#print axioms all_tape_halts_iff
#print axioms blank_halts_iff
#print axioms parent_working_states
#print axioms marker_working_states
#print axioms exactly_six_changed_rows
end CM215Certificate
'''
 (a.out/'CM215Certificate.lean').write_text(facade)
 files={x.name:hashlib.sha256(x.read_bytes()).hexdigest() for x in sorted(a.out.glob('CM215*.lean'))}
 receipt={'repository_pin':PIN,'input_sha256':HASHES,'chunk_size':a.chunk_size,'chunks':len(chunks),'files':files,'kernel_validation':'generation only; run build_lean.py'}
 (a.out/'generation.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps({'chunks':len(chunks),'modules':len(files)}))
if __name__=='__main__':main()
