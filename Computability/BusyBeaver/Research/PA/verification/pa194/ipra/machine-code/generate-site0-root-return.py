from pathlib import Path
rows=[tuple(map(int,s.split(','))) for s in Path('/dev/shm/pa194-site28-work/site33-rows.csv').read_text().splitlines()]
q,l=17,16;bits=[0,0]; trace=[]
for i in range(100):
 if q==24 and i:break
 assert bits
 old=bits[:];bit=bits.pop(0);w,d,nq=rows[2*q+bit];oldl=l
 if d==1:l=2*l+w
 else:
  low=l%2;l//=2;bits=[low,w]+bits
 trace.append((q,oldl,old,bit,w,d,nq,l,bits[:]))
 q=nq
assert (q,l,bits)==(24,1,[0,0,0,0,0,0]) and len(trace)==22
def bs(xs):return '['+','.join('true' if x else 'false' for x in xs)+']'
header='''import PA194Site30Jump
import PA194Site32PositivePath
import PA194LeftRows
import PA194LeftOneRows
import PA194LeftOneWriteOne
import PA194RightRows
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 12000000
namespace PA194Site0RootReturn
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes TableDispatch PA194Path27Header PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194BinaryDouble PA194LeftRows PA194LeftOneRows PA194LeftOneWriteOne PA194RightRows PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
'''
out=[header]
for i,(q,l,old,bit,w,d,nq,nl,new) in enumerate(trace):
 rem=old[1:]; yin='y+y+1' if bit else 'y+y'
 out.append(f'''theorem row{i} (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M {q},F pairCode ![modelNumeral M {l},modelWord {bs(old)} x]]) =
    F pairCode ![modelNumeral M {nq},F pairCode ![modelNumeral M {nl},modelWord {bs(new)} x]] := by
  let y := modelWord {bs(rem)} x
''')
 if d==1:
  out.append(f'''  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M {q},F pairCode ![modelNumeral M {l},{yin}]]) =
    F pairCode ![modelNumeral M {nq},F pairCode ![modelNumeral M {nl},y]]
  have h := {'rightOne' if bit else 'rightZero'} {q} {w} {nq} (by decide) (by decide +kernel) (modelNumeral M {l}) y
  have hn : modelNumeral M {l}+modelNumeral M {l}+modelNumeral M {w} = modelNumeral M {nl} := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
''')
 else:
  b0=oldl=l # unused
  inner='y+y+1' if w else 'y+y'
  right=f'({inner})+({inner})'+('+1' if (trace[i][1]%2) else '')
  out.append(f'''  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M {q},F pairCode ![modelNumeral M {trace[i][1]},{yin}]]) =
    F pairCode ![modelNumeral M {nq},F pairCode ![modelNumeral M {nl},{right}]]
''')
  meth='leftZero' if bit==0 else ('leftOneWriteOne' if w==1 else 'leftOne')
  out.append(f'  have h := {meth} {q} {nq} (by decide) (by decide +kernel) (modelNumeral M {trace[i][1]}) y\n')
  odd=trace[i][1]%2
  if odd:
   out.append(f'''  have hn : modelNumeral M {trace[i][1]} = modelNumeral M {nl}+modelNumeral M {nl}+1 := by
    rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M {trace[i][1]}) = (1 : M) := by rw [hn,(modelOdd (modelNumeral M {nl})).1]
  have hh : F halfCode (fun _ => modelNumeral M {trace[i][1]}) = modelNumeral M {nl} := by rw [hn,(modelOdd (modelNumeral M {nl})).2]
''')
  else:
   out.append(f'''  have hn : modelNumeral M {trace[i][1]} = modelNumeral M {nl}+modelNumeral M {nl} := by rw [←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M {trace[i][1]}) = (0 : M) := by rw [hn,(modelDouble (modelNumeral M {nl})).1]
  have hh : F halfCode (fun _ => modelNumeral M {trace[i][1]}) = modelNumeral M {nl} := by rw [hn,(modelDouble (modelNumeral M {nl})).2] <;> simp only [show modelNumeral M 0 = (0 : M) from rfl,zero_add]
''')
  out.append('  rw [hp,hh] at h\n  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h\n')
out.append(f'''theorem returnWord (x : M) :
    F PA194Stepper.stepper ![modelNumeral M 22,F pairCode ![modelNumeral M 17,F pairCode ![modelNumeral M 16,modelWord {bs(trace[0][2])} x]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![modelNumeral M 1,modelWord {bs(trace[-1][-1])} x]] := by
  rw [PA194Site30Jump.standardRunCorrect]
  simp only [PA194Site30Jump.standardRun]
  rw [{','.join(f'row{i}' for i in range(len(trace)))}]
#print axioms returnWord
end models
end PA194Site0RootReturn
''')
Path('/dev/shm/pa194-site28-work/PA194Site0RootReturn.lean').write_text(''.join(out))
