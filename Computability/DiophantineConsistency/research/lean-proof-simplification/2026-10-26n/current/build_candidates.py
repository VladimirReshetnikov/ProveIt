from pathlib import Path
import json, hashlib, difflib
BASE=Path(__file__).resolve().parent.parent
SRC=BASE/'sources/Computability/DiophantineConsistency/Lean/DiophantineConsistency'
OUT=BASE/'current'
PIN='b310142330df89e48413c8fce62e7de223e1c7d5'
entries=[]
def declaration(module,name):
    s=(SRC/(module+'.lean')).read_text()
    a=s.index('theorem '+name+' ')
    b=s.index(':= by',a)+len(':= by')
    e=s.index('\n\n',b)
    return s,a,b,e

def add(module,name,body,label):
    s,a,b,e=declaration(module,name)
    header=s[a:b].replace('theorem '+name+' ','theorem '+name+'_candidate ',1)
    proof='\n'+body.strip('\n')
    original=s[b:e]
    row=dict(id=label,module=module,original=name,candidate=name+'_candidate',source_line=s[:a].count('\n')+1,
             source_end_line=s[:e].count('\n')+1,original_proof_nonblank_lines=sum(bool(x.strip()) for x in original.splitlines()),
             candidate_proof_nonblank_lines=sum(bool(x.strip()) for x in proof.splitlines()),
             original_declaration_nonblank_lines=sum(bool(x.strip()) for x in s[a:e].splitlines()),
             candidate_declaration_nonblank_lines=sum(bool(x.strip()) for x in (header+proof).splitlines()),
             url=f'https://github.com/VladimirReshetnikov/ProveIt/blob/{PIN}/Computability/DiophantineConsistency/Lean/DiophantineConsistency/{module}.lean#L{s[:a].count(chr(10))+1}',
             original_proof=original,candidate_proof=proof,header=header)
    entries.append(row)
    return header+proof+'\n'

prelude='''import DiophantineConsistency.CurrentSouthShift2011
import DiophantineConsistency.CurrentTileColors2011
import DiophantineConsistency.CurrentOccupation2011
import DiophantineConsistency.CurrentCellCycle2011

/-!
# Review-only simplification candidates, pinned to b310142330df89e48413c8fce62e7de223e1c7d5

UNCOMPILED: no Lean runtime was available. This file is a proposal, not a
verified patch. It imports the original modules and places alternative
proofs under fresh names; the repository snapshot is not changed.

C1 uses an API already called in NativeSelectorClause54.selectors_one.
C2 needs only the existing binaryWord_prefix; the two private helpers below
repeat helpers already in CurrentSouthShift2011, because private names are
not a public import interface. They add no helpers to the intended patch.
C3 moves the existing binaryWord_congr to CurrentCellLabels2011; this
standalone candidate instead refers to its current namespace.
C4 reorders propagate_from before propagate in the intended patch.
-/

namespace DiophantineConsistency.Round2Current

open CurrentCellLabels2011 CurrentSouthShift2011 CurrentCellTranslation2011
  CurrentAdjacency2011 CurrentOccupation2011 CurrentCellCycle2011
open scoped BigOperators

'''
text=prelude
text+=add('CurrentCellLabels2011','sum_le_one_cases','''  classical
  by_cases hz : ∀ i, f i = 0
  · exact Or.inl hz
  · push_neg at hz
    obtain ⟨i, hi⟩ := hz
    have hs := Finset.sum_le_one_iff.mp hf
    refine Or.inr ⟨i, (hs i i (Finset.mem_univ i) (Finset.mem_univ i) hi hi).2, ?_⟩
    intro j hji
    by_contra hj
    exact hji (hs j i (Finset.mem_univ j) (Finset.mem_univ i) hj hi).1''','C1')
text+='''
private theorem binaryWord_one (f : ℕ → ℕ) : binaryWord f 1 = f 0 := by
  simp [binaryWord]

private theorem binaryWord_two (f : ℕ → ℕ) : binaryWord f 2 = f 0 + 2 * f 1 := by
  simp [binaryWord, Finset.sum_range_succ]

variable {N : ℕ} [NeZero (N * 2011)]

'''
for offset,k,n in [(19,1,8),(20,2,7)]:
    a=960-offset
    text+=add('CurrentSouthShift2011',f'offset{offset}_word',f'''  rw [copy_word_translation c t {a} b (by omega) hcopy]
  simpa only [southWord, binaryWord_{'one' if k==1 else 'two'}, ← Nat.add_assoc,
    Nat.reduceAdd, Nat.reducePow, Nat.add_zero, Nat.cast_ofNat] using
    (binaryWord_prefix
      (fun j => c (((theta t b : Cell N) : ZMod (N * 2011)) +
        (({a} + j : ℕ) : ZMod (N * 2011)))) {k} {n} (fun j _ => hc _))''','C2')+'\n'
text+=add('CurrentSouthShift2011','copy_word_translation','''  unfold southWord
  apply CurrentTileColors2011.binaryWord_congr
  intro j hj
  have hs := source_eq_of_remainder_le b t (960+j) (by omega)
  rw [show 960+j-t%2011 = a+j by omega] at hs
  exact (hcopy ⟨j, hj⟩).trans (congrArg c hs)''','C3')+'\n'
text+='omit [NeZero (N * 2011)] in\n'
text+=add('CurrentOccupation2011','horizontal_words','''  exact CurrentTileColors2011.binaryWord_congr _ _ 8
    (fun j hj => hbits ⟨j, hj⟩)''','C3')+'\n'
text+=add('CurrentCellCycle2011','propagate','''  exact propagate_from P 0 hzero hnext''','C4')
text+='\nend DiophantineConsistency.Round2Current\n'
text+='\n-- Candidate axiom audits: execute with the pinned Lean toolchain.\n'
for row in entries:
    text+=f"#print axioms DiophantineConsistency.Round2Current.{row['candidate']}\n"
(OUT/'CurrentSimplificationCandidates.lean').write_text(text)
public=[]
for x in entries:
    y={k:v for k,v in x.items() if k not in ['original_proof','candidate_proof','header']}
    y['saving_nonblank_proof_lines']=x['original_proof_nonblank_lines']-x['candidate_proof_nonblank_lines']
    p=SRC/(x['module']+'.lean'); data=p.read_bytes()
    y['source_sha256']=hashlib.sha256(data).hexdigest()
    y['git_blob_sha1']=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
    public.append(y)
(OUT/'candidate_metrics.json').write_text(json.dumps({'pin':PIN,'status':'UNCOMPILED','counting_rule':'Nonblank physical lines after := by; declaration totals include headers; no formatter applied. Counts are draft text, not kernel/performance metrics.','candidates':public},ensure_ascii=False,indent=2)+'\n')
# The source bodies are supplied verbatim to make proposal review reproducible.
(OUT/'proof_comparison.txt').write_text('\n\n'.join(f"{x['id']}: {x['module']}.{x['original']}\nBEFORE (verbatim):{x['original_proof']}\nAFTER (uncompiled):{x['candidate_proof']}" for x in entries)+'\n')
print(json.dumps(public,ensure_ascii=False,indent=2))
