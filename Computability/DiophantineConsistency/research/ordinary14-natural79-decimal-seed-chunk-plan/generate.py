#!/usr/bin/env python3
"""Generate inert finite proof proposals; no Lean and no staging."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1];base=D/'research/ordinary14-natural79-decimal-selector-kernel-draft';out=P/'source'
def pin(path,h):
 b=path.read_bytes();assert hashlib.sha256(b).hexdigest()==h,(str(path),hashlib.sha256(b).hexdigest());return b.decode()
seedSrc=pin(base/'PrintedDecimalSeed.lean.src','90412429af931cf76323671d059993b02eef68a11df63e79de91cb01372f305d')
blocksSrc=pin(base/'PrintedDecimalBlocks.lean.src','86252120c4aa90f31c6084b70507e9c67ee7602889daad73df3b0cc84a83eb3d')
pin(base/'DecimalSelectorKernel.lean.src','28ae1b56e9c9b2d83d7457d3fcbf65d0c5effe2f440fe5843ff6e2e649ab3c61')
rowsSrc=pin(D/'Lean/DiophantineConsistency/Compact44/Compact943Data.lean','10a75f23bf358ac745949b9d2717da33c8ccbc4e069892128b913d78d43617f8')
seed=seedSrc.split('def printedSeed : ℕ :=\n  ',1)[1].split('\nend ',1)[0];assert len(seed)==15086 and seed.isdecimal()
text=blocksSrc.split('def printedBlocks : List ℕ := [\n',1)[1].split('\n]',1)[0];assert re.fullmatch(r'[0-9,\s]+',text);blocks=[int(x) for x in text.split(',')];assert len(blocks)==943
part=rowsSrc.split('-- BEGIN PINNED ORDERED ROWS\n',1)[1].split('\n-- END PINNED ORDERED ROWS',1)[0];rows=[]
for line in part.splitlines():
 m=re.fullmatch(r'  \((\d+), (\d+), (\d+), (\d+)\),?',line);assert m;rows.append(tuple(map(int,m.groups())))
assert len(rows)==943
selectors=[1+2**10*(2**41-(a+2**8*b+2**17*c+2**25*d+127*2**34)) for a,b,c,d in rows]
assert selectors==blocks and all(0<=x<10**16 for x in blocks)
# This is an external computation of the printed decimal value, not a Lean proof.
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
number=int(seed);assert number < (10**16)**943
for i,x in enumerate(blocks):assert (number//((10**16)**i))%(10**16)==x
common='''import DecimalSelectorKernel
import DiophantineConsistency.Compact44.RadixWindowReconstruction
import Mathlib.Data.List.GetD

/-! Inert source-only finite proof proposal; no Lean execution. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
namespace Natural79DecimalSeedChunkDraft
open Natural79PrintedDecimalSeedDraft Natural79PrintedDecimalBlocksDraft
open Natural79DecimalSelectorKernelDraft

def selectorAt (n : ℕ) : ℕ :=
  if hn : n < 943 then CompactCoefficientMass.selector (Compact943Data.row ⟨n,hn⟩) else 0

def seedBlockAt (n : ℕ) : ℕ := (printedSeed / (10^16)^n) % (10^16)

/-- Both source numerals are concrete, but these suggested proofs have not
been tried and can have substantial elaboration or kernel costs. -/
theorem printedBlocks_length : printedBlocks.length = 943 := by decide

theorem printedSeed_lt : printedSeed < (10^16)^943 := by decide

end Natural79DecimalSeedChunkDraft
#print axioms Natural79DecimalSeedChunkDraft.printedBlocks_length
#print axioms Natural79DecimalSeedChunkDraft.printedSeed_lt
'''
(out/'DecimalFiniteCommon.lean.src').write_text(common)
chunks=[]
for i,start in enumerate(range(0,943,32)):
 width=min(32,943-start);name=f'DecimalFiniteChunk{i:02d}';theorem=f'chunk{i:02d}'
 code=f'''import DecimalFiniteCommon

/-! Inert source-only suggestion for indices [{start}, {start+width}). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
namespace Natural79DecimalSeedChunkDraft
open Natural79PrintedDecimalBlocksDraft

/-- All {width} proposed equalities are finite; this proof is untested. -/
theorem {theorem} : ∀ i : Fin {width},
    printedBlocks.getD ({start}+i.val) 0 = selectorAt ({start}+i.val) ∧
    printedBlocks.getD ({start}+i.val) 0 = seedBlockAt ({start}+i.val) := by
  decide

end Natural79DecimalSeedChunkDraft
#print axioms Natural79DecimalSeedChunkDraft.{theorem}
'''
 path=out/(name+'.lean.src');path.write_text(code);chunks.append({'index':i,'start':start,'stop':start+width,'module':name,'theorem':theorem,'sha256':hashlib.sha256(code.encode()).hexdigest()})
imports=''.join('import '+x['module']+'\n' for x in chunks)
branches='''  by_cases h00 : n < 32
  · simpa only [Nat.zero_add] using chunk00 ⟨n,h00⟩
'''
for c in chunks[1:-1]:
 i,start,stop=c['index'],c['start'],c['stop']
 branches+=f'''  by_cases h{i:02d} : n < {stop}
  · have hi : n-{start} < {c['stop']-start} := by omega
    have he : {start}+(n-{start}) = n := by omega
    simpa only [he] using chunk{i:02d} ⟨n-{start},hi⟩
'''
c=chunks[-1];start=c['start'];branches+=f'''  have hi : n-{start} < {c['stop']-start} := by omega
  have he : {start}+(n-{start}) = n := by omega
  simpa only [he] using chunk{c['index']:02d} ⟨n-{start},hi⟩
'''
assembly=imports+'''
/-! Inert source-only assembly; no theorem here has been elaborated. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
namespace Natural79DecimalSeedChunkDraft
open Natural79PrintedDecimalSeedDraft Natural79PrintedDecimalBlocksDraft
open Natural79DecimalSelectorKernelDraft

theorem all_blocks (n : ℕ) (hn : n < 943) :
    printedBlocks.getD n 0 = selectorAt n ∧
    printedBlocks.getD n 0 = seedBlockAt n := by
'''+branches+'''
/-- Assemble chunked selector checks into the exact prior hblocks premise. -/
theorem printedBlocks_eq_selectorBlocks : printedBlocks = selectorBlocks := by
  apply List.ext_getElem
  · simpa [selectorBlocks] using printedBlocks_length
  · intro n h₁ h₂
    have hn : n < 943 := by simpa [selectorBlocks] using h₂
    have h := (all_blocks n hn).1
    rw [List.getD_eq_getElem printedBlocks 0 h₁] at h
    simpa [selectorAt, hn, selectorBlocks] using h

/-- Reconstruct the huge seed from checked small digit windows. -/
theorem printedSeed_eq_blocks : printedSeed = Nat.ofDigits (10^16) printedBlocks := by
  symm
  apply RadixWindowReconstruction.ofDigits_eq_of_windows (10^16) (by norm_num)
  · simpa only [printedBlocks_length] using printedSeed_lt
  · intro n hn
    have hn' : n < 943 := by simpa only [printedBlocks_length] using hn
    simpa [seedBlockAt] using (all_blocks n hn').2

/-- Proposed final closed identity; this source has not been Lean checked. -/
theorem printedSeed_eq_symbolicSeed : printedSeed = symbolicSeed :=
  seed_equality_of_finite_checks printedSeed_eq_blocks printedBlocks_eq_selectorBlocks

end Natural79DecimalSeedChunkDraft
#print axioms Natural79DecimalSeedChunkDraft.printedBlocks_eq_selectorBlocks
#print axioms Natural79DecimalSeedChunkDraft.printedSeed_eq_blocks
#print axioms Natural79DecimalSeedChunkDraft.printedSeed_eq_symbolicSeed
'''
(out/'DecimalFiniteAssembly.lean.src').write_text(assembly)
assert chunks[0]['start']==0 and chunks[-1]['stop']==943 and all(a['stop']==b['start'] for a,b in zip(chunks,chunks[1:]))
report={'scope':'external exact finite coverage and arithmetic controls for inert proposed proofs; no Lean or proof claim',
 'block_count':len(blocks),'seed_digits':len(seed),'chunk_count':len(chunks),'max_chunk_width':32,
 'external_selector_matches':len(selectors),'external_seed_window_matches':len(blocks),
 'chunks':chunks,'common_sha256':hashlib.sha256(common.encode()).hexdigest(),'assembly_sha256':hashlib.sha256(assembly.encode()).hexdigest()}
(P/'manifest.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
print(json.dumps({'blocks':len(blocks),'chunks':len(chunks),'external_selector_matches':len(selectors),'external_seed_window_matches':len(blocks),'scope':report['scope']},sort_keys=True,indent=2))
