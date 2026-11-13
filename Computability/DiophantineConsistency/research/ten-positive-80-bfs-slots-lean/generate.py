#!/usr/bin/env python3
"""Transcribe the 41 PDF slot numbers into an explicit Lean kernel formula."""
from pathlib import Path
from hashlib import sha256
import re, subprocess
h=Path(__file__).resolve().parent;pdf=h.parent/'ten-positive-80-bfs-decimal-display/equation.pdf'
if sha256(pdf.read_bytes()).hexdigest()!='412ebf276d1e3d9b2802d333e020a4b7579f2368660bdede31be665564e40fe7':raise ValueError('PDF changed')
r=subprocess.run(['pdftotext','-layout',str(pdf),'-'],capture_output=True,text=True,check=True,timeout=60)
if r.stderr:raise ValueError('extract diagnostics')
part=r.stdout.split('λ = (',1)[1].split(').',1)[0];values=list(map(int,re.findall(r'\d+',part)))
if len(values)!=41:raise ValueError('slot count')
out=h/'BFSDisplayedSlots.lean'
if out.exists() or out.is_symlink():raise FileExistsError(out)
body=',\n'.join('  '+', '.join(map(str,values[i:i+8])) for i in range(0,len(values),8))
source='''import BFSDisplayedKernelV4

/-! The 41 printed slots and the fully decimal-list BFS kernel formula. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 20000000
namespace BFSDisplayedSlots
open scoped BigOperators

def values : List ℕ := [
'''+body+'''
]

theorem values_eq_slots : values = CompactSymbolicKernel.slots := by rfl

theorem values_length : values.length = 41 := by
  rw [values_eq_slots, CompactSymbolicKernel.slots_length]

def displayedPosition (i : Fin 41) : ℕ :=
  values.get ⟨i.val, by simpa only [values_length] using i.isLt⟩

theorem displayedPosition_eq (i : Fin 41) :
    displayedPosition i = CompactSymbolicKernel.position i := by
  unfold displayedPosition CompactSymbolicKernel.position
  simp only [List.get_eq_getElem, values_eq_slots]

def displayedKernel (r : ℕ) : ℕ :=
  r^30+r^62+r^1100+r^2201 +
  (∑ i : Fin 943, BFSDisplayedKernel.displayedSelector i * (r^(4393-i.val)+r^(5495-i.val))) +
  (∑ i : Fin 41, (2^(10+i.val):ℕ) * (r^(4393-displayedPosition i)+r^(5495-displayedPosition i))) +
  r^8849

theorem kernel_eq_displayed (r : ℕ) :
    DirectBFSSymbolicKernel.paramKernel r = displayedKernel r := by
  rw [BFSDisplayedKernel.kernel_eq_displayed]
  unfold BFSDisplayedKernel.displayedKernel displayedKernel
  simp only [displayedPosition_eq]

#print axioms BFSDisplayedSlots.kernel_eq_displayed
end BFSDisplayedSlots
'''
out.write_text(source);print('slots',len(values),'source_sha256',sha256(source.encode()).hexdigest())
