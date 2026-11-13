#!/usr/bin/env python3
"""Transcribe the displayed PDF selector sequence into a Lean finite-list goal."""
from pathlib import Path
from hashlib import sha256
import re, subprocess
h=Path(__file__).resolve().parent
pdf=h.parent/'ten-positive-80-bfs-decimal-display/equation.pdf'
if sha256(pdf.read_bytes()).hexdigest()!='412ebf276d1e3d9b2802d333e020a4b7579f2368660bdede31be665564e40fe7':raise ValueError('PDF changed')
r=subprocess.run(['pdftotext','-layout',str(pdf),'-'],capture_output=True,text=True,check=True,timeout=60)
if r.stderr:raise ValueError('extract diagnostics')
a=re.findall(r'(?<!\d)\d{14}(?!\d)',r.stdout.split('Decimal selector list.',1)[1])
if len(a)!=943:raise ValueError('selector count')
out=h/'BFSDisplayedSelectors.lean'
if out.exists() or out.is_symlink():raise FileExistsError(out)
body=',\n'.join('  '+', '.join(str(int(x)) for x in a[i:i+8]) for i in range(0,len(a),8))
source='''import DirectBFSSymbolicKernel

/-! Decimal selector sequence transcribed from the external BFS display. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 20000000
namespace BFSDisplayedSelectors

def values : List ℕ := [
'''+body+'''
]

theorem values_eq_rows_map :
    values = DirectBFSSymbolicKernel.rows.map CompactCoefficientMass.selector := by
  decide

#print axioms BFSDisplayedSelectors.values_eq_rows_map
end BFSDisplayedSelectors
'''
out.write_text(source)
print('selectors',len(a),'source_sha256',sha256(source.encode()).hexdigest())
