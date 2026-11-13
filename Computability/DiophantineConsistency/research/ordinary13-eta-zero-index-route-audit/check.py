#!/usr/bin/env python3
"""Bounded source audit for eta=0 parity route; no new graph or Lean."""
from pathlib import Path
import hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
g=json.loads(pin('research/ordinary13-natural-forced-w86/candidate.json','75d3110827afc1ef14a5ed2367229e81c645d3394beba2c04d255f53ffeefe50'))
index=pin('Lean/DiophantineConsistency/Compact44/P72Exact.lean','a07730d92aefd39d86083d037f4772bacd7741788e2fff1f7669d33fa0ad05d3')
first=pin('Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean','374719597b3126504fc7b4daeb8ce08a7bae36c911ed37d8fee3d90ed324a5d5')
half=pin('Lean/DiophantineConsistency/ArithmeticPellHalfIndex.lean','7703193660d8ae98408d1ec3a83f6f8811927252e739bb7af18dbafb833a8877')
rec=pin('Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean','63ec2a49f8d7066dbd8647a663db4bbd7255abd3ca7c3cc0d4d7b3533a189b16')
orient=pin('Lean/DiophantineConsistency/Compact44/DirectMainNorm.lean','29c748582368b4ab2bcdb4b4cdd4f7890dda32f77718e33355b590b8f07b7fbd')
rank=pin('Lean/DiophantineConsistency/ArithmeticAdaptiveRankWindow2011.lean','0895f6e74b29c2cc2e4542d739b238352778750da62766819caeb105995fb794')
aux=pin('research/ordinary14-aux-root-model-draft/AuxRootBridge.lean','796819c48d53665e1ee9c90d8d1bfd0fbd00cd4ca5535fe4fad1a3462d74c8b7')
geom=pin('research/ordinary14-aux-geometry-model-draft/AuxGeometry.lean','88de9d4d0e92e43ca9483dcb90ae96a7e16284e69b8384cd41c9e16a7ad87b77')
bounds=pin('research/ordinary14-aux-root-bounds-model-draft/AuxRootBounds.lean','f7e198e882e31c67e915c0c7953f5a37c03e2c8c2ddb0a8c0043d2b8b71ca504')
a=index.split('theorem index_window',1)[1].split('theorem index_close',1)[0];b=index.split('theorem indices_ordinary',1)[1].split('theorem exact_ordinary',1)[0]
ha=[x.strip() for x in a.splitlines() if 'hη' in x];hb=[x.strip() for x in b.splitlines() if 'hη' in x]
assert len(ha)==4 and len(hb)==3
assert sum('lt_add_of_pos_right _ hη' in x for x in ha)==2
assert 'add_pos_of_pos_of_nonneg hη' in ha[1] and 'index_window' in hb[1] and 'lt_add_of_pos_right _ hη' in hb[2]
for text,term in [(first,'theorem even_ordinate'),(half,'theorem y_two_step'),(rec,'theorem y_succ'),(orient,'theorem direct_main_orientation'),(rank,'theorem scalar_rank_window'),(aux,'theorem positive_aux_coordinate_iff'),(geom,'theorem geometry_of_large_k'),(bounds,'theorem first_ordinate_large')]:assert term in text,term
rows={r[0]:r for r in g['source']}
for row in [['eta','+','n_eta',1],['kbase','+','eta','n_zeta'],['k','+','kbase',1],['kY','*','Y','k'],['c','+','eta','kY'],['g40','*','ell','g30'],['g41','+',1,'g40'],['A0','-','g38','g42'],['A1','-','g61','g65']]:assert rows[row[0]]==row,row
# Finite parity controls illustrate, but do not prove, the recurrence invariant.
cases=0
for a0 in range(24):
 x,y=1,0
 for n in range(90):
  assert y%2==n%2
  x,y=((a0+2)*x+(a0+1)*(a0+3)*y)%2,(x+(a0+2)*y)%2
  cases+=1
print(json.dumps({'scope':'bounded source-interface inventory and finite parity controls; no generalized theorem, graph zero map or Lean','index_window_eta_token_lines':ha,'indices_ordinary_eta_token_lines':hb,'parity_controls':cases,'first_even_ordinate_source_pinned':True,'main_two_step_source_pinned':True,'graph_eta_is_shifted':True,'lean_elaboration':False},ensure_ascii=False,sort_keys=True,indent=2))
