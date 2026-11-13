#!/usr/bin/env python3
"""Bounded source audit, not a Lean proof."""
from pathlib import Path
import hashlib,json,re,math,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
pins={'research/ordinary14-natural81-combined-slim-overlay/source/AuxRootBounds.lean.src': 'f7e198e882e31c67e915c0c7953f5a37c03e2c8c2ddb0a8c0043d2b8b71ca504', 'research/ordinary14-natural81-combined-slim-overlay/source/FirstMainLargeK.lean.src': '65d2de66fec31d7cc2d79687acc353638e864077c561af12829d93007d430e61', 'research/ordinary14-natural81-combined-slim-overlay/source/MainSquareGap.lean.src': '6639167627e5cf01814d1ae48f3975d42a72a6451863b31c9795b427ec6c5e68', 'Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean': '374719597b3126504fc7b4daeb8ce08a7bae36c911ed37d8fee3d90ed324a5d5', 'Lean/DiophantineConsistency/Compact44/P72Root.lean': '066fce52d35ab720519ee8817d9b56c2eacc9ac4f6bb7bf6e92286a87f44d091'}
for f,h in pins.items():assert hashlib.sha256((D/f).read_bytes()).hexdigest()==h,f
aux=(D/'research/ordinary14-natural81-combined-slim-overlay/source/AuxRootBounds.lean.src').read_text()
first=aux.split('theorem first_ordinate_large',1)[1].split('/-- Given the explicit strong norm',1)[0]
for token in ['(hm : 0<m)','(hk : 2<k)','tau*tau=1+m*(m+1)*k*k','8*m+4≤k','descent q tau k','two_le_ordinate q u v','m-1+1=m']:
 assert token in first,token
assert not re.search(r'\b(?:Even|Odd|even|odd|parity|sorry|admit|axiom|unsafe)\b',first)
source=(D/'Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean').read_text()
for token in ['theorem two_le_ordinate','theorem descent','k=2*u+(2*q+3)*v']:
 assert token in source,token
main=(D/'research/ordinary14-natural81-combined-slim-overlay/source/FirstMainLargeK.lean.src').read_text()
for token in ['two_ordinate_impossible','first_ordinate_large','(hX : 0<X)','(hY : 0<Y)']:
 assert token in main,token
solutions=0
for m in range(1,31):
 for k in range(3,1001):
  n=1+m*(m+1)*k*k;t=math.isqrt(n)
  if t*t==n:
   solutions+=1;assert k>=8*m+4,(m,k,t)
print(json.dumps({'scope':'bounded source audit and finite sanity only; no Lean','pinned_files':pins,'first_ordinate_signature_present':True,'no_parity_premise_in_target_block':True,'existing_first_main_client_present':True,'finite_m_range':[1,30],'finite_k_range':[3,1000],'finite_solutions':solutions},sort_keys=True,indent=2))
