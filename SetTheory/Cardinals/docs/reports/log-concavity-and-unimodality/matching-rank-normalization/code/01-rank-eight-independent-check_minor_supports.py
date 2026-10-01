from itertools import combinations_with_replacement, combinations, permutations
import json
from pathlib import Path
import sys
records=[]
for cols in combinations_with_replacement(range(8),4):
 m1=sum(x.bit_count() for x in cols)
 m2=sum(bool((cols[i]>>a&1 and cols[j]>>b&1) or (cols[i]>>b&1 and cols[j]>>a&1)) for i,j in combinations(range(4),2) for a,b in combinations(range(3),2))
 m3=sum(any(all(cols[j]>>a&1 for j,a in zip(J,p)) for p in permutations(range(3))) for J in combinations(range(4),3))
 if m3 and m2>2*m1:raise RuntimeError((cols,m1,m2,m3))
 records.append([cols,m1,m2,m3])
if '--save-certificate' in sys.argv:
 json.dump({'passed':True,'support_profiles':len(records),'rank_three_profiles':sum(bool(r[3]) for r in records),'records':records},open(Path(__file__).resolve().parents[2]/'data'/'minor_support_result.json','w'),indent=2)
print('PASS',len(records),'profiles; generic minor counts upper-bound all realizations with fixed nonzero-entry support')
