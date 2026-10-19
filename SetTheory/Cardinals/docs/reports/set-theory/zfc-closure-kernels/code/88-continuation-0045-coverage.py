from pathlib import Path
import sys
sys.dont_write_bytecode=True
from state_paths import output_directory
import sys,json,importlib.util
ROOT=Path(__file__).resolve().parents[2]
R=output_directory()
VENDOR=ROOT/'vendor/context246'
sys.path.insert(0,str(VENDOR/'code'))
import check_macro_inductions as macro
import review_affine_source as review
from rebuild_machines import read_table

class Monitor(dict):
    def __init__(self,*args):
        super().__init__(*args);self.used=set()
    def __getitem__(self,k):
        self.used.add(k);return super().__getitem__(k)

T=read_table(VENDOR/'machine/zfc_prefix246_old.tm')[0]
mt=Monitor(T)
macro.TABLE=mt
macro.prove_blocks();macro.prove_word_identity();macro.prove_macros();macro.prove_marks()
affine=review.module(VENDOR/'sources/prior/prefix_affine.py')
at=Monitor({(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in T.items()})
nodes,sites=review.parse_source(VENDOR/'sources/Prog254.v')
print(review.check_sites(affine,at,sites))
used=mt.used|{(int(q),b) for q,b in at.used}
unused=sorted(set(T)-used)
print('unused runtime',unused)
merges=[]
for (q,b) in unused:
    if (q,1-b) in used:
        matches=[r for r,c in T if c==1-b and r!=q and T[r,c]==T[q,c]]
        if matches:merges.append((q,b,matches))
print('single-symbol matches',merges)
json.dump({'macro_used':sorted(mt.used),'affine_used':sorted([(int(q),b)for q,b in at.used]),'unused_runtime':unused,'single_symbol_matches':merges},open(R/'coverage.json','w'),indent=2)
