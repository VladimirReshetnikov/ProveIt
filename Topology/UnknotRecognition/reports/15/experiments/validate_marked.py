from pathlib import Path
import sys,json,time
ROOT=Path(__file__).resolve().parents[1]
sys.path[:0]=[str(ROOT/'code'),str(ROOT/'tests')]
from radical import *
from fixtures import gauge_complex,sharp_transfer_complex
start=time.perf_counter(); count=0
for k in range(1,5):
    for seed in range(75):
        a=ArcAlgebra(); d=gauge_complex(a,k,87000+seed)
        t=transfer_marked(d,a,0); check_contraction(t,a)
        assert t.profile==survivor_profile(d)
        count+=1
for k in range(1,9):
    a=ArcAlgebra(); d=sharp_transfer_complex(a,k)
    check_contraction(transfer_marked(d,a,0),a); count+=1
out={'status':'passed','two_pass_full_certificates':count,'seconds':time.perf_counter()-start}
(ROOT/'results'/'marked_validation.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
