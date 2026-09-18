"""Run the exact original backend on its recorded 36-crossing timeout case."""
import json,sys,time,pathlib
ROOT=pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'baseline'))
from fastunknot import Diagram
from fastunknot.scan import khovanov_rank,ScanLimit
x=json.loads((ROOT/'examples/baseline_timeout36.json').read_text())
d=Diagram.from_json(x)
t=time.perf_counter()
try:
 r=khovanov_rank(d.pd,seconds=120)
 result={'completed':True,'result':r}
except ScanLimit as e:
 result={'completed':False,'limit_seconds':120,'reason':str(e)}
result['elapsed_seconds']=time.perf_counter()-t
(ROOT/'results/baseline-hard-120s.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result),flush=True)
