"""Compare replay output with pinned finite-check results."""
from pathlib import Path
import json, math, sys
expected=Path(sys.argv[1]); actual=Path(sys.argv[2])
pairs={'uniform.json':'checks.json','symbolic.json':'recomputed.json','inverse.json':'inverse.json'}
def compare(x,y,path='root'):
    if isinstance(x,dict):
        assert isinstance(y,dict) and set(x)==set(y), (path,'keys differ')
        for k in x:compare(x[k],y[k],path+'.'+k)
    elif isinstance(x,list):
        assert isinstance(y,list) and len(x)==len(y),(path,'length differs')
        for j,(a,b) in enumerate(zip(x,y)):compare(a,b,path+f'[{j}]')
    elif isinstance(x,str):
        try:a=float(x);b=float(y)
        except (ValueError,TypeError):assert x==y,(path,x,y)
        else:
            assert math.isfinite(a) and math.isfinite(b),(path,'nonfinite')
            assert math.isclose(a,b,rel_tol=2e-10,abs_tol=1e-28),(path,x,y)
    else:assert x==y,(path,x,y)
for a,b in pairs.items():
    compare(json.loads((expected/a).read_text()),json.loads((actual/b).read_text()),a)
print('PASS: all symbolic and numerical outputs agree with the recorded checks')
