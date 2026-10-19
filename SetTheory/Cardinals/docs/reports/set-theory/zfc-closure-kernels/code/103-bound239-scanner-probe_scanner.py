"""Concrete diagnostics for shortened backward scans on the pinned 240 table."""
from pathlib import Path
import sys, json, time
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'validation'))
import independent_runtime as r
ROOT = Path(__file__).resolve().parents[1]
base = r.table(ROOT/'baseline/rotation240/zfc_rotation240_old.tm')
sites = json.loads((ROOT/'baseline/rotation240/sites_logical.json').read_text())
new = dict(base)
del new[58,0]; del new[58,1]
new[41,0] = (0,-1,84)
started = time.monotonic()
fails=[];passed=0
for i,s in enumerate(sites):
    for pos in ([False,True] if s[1]=='CD' else [False]):
        regs=[0]*9
        if pos: regs[s[2]]=1
        wanted=r.expected(s,regs,[0])
        got,ticks,trace=r.run(new,s[0],regs,trace=False,limit=10000)
        ok=got[0]==254 if wanted is None else got==wanted[0]
        if ok: passed+=1
        else:
            original,oticks,_=r.run(base,s[0],regs,limit=10000)
            assert original[0]==254 if wanted is None else original==wanted[0]
            fails.append({'site_index':i,'site':s,'positive':pos,'ticks':ticks,
               'actual_state':got[0],'actual_head':got[1],
               'expected_state':None if wanted is None else wanted[0][0],
               'expected_head':None if wanted is None else wanted[0][1],
               'difference_ones':None if wanted is None else sorted(got[2]^wanted[0][2])})
out={'scope':'All guarded source sites on a finite zero/minimum-positive register fixture, one zero spare. No unbounded conclusion.',
     'passed':passed,'failed':len(fails),'failures':fails,'seconds':time.monotonic()-started}
(ROOT/'scanner/scanner_probe.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='failures'},indent=2))
print(json.dumps(fails[:8],indent=2))
