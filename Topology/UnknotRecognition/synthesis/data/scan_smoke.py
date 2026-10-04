import sys, time
sys.path.insert(0, 'C:/Knots/fast')
sys.path.insert(0, 'C:/Users/vresh/AppData/Local/Temp/claude/C--Knots/098bb8b7-a324-4a1d-a8ef-b20101618640/scratchpad/xval')
from fastunknot.scan import khovanov_rank
from kh04 import Diagram, recognize
tests = [(1,[]), (2,[1]), (2,[1,1,1]), (3,[1,-2,1,-2]), (3,[1,2]*5), (3,[1,2]), (3,[-2,-2,1,2,2,2]), (4,[1,2,3])]
for s,w in tests:
    d = Diagram.from_braid(s,w)
    pd = [list(c) for c in d.pd]
    t=time.perf_counter(); r = khovanov_rank(pd, check_d_squared=True); t=time.perf_counter()-t
    ref = recognize(d).reduced_rank
    print(s, w, 'scan', r['rank'], r['reduced_rank'], 'ref', ref, 'OK' if r['reduced_rank']==ref else 'MISMATCH', round(t,3), r['stats'])
