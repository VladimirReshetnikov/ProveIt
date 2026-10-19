"""ctypes discovery interface; original Python checker remains final authority."""
from pathlib import Path
import ctypes as C
import json,time
import composed_rotations as D
E=D.E
class Action(C.Structure):
    _fields_=[('write',C.c_int),('move',C.c_int),('next',C.c_int)]
class Site(C.Structure):
    _fields_=[('bits',C.c_uint64),('length',C.c_int),('op',C.c_int),('reg',C.c_int)]
LIB=C.CDLL(str(Path(__file__).with_name('affine_screen.so')))
LIB.affine_cases.argtypes=[C.POINTER(Action),C.c_int,C.POINTER(Site),C.c_int,
                          C.POINTER(C.c_int),C.POINTER(C.c_int),C.POINTER(C.c_int),
                          C.POINTER(C.c_ubyte),C.c_int,C.c_int,C.POINTER(C.c_int),C.POINTER(C.c_int)]
LIB.affine_cases.restype=C.c_int
PRIORITY_PATH=Path(__file__).with_name('case_order.json')
PRIORITY=json.loads(PRIORITY_PATH.read_text())['priority_leaf_indices'] if PRIORITY_PATH.exists() else []

def run(U,sites,stop_states=246,fuel=2000,use_priority=True):
    assert all(U[pair]==E.T[pair] for pair in E.PAIRS),'macro proof support changed'
    qmax=max(int(q) for q,b in U)
    assert qmax<1024
    table=(Action*(2*qmax+2))()
    for a in table:a.next=-1
    for (q,b),(w,m,t) in U.items():table[2*int(q)+b]=Action(w,1 if m=='R' else -1,int(t))
    if use_priority and len(sites)==6460:
        first=set(PRIORITY);order=PRIORITY+[i for i in range(len(sites)) if i not in first]
    else:order=list(range(len(sites)))
    source=(Site*len(sites))(*(Site(int(sites[i][0],2) if sites[i][0] else 0,len(sites[i][0]),ord(sites[i][1][-1]),-1 if sites[i][2] is None else sites[i][2]) for i in order))
    failed,branch,error=C.c_int(-1),C.c_int(-1),C.c_int(-1)
    footprint=(C.c_ubyte*2048)()
    witnesses=(C.c_int*1024)();nwitnesses=C.c_int(0)
    result=LIB.affine_cases(table,qmax,source,len(source),C.byref(failed),C.byref(branch),C.byref(error),footprint,stop_states,fuel,witnesses,C.byref(nwitnesses))
    used={(str(i//2),i%2) for i in range(len(footprint)) if footprint[i]}
    return dict(code=result,failed_site=order[failed.value] if failed.value>=0 else -1,failed_branch=branch.value,error=error.value,
                states=len({q for q,b in used}),witness_leaf_indices=[order[witnesses[i]] for i in range(nwitnesses.value)]),used

def make_priority():
    sites=E.get_sites(E.NODES,E.ROOT);footprints=[];all_states=0
    table=E.Track(E.T)
    for site in sites:
        table.used=set()
        for pc,branch,target,halt in E.make_cases([site]):E.A.run(table,pc,branch,target,halt=halt,fuel=2000)
        mask=sum(1<<int(q) for q in {q for q,b in table.used})
        footprints.append(mask);all_states|=mask
    covered=sum(1<<int(q) for q in {q for q,b in E.PAIRS});priority=[]
    while covered&all_states!=all_states:
        i=max(range(len(sites)),key=lambda j:(footprints[j]&~covered).bit_count())
        gain=footprints[i]&~covered;assert gain
        priority.append(i);covered|=footprints[i]
    PRIORITY_PATH.write_text(json.dumps(dict(priority_leaf_indices=priority,baseline_states_covered=(covered&all_states).bit_count(),
                                           purpose='Search priority only; every full pass still checks all source sites.'),indent=2)+'\n')
    print('priority length',len(priority))

def baseline_control():
    sites=E.get_sites(E.NODES,E.ROOT);began=time.monotonic()
    fast,fast_rows=run(E.T,sites,stop_states=0)
    assert fast['code']==0,fast
    table=E.Track(E.T);table.used=set()
    cases=E.make_cases(sites)
    for pc,branch,target,halt in cases:E.A.run(table,pc,branch,target,halt=halt,fuel=2000)
    expected=table.used|E.PAIRS
    assert fast_rows==expected,(sorted(fast_rows-expected),sorted(expected-fast_rows))
    # Three invalid decoder rewrites must fail both implementations on the
    # exact same first guarded case; macro proof rows remain protected.
    controls=[]
    for pair in [('96',0),('178',1),('218',0)]:
        mutant=E.T.copy();mutant[pair]=(0,'R','254')
        rec,_=run(mutant,sites,stop_states=0)
        assert rec['code']==-1
        pos=rec['failed_site'];pc,op,r=sites[pos]
        wanted_branch=(r,rec['failed_branch']==1) if op=='CD' else None
        this_case=next(c for c in cases if c[0]==pc and c[1]==wanted_branch)
        try:E.A.run(mutant,*this_case[:3],halt=this_case[3],fuel=2000)
        except Exception as ex:controls.append(dict(row=pair,fast=rec,python=str(ex)))
        else:raise AssertionError(('C++ false negative',pair,rec))
    out=dict(status='PASS_DISCOVERY_CONTROLS',baseline_sites=len(sites),guarded_cases=len(cases),
             baseline_used_rows=len(expected),baseline_used_states=fast['states'],
             negative_controls=controls,elapsed=time.monotonic()-began,
             boundary='Implementation cross-check only; all positive discoveries require original Python replay.')
    Path(__file__).with_name('acceleration-control.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__':
    import sys
    if '--make-priority' in sys.argv:make_priority()
    else:baseline_control()
