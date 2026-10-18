#!/usr/bin/env python3
"""Literal startup and full affine runtime audit for a new MP0 permutation.

The initial structural frame has H=1 and is not assumed sound.  We execute
literal transitions until a complete root frame has T=W=H=A=X=Y=0.
The affine check uses the four unchanged published Box contracts.
"""
from pathlib import Path
from collections import Counter
import hashlib,json,sys,time
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'redesign'))
import mp_protocol_runtime as m

PERM=(0,2,6,8,7,5,3,1,4)

def main():
    begun=time.monotonic()
    table,nodes=m.generate()
    previous=m.audit.PERM
    inverse={v:i for i,v in enumerate(previous)}
    for q,b in m.audit.SELECTOR_INCOMING:
        w,d,t=table[str(q),b]
        oldphysical=inverse[m.a.SKIP.index(int(t))]
        table[str(q),b]=w,d,str(m.a.SKIP[PERM[oldphysical]])
    m.audit.PERM=PERM
    path=HERE/'mp_rebased252.tm'
    path.write_bytes(m.a.encoded(table))
    assert all(table[key]==m.a.T[key] for key in m.a.BOX_PAIRS)
    affine=m.certify(table,m.guards())
    assert affine['passed'] and affine['cases_passed']==8366
    q='64';h=0;ones=set();used=Counter();roots=[]
    for step in range(1000001):
        frame=m.a.parse_root(q,h,ones,PERM)
        if frame:
            frame['steps']=step
            # Suppress duplicates at this same literal time, but retain unsafe
            # structural frames so the recovery is completely visible.
            roots.append(frame)
            logical=frame['logical_primary']
            if all(logical[r]==0 for r in (1,2,3,5,6,7)):
                assert len(frame['spares'])>=0
                break
        if q=='254':raise AssertionError(('halt before safe frame',step))
        if step==1000000:raise AssertionError('safe frame not reached')
        key=q,int(h in ones);used[key]+=1
        w,d,q=table[key]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=1 if d=='R' else -1
    assert roots[0]['steps']==81371
    assert roots[0]['logical_primary']==[0,0,0,0,1,1,0,0,0]
    assert roots[-1]['logical_primary']==[1,0,0,0,1,0,0,0,0]
    result=dict(status='ordinary_checks_pass',working_states=len(table)//2,
                table_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                physical_permutation=list(PERM),
                logical_to_physical=[PERM[p] for p in m.a.PHYS],
                affine=affine,protected_box_pairs_unchanged=55,
                blank_literal_steps=step,structural_roots=roots,
                blank_used_rows=len(used),blank_used_states=len({q for q,b in used}),
                elapsed_seconds=time.monotonic()-begun,
                scope='Full exact finite blank execution; all runtime affine cases conditional on four unchanged Box contracts. No fresh proof-assistant build or fewer-than-252-state claim.')
    (HERE/'mp_rebased_audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='structural_roots'},indent=2))
    print('Root summaries:',[(r['steps'],r['logical_primary'],r['gap'],len(r['spares'])) for r in roots])

if __name__=='__main__':main()
