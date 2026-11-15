from pathlib import Path
exec((Path(__file__).resolve().parent/'rotate_fixed.py').read_text().split('import build194 as bld')[0])
import build194 as bld
q,r,direction=19,29,1
name='node49';orig_t=nodes[name];ch=nodes[orig_t[1]];nodes[name]=((orig_t[0],ch[0]),ch[1])
newsites,newins,newcs=c.source(grammar)
assert newins==ins
RR=dict(R);a0,a1=R[q,0],R[q,1];r0,r1=R[r,0],R[r,1]
RR[q,0]=(0,True,r);RR[q,1]=(1,True,r1[2]);RR[r,0]=(0,True,a0[2]);RR[r,1]=(1,True,r0[2])
child,aliases=bld.apply_folds(RR,folds)
local=bld.check_local_folds(RR,child,aliases,folds)
valid=c.validate(child,newcs)
print('validation',valid,flush=True)
assert valid == {'ok': False, 'failed': (50, (2, True)), 'completed': 70}
print('Expected rejection reproduced; this table is not a delivered machine.')
