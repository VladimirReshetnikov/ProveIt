"""Owned discovery with actual Home scanner premises, no ends-in-one requirement."""
if not __debug__:
    raise RuntimeError('Assertions must be enabled')
from pathlib import Path
import json, collections
import check_framed_templates as F
A=F.A;D=Path(__file__).parent
sites=json.loads((F.OLD/'inputs/K215_Formal.sites.json').read_text())
ports=json.loads((F.OLD/'PORT_BINDING.json').read_text())['ports']
keys={};records=[];fallback=[];attempts=0
for i,(pc,op,arg) in enumerate(sites):
    if op not in ('CC','CB'):continue
    if op=='CC':successor=A.I.strip(pc,'1',arg);ov=0
    else:successor,ov=A.I.inc(A.I.strip(pc,'0',arg))
    result=None
    for cut in range(min(len(pc)-1,len(successor)),0,-1):
        prefix=pc[:cut]
        if not successor.startswith(prefix):continue
        S=pc[cut:];E=successor[cut:]
        k=(True,ports[pc],S,op,arg,False,E,0,ov,len(pc)-len(successor))
        if op=='CC':frame=S.count('1')>=arg and A.I.strip(S,'1',arg)==E
        else:
            stripped=A.I.strip(S,'0',arg);new,overflow=A.I.inc(stripped)
            frame=S.count('0')>=arg and not overflow and new==E
        if not frame:continue
        attempts+=1
        r=F.inspect(k)
        if 'failed'in r:continue
        # Existing KHome scan premise applied to concrete source prefix, not any prefix.
        full_scan=r['pre_home'][2]+tuple(A.B(int(b))for b in reversed(prefix))
        if F.bounded_scan(full_scan) is None:continue
        result=(cut,k,r,F.bounded_scan(full_scan));break
    if result is None:
        fallback.append(dict(site=i,pc=pc,op=op,arg=arg));continue
    cut,k,r,scan=result
    if k not in keys:keys[k]=dict(id=len(keys),**r)
    records.append(dict(site=i,cut=cut,template=keys[k]['id'],home_scan_bound=scan))
out=dict(status='LEFT_FRAME_EXISTING_HOME_DISCOVERY_PASS',control_guards=len(records)+len(fallback),framed_guard_uses=len(records),templates=len(keys),literal_control_guards=len(fallback),total_expensive_obligations=len(keys)+len(fallback)+1900+2850+1,attempts=attempts,guard_records=records,literal_controls=fallback,templates_data=[dict(key=k,**r)for k,r in keys.items()],scope='Finite owned model only. Generic guarded frame lift, finite template proofs and coverage integration are uncompiled.')
(D/'LEFT_FRAME_DISCOVERY.json').write_text(json.dumps(out,separators=(',',':')))
print({k:v for k,v in out.items()if k not in('guard_records','templates_data')})
