"""Owned boundary/mutation checks. They are tests, not unbounded proofs."""
if not __debug__:
    raise RuntimeError('Assertions must be enabled')
from pathlib import Path
import json
import check_framed_templates as F
A=F.A;D=Path(__file__).parent
x=json.loads((D/'LEFT_FRAME_DISCOVERY.json').read_text())
passed=[]
s=(2,True,(),(A.B(1),A.X()))
assert F.local_step(None,s) is None
# Original sstep fabricates a blank here; adding a nonblank frame changes it.
plain=A.step(F.T,None,s)[0]
framed=A.step(F.T,None,(2,True,(A.B(1),),(A.B(1),A.X())))[0]
assert plain!=framed
passed.append('unsafe-empty-left-continuation-rejected')
for label,index,value in [('wrong-target-word',6,'0'),('wrong-gap-delta',9,99),('wrong-port',1,254)]:
    k=list(x['templates_data'][0]['key']);k[index]=value
    assert 'failed'in F.inspect(k)
    passed.append(label+'-rejected')
assert F.bounded_scan(tuple(A.B(0)for _ in range(8))) is None
passed.append('eight-zero-prefix-rejected')
assert F.bounded_scan((A.B(0),A.B(1),A.B(0))) is not None
passed.append('prefix-ending-zero-accepted')
# Ordinary sstep commutes with left-frame append on every recorded transition,
# for several differently shaped frames. No transition reads an empty local l.
frames=[(),(A.B(1),),(A.B(0),A.B(1)),(A.U(0,1,0),A.B(1)),(A.X(),)]
count=0
for t in x['templates_data']:
    assert t['pre_home'][0:3]==[2,True,[]]
    for e in t['trace']:
        s=tuple(e['before'][:2])+tuple(tuple(tuple(x)for x in a)for a in e['before'][2:])
        u=tuple(e['after'][:2])+tuple(tuple(tuple(x)for x in a)for a in e['after'][2:])
        assert not(s[1]and not s[2])
        for frame in frames:
            sf=(s[0],s[1],s[2]+frame,s[3]);uf=(u[0],u[1],u[2]+frame,u[3])
            got,m,kind=A.step(F.T,None,sf)
            assert got==uf and m==e['moved'] and kind==e['kind']
            count+=1
passed.append('all-recorded-step-frame-smoke-checks')
# Full occurrence accounting and exact source-operation framing.
sites=json.loads((F.OLD/'inputs/K215_Formal.sites.json').read_text())
ports=json.loads((F.OLD/'PORT_BINDING.json').read_text())['ports']
assert all('00000000'not in site[0]for site in sites)
seen=set()
for row in x['guard_records']:
    i=row['site'];assert i not in seen;seen.add(i)
    pc,op,arg=sites[i];cut=row['cut'];k=x['templates_data'][row['template']]['key']
    assert k[1]==ports[pc] and k[2]==pc[cut:] and k[3:5]==[op,arg]
    P=pc[:cut];S=k[2];E=k[6]
    if op=='CC':
        assert S.count('1')>=arg and A.I.strip(S,'1',arg)==E
        assert A.I.strip(pc,'1',arg)==P+E
    else:
        assert S.count('0')>=arg
        assert A.I.inc(A.I.strip(S,'0',arg))==(E,0)
        assert A.I.inc(A.I.strip(pc,'0',arg))==(P+E,0)
    assert k[9]==len(S)-len(E) and k[7:9]==[0,0]
    assert len(pc)<=48
    assert F.bounded_scan(tuple(A.B(int(b))for b in reversed(P)))==row['home_scan_bound']
for row in x['literal_controls']:
    assert row['site']not in seen;seen.add(row['site'])
assert seen=={i for i,s in enumerate(sites)if s[1]in('CC','CB')}
passed.append('all-1425-control-occurrences-accounted-exactly')
result=dict(status='NEGATIVE_AND_COVERAGE_CHECKS_PASS',checks=passed,finite_frame_smoke_checks=count,all_source_pcs_avoid_eight_zeros=True,all_new_templates_stop_with_empty_left=True,explicit_lifetime='The frame is never read before the terminal Home. Local positive progress is unnecessary, final Home supplies it.')
(D/'BOUNDARY_TESTS.json').write_text(json.dumps(result,indent=2));print(result)
