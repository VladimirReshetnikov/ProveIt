"""Independent reconstruction of the unchanged source19/source30 quartet.
All input files are inert JSON. No unknowns are used to specify coefficients.
"""
from pathlib import Path
from hashlib import sha256
import json, gzip
P=Path(__file__).resolve().parent

def build():
    raw=(P/'k215.tm').read_bytes()
    assert sha256(raw).hexdigest()=='fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090'
    rows=[]
    for line in raw.decode().splitlines():
        if line and not line.startswith('#'):
            q,bit,v,move,t=line.split();rows.append([int(q),int(bit),int(v),1 if move=='R' else -1,int(t)])
    assert len(rows)==430 and rows==json.loads((P/'k215_transitions.json').read_text())['transitions']
    tiles=json.loads((P/'wang943_tiles.json').read_text())
    assert len(tiles)==943 and len(set(map(tuple,tiles)))==943
    b,L,d,H=625,15625,9765625,5497
    anchors=[1095,1096,2195,3296]
    cp={(s,j):o+j for s,o in enumerate([1023,1013,1003,983]) for j in range(10)}
    E=set(range(943))|set(cp.values())|set(anchors)|{1063,1064}
    A=1024
    ce={i:1+sum(A**(1+10*s+j) for s,x in enumerate(tile) for j in range(10) if ((x+512)>>j)&1)+sum(A**j for j in range(41,45)) for i,tile in enumerate(tiles)}
    ce.update({e:A**(1+10*s+j) for (s,j),e in cp.items()})
    ce.update({e:A**(41+j) for j,e in enumerate(anchors)})
    ce.update({1063:0,1064:0})
    mu=A-2+sum((A-3)*A**j for j in range(1,45))+((1<<78)-1)*(1<<450)
    dc={e:1 for e in [30,5517,1100,2200]}
    for e,c in ce.items():
        for t in [7631,8733]: dc[t-e]=dc.get(t-e,0)+c
    targets=[(1013+j,{983+j},set(),{1013+j}) for j in range(10)]
    targets += [(H+1023+j,{1003+j},{1023+j},set()) for j in range(10)]
    targets += [(2195,{1095},set(),{2195}),(3296,{1096},set(),{3296})]
    checks=0
    for t,x,y,z in targets:
        for e in E:
            assert dc.get(t-e,0)==int(e in x)
            assert int(e+H==t)==int(e in y)
            assert int(e==t)==int(e in z)
            checks+=3
    for t in [7631,8733]:
        for e in E:
            assert dc.get(t-e,0)==ce[e] and e+H!=t
            checks+=2
    assert {(7631-e)%L for e in E}.isdisjoint({(8733-e)%L for e in E})
    assert {(2195-e)%L for e in E}&{(3296-e)%L for e in E}=={0}
    B=1<<d
    DC=sum(c<<(b*e) for e,c in dc.items()); DR=1<<(b*H)
    MC=B-1-sum(1<<(b*e) for e in E if e!=1)-(2<<(b*1063))
    native=4+(mu<<(b*7631))+(mu<<(b*8733))+sum(1<<(b*t) for t,*_ in targets)
    ports={'beta':B-1,'K':DC+B*DR,'MC':MC,'MF_source':native+B-1}
    assert MC%4==2 and native%8==4 and native.bit_count()==989
    assert MC.bit_count()+native.bit_count()==d and (2*DC-DR)%5==4
    original=json.loads((P/'COMPACT_COEFFICIENT_BINDING.json').read_text())
    expected={r['name']:r for r in original['files']}
    out=P/'coefficients_compact';out.mkdir(exist_ok=True)
    result={}
    for name,n in ports.items():
        raw=n.to_bytes((n.bit_length()+7)//8,'little')
        digest=sha256(raw).hexdigest()
        assert digest==expected[name]['sha256']
        assert len(raw)==expected[name]['bytes'] and n.bit_length()==expected[name]['bit_length']
        (out/(name+'.bin')).write_bytes(raw)
        (out/(name+'.bin.gz')).write_bytes(gzip.compress(raw,mtime=0))
        result[name]={'sha256':digest,'bytes':len(raw),'bit_length':n.bit_length()}
    receipt={'status':'PASS','variant':'wang943-compact-5pow10','literal_transition_rows':len(rows),'basis_checks':checks,'ports':result,'total_raw_bytes':sum(v['bytes'] for v in result.values()),'claim':'Exact byte reproduction only; inherited compiler proof remains a mathematical dependency.'}
    (P/'REBUILD_CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
    return receipt

if __name__=='__main__':
    if not __debug__: raise SystemExit('Do not disable assertions.')
    build()
