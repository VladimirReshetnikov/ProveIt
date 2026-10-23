"""Independent finite audit of the mixed-radix compiler tuple.

Uses inert tile and transition data, never imports the coefficient builder.
These checks do not replace the infinite tiling/Pell or logical proofs.
"""
from pathlib import Path
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
C = ROOT / 'coefficients'

def require(p, message):
    if not p:
        raise ValueError(message)

def run():
    require(__debug__, 'Run without -O')
    tiles = json.loads((C/'wang943_tiles.json').read_text())
    require(len(tiles)==943 and len(set(map(tuple,tiles)))==943,'Tile count')
    require(tiles[:2]==[[2,435,3,1],[5,0,0,0]],'Distinguished order')
    offsets=(1023,1013,1003,983)
    anchors=(1095,1096,2195,3296)
    support=set(range(943))|{1063,1064}|set(anchors)
    support.update(e+j for e in offsets for j in range(10))
    require(len(support)==989,'Support count')
    # One 10-bit count digit followed by forty-four two-bit clause digits.
    bit_positions=tuple(10+2*j for j in range(44))
    coefficients={e:0 for e in support}
    for i,tile in enumerate(tiles):
        a=1
        for slot,label in enumerate(tile):
            require(0<=label<512,'Label bounds')
            for j in range(10):
                if ((label|512)>>j)&1:
                    a |= 1<<bit_positions[10*slot+j]
        for j in range(40,44):
            a |= 1<<bit_positions[j]
        coefficients[i]=a
    for slot,e in enumerate(offsets):
        for j in range(10): coefficients[e+j]=1<<bit_positions[10*slot+j]
    for j,e in enumerate(anchors): coefficients[e]=1<<bit_positions[40+j]
    mu=1022+sum(1<<p for p in bit_positions)
    require(mu.bit_count()==53 and mu.bit_length()==97,'Clause mask')
    require([n for n in range(944) if n&1022==0]==[0,1],'Count decoder')
    require([n for n in range(3) if n&1==0]==[0,2],'Boolean decoder')
    # This order is essential: first obtain count <=1; only then may we
    # infer no carry between the two-bit payload digits.
    for t in tiles:
        for label in t:
            for j in range(10):
                bit=((label|512)>>j)&1
                require([v for v in (0,1) if (v+bit)&1==0]==[bit],'Copy extraction')
    dc={30:1,62:1,1100:1,2200:1}
    for e,v in coefficients.items():
        for target in (7631,8733): dc[target-e]=dc.get(target-e,0)+v
    dc={e:v for e,v in dc.items() if v}
    targets=[]
    for j in range(10):targets.append((1013+j,983+j,None,1013+j))
    for j in range(10):targets.append((1065+j,1003+j,1023+j,None))
    targets.extend([(2195,1095,None,2195),(3296,1096,None,3296)])
    def geometry(transport):
        for target,local,neighbor,time in targets:
            for e in support:
                if dc.get(target-e,0)!=(e==local):return False
                if (e+transport==target)!=(e==neighbor):return False
                if (e==target)!=(e==time):return False
        for target in (7631,8733):
            for e in support:
                if dc.get(target-e,0)!=coefficients[e] or e+transport==target:return False
        return True
    require(geometry(42),'Exact target geometry')
    require(not geometry(43),'Transport corruption control')
    require(not ({(7631-e)%15625 for e in support}&{(8733-e)%15625 for e in support}), 'Clean band intersection')
    require({(2195-e)%15625 for e in support}&{(3296-e)%15625 for e in support}=={0},'Anchor alignment')
    mass=(989+2)*(2*sum(coefficients.values())+6)
    require(4*mass+8<2**125 and 2*mu+4<2**125,'Uniform carry bound')
    top=max(max(dc)+max(support),42+max(support),max(support))
    require(top==12029,'Largest product field')
    padding=range(12030,12890)
    require(len(padding)==860 and padding.stop<=15625,'Zero fields')
    b=125;d=5**9;B=1<<d
    D_C=sum(v<<(b*e) for e,v in dc.items())
    D_R=1<<(b*42)
    high=4+(mu<<(b*7631))+(mu<<(b*8733))
    high+=sum(1<<(b*t[0]) for t in targets)
    high+=sum(1<<(b*t) for t in padding)
    low=B-1-sum(1<<(b*e) for e in support if e!=1)-(2<<(b*1063))
    require(high.bit_count()==989 and low.bit_count()==d-989,'Population balance')
    require(low%4==2 and high%8==4,'Low residues')
    require(0<low<B-1 and 0<high<B-1 and 0<D_C<B,'Magnitude bounds')
    require((2*D_C-D_R)%5==1,'Actual-rank unit')
    ports={'beta':B-1,'K':D_C+B*D_R,'MC':low,'MF_source':high+B-1}
    manifest=json.loads((C/'expanded/MANIFEST.json').read_text())
    records={}
    for name,value in ports.items():
        raw=(C/'expanded'/f'{name}.bin').read_bytes()
        expected=value.to_bytes((value.bit_length()+7)//8,'little')
        require(raw==expected,'Whole-tuple byte mismatch '+name)
        h=hashlib.sha256(raw).hexdigest()
        require(h==manifest['ports'][name]['sha256'],'Manifest mismatch '+name)
        records[name]={'sha256':h,'bytes':len(raw),'bits':value.bit_length()}
    # A change of one numeric port must not pass an atomic binding audit.
    require(ports['MF_source']!=high,'Shift corruption control')
    return {'status':'PASS','tuple_id':'wang943-mixed-radix4-zero-fields-5pow9',
            'decoder_cases':944+3+943*40,'geometry_basis_checks':69230,
            'negative_controls':['transport 42 to 43','native high mask substituted for shifted port'],
            'population':{'native_high':989,'low':d-989,'sum':d},'ports':records,
            'scope':'Independent finite reconstruction; infinite semantic arguments remain separate.'}

if __name__=='__main__':
    out=run()
    (Path(__file__).parent/'MIXED_INDEPENDENT_CHECKS.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
