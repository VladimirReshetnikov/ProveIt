"""Exact symbolic phase proof for the creator's fixed U15,2 Waterfall matrix.

This checks a finite collection of affine inequalities for all Q,Y >= 0,
not a finite input grid. Ordinary Python integers are used throughout.
Matrix rows in the downloaded file are source-trigger rows.
"""
from pathlib import Path
from collections import Counter
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]

class Aff:
    def __init__(self, c=0, q=0, y=0): self.v = (c,q,y)
    @staticmethod
    def cast(a): return a if isinstance(a,Aff) else Aff(a)
    def __add__(self,b):
        b=self.cast(b); return Aff(*(a+c for a,c in zip(self.v,b.v)))
    __radd__=__add__
    def __neg__(self): return Aff(*(-a for a in self.v))
    def __sub__(self,b): return self+-self.cast(b)
    def __rsub__(self,b): return self.cast(b)+-self
    def __mul__(self,k):
        assert type(k) is int
        return Aff(*(a*k for a in self.v))
    __rmul__=__mul__
    def at(self,q,y): return self.v[0]+q*self.v[1]+y*self.v[2]
    def positive_on(self, q_min=0, y_min=0):
        return self.at(q_min,y_min)>=1 and self.v[1]>=0 and self.v[2]>=0

NAMES=(['LeftTape','LeftTemp','LeftTrans','LeftDiv0','LeftDiv1','LeftMult','LeftWrite0','LeftWrite1']+
       [f'Trans{chr(65+q)}{s}' for q in range(15) for s in range(2)]+
       ['RightWrite0','RightWrite1','RightMult','RightDiv0','RightDiv1','RightTrans','RightTemp','RightTape'])
INDEX={n:i for i,n in enumerate(NAMES)}

def canonical(state,symbol,left,right):
    d=[Aff(2) for _ in NAMES]
    d[INDEX['LeftTape']]=2+2*left
    d[INDEX['RightTape']]=2+2*right
    for side in ['Left','Right']:
        for s in range(2): d[INDEX[f'{side}Div{s}']]=Aff(2+(s!=symbol))
    for q in range(15):
        for s in range(2): d[INDEX[f'Trans{chr(65+q)}{s}']]=Aff(1+(q!=state)+(s!=symbol))
    return d

def read_sources():
    raw=(ROOT/'source/UniversalTM15x2.twm.txt').read_bytes()
    mat=json.loads(raw)
    assert len(mat)==47 and {len(r) for r in mat}=={47}
    assert all(type(x) is int and x>=0 for row in mat for x in row)
    assert mat[0]==[47]+[46]*46
    triggers=[r[1:] for r in mat[1:]]
    assert max(map(max,triggers))==12
    assert [i for i,r in enumerate(triggers) if not any(r)]==[INDEX['TransJ1']]
    assert all(triggers[i][i]>0 for i in range(46) if i!=INDEX['TransJ1'])
    assert [r[0] for r in mat[1:]]==[a.at(0,0) for a in canonical(0,0,Aff(),Aff())]
    text=(ROOT/'source/UniversalTM15x2.tm.txt').read_text().splitlines()[0]
    # Independent transcription from Table 16 of Neary--Woods, c=0,b=1,u_i=letter i.
    expected=['0RB1RA','1RC1RA','0LG0LE','0LF1LE','1RA1LD','1LD1LD','0LH1LG','1LI1LG',
              '0RA1LJ','1LK---','0RL1RN','0RM1RL','0LB1RL','0LC0RO','0RN1RN']
    assert text.split('_')==expected
    return mat,triggers,expected,hashlib.sha256(raw).hexdigest()

def symbolic_proof(triggers,table):
    records=[]; checked=0; distinct_constraints=Counter()
    Q,Y=Aff(0,1,0),Aff(0,0,1)
    for q,cell in enumerate(table):
        for symbol in range(2):
            rule=cell[3*symbol:3*symbol+3]
            if rule=='---': continue
            w,direction,newstate=int(rule[0]),rule[1],ord(rule[2])-65
            D='Left' if direction=='L' else 'Right'; O='Right' if D=='Left' else 'Left'
            for r in range(2):
                X=2*Q+r
                left,right=(X,Y) if D=='Left' else (Y,X)
                d=canonical(q,symbol,left,right)
                blocks=[([f'Trans{chr(65+q)}{symbol}'],Aff(1),0,0),
                        ([D+'Div0',D+'Div1'],Q,1,0)]
                if r: blocks.append(([D+'Div0'],Aff(1),0,0))
                blocks += [([D+'Tape'],Aff(1),0,0),([D+'Trans'],Q,1,0),
                           ([D+'Temp'],Aff(1),0,0),([O+'Mult'],Y,0,1),
                           ([O+'Tape'],Aff(1),0,0),([O+'Trans'],2*Y,0,1),
                           ([O+'Temp'],Aff(1),0,0),([O+f'Write{w}'],Aff(1),0,0)]
                for labels,K,qmin,ymin in blocks:
                    ids=[INDEX[name] for name in labels]
                    delta=[sum(triggers[i][j] for i in ids) for j in range(46)]
                    prefix=[0]*46
                    endpoints=[Aff()] if K.v==(1,0,0) else [Aff(),K-1]
                    for i in ids:
                        for endpoint in endpoints:
                            for j in range(46):
                                if j==i:continue
                                gap=d[j]-d[i]+prefix[j]-prefix[i]+endpoint*(delta[j]-delta[i])
                                assert gap.positive_on(qmin,ymin),(q,symbol,r,labels,NAMES[i],NAMES[j],gap.v,qmin,ymin)
                                checked+=1;distinct_constraints[(gap.v,qmin,ymin)]+=1
                        prefix=[a+b for a,b in zip(prefix,triggers[i])]
                    d=[a+K*b for a,b in zip(d,delta)]
                newleft,newright=(Q,2*Y+w) if D=='Left' else (2*Y+w,Q)
                target=canonical(newstate,r,newleft,newright)
                active=INDEX[f'Trans{chr(65+newstate)}{r}']
                common=d[active]-1
                assert all((a-common-b).v==(0,0,0) for a,b in zip(d,target)),(q,symbol,r)
                records.append(dict(state=chr(65+q),symbol=symbol,read_residue=r,
                                    write=w,direction=direction,next=chr(65+newstate),
                                    event_count=[6+r,3,3],physical_time_increment=list(common.v)))
    assert len(records)==58
    return dict(symbolic_macrosteps=len(records),strict_minimum_inequalities=checked,
                distinct_affine_inequalities=len(distinct_constraints),records=records,
                gap_forms=[dict(c=v[0],a=v[1],b=v[2],Q_min=qmin,Y_min=ymin,multiplicity=count)
                           for (v,qmin,ymin),count in sorted(distinct_constraints.items())],
                method='First and last iteration guards of each repeated fixed word; affine coefficients nonnegative after Q>=1/Y>=1 activation shifts.')

def main():
    mat,triggers,table,sha=read_sources()
    proof=symbolic_proof(triggers,table)
    receipt=dict(status='PASS',source_sha256=sha,clocks=46,trigger_entries=2116,
                 trigger_max=12,halt_clock_one_based=28,raw_input_coordinates=['L','R'],
                 loader={'LeftTape':'2+2L','RightTape':'2+2R','operations':4,'multiplications':2,'additions':2},
                 **proof)
    (ROOT/'replay/frontend-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    (ROOT/'replay/affine-gap-forms.json').write_text(json.dumps(proof['gap_forms'],indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k not in ['records','gap_forms']},indent=2))
if __name__=='__main__':main()
