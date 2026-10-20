#!/usr/bin/env python3
"""Concrete diagnostic for the boot-only row36 repairs; no general proof."""
from pathlib import Path
import json,sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'baseline219/K219_Construction_2026-10-20/portable'))
import common as c

def run(T,pc,vals,spares,gap=12):
    phys=[None]*9
    for i,j in enumerate(c.PHY):phys[j]=vals[i]
    ones={-1,64+gap}|{i for i,v in enumerate(pc)if v=='1'};p=65+gap
    for v in phys+spares:
        p+=1;ones.update(range(p,p+v+1));p+=v+1
    q=h=0;q=84;visits=[]
    for k in range(200000):
        if q==254:return {'status':'HALT','steps':k}
        w,d,q=T[q,int(h in ones)]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=d
        if q!=84:continue
        if len(visits)<20:visits.append([k+1,h,sorted(ones)])
        if not ones or min(ones)!=h-1:continue
        # Search each plausible header after the bounded source-code field.
        for header in sorted(x for x in ones if x>=h+40):
            p=header+1;values=[];valid=True
            while p<=max(ones):
                if p in ones or p+1 not in ones:valid=False;break
                p+=1;n=0
                while p in ones:n+=1;p+=1
                values.append(n-1)
            if valid and len(values)>=10 and all(x<h+38 for x in ones if h<=x<header):
                logical=[values[j]for j in c.PHY]
                bits=''.join(str(int(i in ones))for i in range(h,header))
                return {'status':'FRAME','steps':k+1,'head':h,'header':header,'prefix':bits.rstrip('0'),
                        'registers':logical,'spares':values[9:],'visits':visits}
        if len(visits)>=20:return {'status':'NO_RECOGNIZED_FRAME','visits':visits}
    return {'status':'BOUND','visits':visits,'q':q,'h':h,'ones':len(ones)}

def main():
    tables={n:c.parse_table((ROOT/p).read_bytes())for n,p in [
        ('core218','root218/candidate218/candidate.tm'),
        ('boot36to6','root218/candidate218/boot36to6/candidate.tm'),
        ('boot36to10','root218/candidate218/boot36to10/candidate.tm')]}
    records=[]
    for vals in [[0]*9,[0,0,1,0,0,0,0,0,0],[1,2,3,4,5,6,7,8,0]]:
        for name,T in tables.items():
            ans=run(T,'000',vals,[3,4,5]);record=dict(table=name,initial=vals,**ans);records.append(record)
            print(json.dumps({k:v for k,v in record.items()if k!='visits'}),flush=True)
    (ROOT/'root218/candidate218/boot36_semantics.json').write_text(json.dumps(records,indent=2)+'\n')
if __name__=='__main__':main()
