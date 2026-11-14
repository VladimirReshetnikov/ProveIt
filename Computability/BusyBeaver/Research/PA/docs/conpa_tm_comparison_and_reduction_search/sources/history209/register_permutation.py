#!/usr/bin/env python3
"""Permute register targets of unchanged PA196 instruction decoders."""
from grammar_search import *
sys.path.insert(0,str(OUT.parent/'incoming208'))
import compile_ax as ca
SK=[51,36,25,48,32,33,22,55,60]
BOX={0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198}
PHYSICAL=[6,2,0,4,3,7,8,5,1]

def permute(T,p):
    assert sorted(p)==list(range(9))
    return {k:(w,d,SK[p[SK.index(q)]] if q in SK and k[0] not in BOX else q)
            for k,(w,d,q) in T.items()}

def main():
    sys.path.insert(0,str(OUT.parent/'theory_audit'))
    from scan_threshold import frame,run
    p=list(range(9));a,b=map(int,sys.argv[1:3]);p[a],p[b]=p[b],p[a]
    T=permute(ca.native(),p)
    labels=json.loads(re.search(r'def labels : List Nat := (\[.*\])',(ROOT/'PA196/Conjugacy.lean').read_text()).group(1));inv={v:i for i,v in enumerate(labels)}
    rows={(inv[q],b):(w,1 if d=='R' else -1,inv[t]) for(q,b),(w,d,t) in T.items()}
    ns=parse_program();tree=ns['trie'];flat=flatten(tree);code=resolve(tree);phy=[p[i] for i in PHYSICAL]
    start=time.time();fails=[];checked=0
    for i,((path,leaf),inst) in enumerate(zip(flat,code)):
        if inst[0]=='halt':continue
        for pos in (False,True) if inst[0]=='dec' else (False,):
            vs=[0]*10+[1]*25
            if inst[0]=='dec' and pos:vs[phy[inst[1]]]=1
            ws=vs.copy();gap=0
            if inst[0]=='inc':ws[phy[inst[1]]]+=1;ws.append(1);j=inst[2]
            elif inst[0]=='dec':
                if pos:ws[phy[inst[1]]]-=1;gap=1;j=inst[3]
                else:j=inst[2]
            else:j=inst[1]
            if j is None:j=0
            st=frame(path,vs);target=frame(flat[j][0],ws,gap);res=run(rows,st,target);checked+=1
            if res[0] is None or res[1]!=target:
                print('FAIL',i,inst,pos,res[2],flush=True);fails.append(i)
                if len(fails)>=3:break
        if len(fails)>=3:break
    obj={'permutation':p,'physical':phy,'failures':fails,'cases':checked,'seconds':time.time()-start}
    print('DONE',obj,flush=True)
    (OUT/f'register_swap_{a}_{b}.json').write_text(json.dumps(dict(obj,tree=tree,table=[[q,b,*v] for(q,b),v in T.items()])))

if __name__=='__main__':main()
