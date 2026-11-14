#!/usr/bin/env python3
"""All 28 N-fixed register transpositions: exact tables, frame checks, folds."""
from register_permutation import *
from itertools import combinations
sys.path.insert(0,str(OUT.parent/'theory_audit'))
from scan_threshold import frame,run
sys.path.insert(0,str(OUT.parents[1]/'research'))
from search_folds import reachable,search

def main():
    dest=OUT/'register_catalog';dest.mkdir(exist_ok=True)
    labels=json.loads(re.search(r'def labels : List Nat := (\[.*\])',(ROOT/'PA196/Conjugacy.lean').read_text()).group(1));inv={v:i for i,v in enumerate(labels)}
    ns=parse_program();tree=ns['trie'];flat=flatten(tree);code=resolve(tree)
    baseline=ca.native();start=time.time();records=[]
    for a,b in combinations([0,1,2,3,4,5,7,8],2):
        p=list(range(9));p[a],p[b]=p[b],p[a]
        T=permute(baseline,p);rows={(inv[q],bit):(w,1 if d=='R' else -1,inv[t]) for(q,bit),(w,d,t) in T.items()}
        fn=dest/f'swap_{a}_{b}.tm'
        fn.write_text(''.join(f'{q} {bit} {w} {"R" if d==1 else "L"} {t}\n' for(q,bit),(w,d,t) in sorted(rows.items())))
        phy=[p[i] for i in PHYSICAL];fails=[];checked=0
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
                    fails.append({'site':i,'positive':pos,'instruction':inst,'visits':res[2]});break
            if fails:break
        # The same blank clean frame is expected because N stays at physical6.
        goal=frame(flat[25][0],[0,0,0,0,0,0,2,0,0]+[1]*26)[2]
        q=h=0;tape=set();startup=None;halted=False
        for step in range(500000):
            if q==75 and len(tape)==len(goal) and {x-h for x in tape}==goal:
                startup=step;break
            if (q,int(h in tape)) not in rows:halted=True;break
            w,d,q=rows[q,int(h in tape)]
            if w:tape.add(h)
            else:tape.discard(h)
            h+=d
        reach=reachable(rows,4);hits=search(rows,reach,4)
        rec={'swap':[a,b],'permutation':p,'physical_registers':phy,'table':fn.name,
             'states':196,'frame_cases_checked':checked,'frame_failures':fails,
             'startup_to_candidate2':startup,'halted_before_target':halted,
             'abstract_window_radius':4,'abstract_windows':sum(map(len,reach)),
             'folds':hits,'elapsed_seconds':time.time()-start}
        records.append(rec);(dest/'receipt.json').write_text(json.dumps(records,indent=2))
        print('SWAP',a,b,'framefails',len(fails),'startup',startup,'folds',len(hits),'sec',time.time()-start,flush=True)
        if hits:break
        if time.time()-start>170:break
    print('DONE',len(records),'folds',sum(len(x['folds']) for x in records),'seconds',time.time()-start,flush=True)

if __name__=='__main__':main()
