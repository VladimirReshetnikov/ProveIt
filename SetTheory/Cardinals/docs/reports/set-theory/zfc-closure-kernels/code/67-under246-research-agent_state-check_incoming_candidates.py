#!/usr/bin/env python3
"""Validate complete simultaneous covers after bounded action discovery."""
import sys,json,time,itertools,ast,random,argparse
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
from check_merges_symbolic import BASE,affine,build,cases
import check_literal_instructions as literal

def main():
    began=time.monotonic();T=build.build();CC=list(cases());random.Random(82).shuffle(CC)
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--prefix',default='incoming')
    args=ap.parse_args()
    info=json.loads((HERE/(args.prefix+'_action_candidates.json')).read_text());result=[]
    for q,v in info.items():
        q=int(q)
        if not 0<v['combinations']<1000:continue
        keys=[ast.literal_eval(e) for e in v['incoming']]
        for acts in itertools.product(*v['incoming'].values()):
            D={k:row for k,row in T.items() if k[0]!=q}
            for key,(w,d,r) in zip(keys,acts):D[key]=(w,'R' if d==1 else 'L',r)
            assert q not in {r for w,d,r in D.values()}
            DT={(str(a),b):(w,d,str(t)) for (a,b),(w,d,t) in D.items()}
            if q!=48:
                passed=0
                try:
                    for c in CC:affine.run(DT,*c[:3],halt=c[3],fuel=1200);passed+=1
                except (AssertionError,KeyError) as e:status='REJECT';why=str(e)
                else:status='PASS';why='all universal instruction cases'
            else:
                DL={(a,b):(w,1 if d=='R' else -1,t) for (a,b),(w,d,t) in D.items()}
                LS=list(literal.program_sites(BASE/'sources/Prog254.v'));random.Random(827).shuffle(LS)
                passed=0
                try:
                    for pc,kind,r in LS:
                        for positive in ((False,True) if kind=='CD' else (False,)):
                            regs=[(i*3+2)%7 for i in range(9)]
                            if kind=='CD':regs[literal.PHYSICAL[r]]=int(positive)*2
                            literal.run_case(DL,pc,kind,r,regs,[0,1],0,40,10000);passed+=1
                except (AssertionError,KeyError) as e:status='REJECT';why=str(e)[:300]
                else:status='FINITE_PASS';why='full finite instruction regression'
            row=dict(remove=q,patch={str(k):a for k,a in zip(keys,acts)},status=status,cases_before_failure=passed,detail=why)
            result.append(row)
            if status!='REJECT':print(row,flush=True)
            elif len(result)%100==0:print('checked',len(result),'last_deleted_state',q,flush=True)
            if status!='REJECT':
                (HERE/f'candidate_{q}_{len(result)}.tm').write_text(build.encode(D,95))
    (HERE/(args.prefix+'_complete_audit.json')).write_text(json.dumps(result,indent=2))
    print('DONE','candidates',len(result),'seconds',time.monotonic()-began,flush=True)

if __name__=='__main__':main()
