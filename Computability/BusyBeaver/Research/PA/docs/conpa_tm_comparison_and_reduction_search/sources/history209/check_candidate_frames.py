#!/usr/bin/env python3
"""Concrete falsification checks for a changed source tree and exact table."""
from grammar_search import *
sys.path.insert(0,str(OUT.parent/'theory_audit'))
from scan_threshold import frame,run
sys.path.insert(0,str(OUT.parent/'incoming208'))
from compile_ax import tuples

def main():
    src=Path(sys.argv[1]);obj=json.loads(src.read_text());tree=tuples(obj['tree'])
    labels=json.loads(re.search(r'def labels : List Nat := (\[.*\])',(ROOT/'PA196/Conjugacy.lean').read_text()).group(1));inv={v:i for i,v in enumerate(labels)}
    T={(inv[q],b):(w,1 if d=='R' else -1,inv[t]) for q,b,w,d,t in obj['table']}
    flat=flatten(tree);code=resolve(tree);physical=[6,2,0,4,3,7,8,5,1]
    start=time.time();fail=[];checked=0
    for i,((p,leaf),inst) in enumerate(zip(flat,code)):
        if inst[0]=='halt':continue
        for pos in (False,True) if inst[0]=='dec' else (False,):
            vs=[0]*10+[1]*25
            if inst[0]=='dec' and pos:vs[physical[inst[1]]]=1
            ws=vs.copy();gap=0
            if inst[0]=='inc':ws[physical[inst[1]]]+=1;ws.append(1);j=inst[2]
            elif inst[0]=='dec':
                if pos:ws[physical[inst[1]]]-=1;gap=1;j=inst[3]
                else:j=inst[2]
            else:j=inst[1]
            if j is None:j=0
            st=frame(p,vs);target=frame(flat[j][0],ws,gap)
            result=run(T,st,target)
            checked+=1
            if result[0] is None or result[1]!=target:
                print('FAIL',i,p,inst,pos,result[2],flush=True);fail.append(i)
                if len(fail)>=4:break
        if len(fail)>=4:break
    record={'failures':fail,'instruction_cases':checked,'source_sites':len(flat),'seconds':time.time()-start}
    print('DONE',record,flush=True)
    src.with_suffix('.checks.json').write_text(json.dumps(record,indent=2))

if __name__=='__main__':main()
