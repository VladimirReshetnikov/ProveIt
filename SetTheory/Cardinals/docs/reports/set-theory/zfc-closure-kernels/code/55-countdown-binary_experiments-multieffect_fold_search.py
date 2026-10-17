"""Revisit all 55,471 frozen-support uniform folds with a richer relation."""
import common as c
import multieffect as m
from collections import defaultdict,Counter
import hashlib,json,time
from pathlib import Path

BOX_STATES={0,1,2,3,4,6,28,31,38,40,43,44,48,56,59,60,63,64,69,73,75,83,85,95,97,109,112,131}
PROTECTED={(str(q),b) for q in BOX_STATES for b in (0,1)}-{('3',0)}
RESULT_STEM='multieffect_fold_results'

class Tracking(dict):
    def __init__(self, rows):super().__init__(rows);self.used=set()
    def __getitem__(self,key):self.used.add(key);return super().__getitem__(key)

def one(table,i):
    p,op,r,z,branch,target=c.CASES[i]
    try:
        rules,literal=c.strict.run(table,p,branch,target,halt=op=='CH',fuel=1000)
        assert literal>0
        return True,sum(rules.values()),None
    except (AssertionError,KeyError) as e:return False,0,str(e)

def main():
    m.install();begin=time.monotonic()
    usage=defaultdict(list)
    for i in range(len(c.CASES)):
        traced=Tracking(c.T);ok,cost,reason=one(traced,i)
        assert ok,('baseline',i,reason)
        for q in {q for q,b in traced.used}:usage[q].append((cost,i))
    for group in usage.values():group.sort()
    states=sorted({q for q,b in c.T},key=int)
    protected_targets={c.T[k][2] for k in PROTECTED}
    eligible=[q for q in states if q!='96' and q not in protected_targets and all((q,b) not in PROTECTED for b in (0,1))]
    assert len(eligible)==221
    result={'baseline_cases':len(c.CASES),'scope':'Universal affine primary effects; existential valid spares. Same four box contracts. Unknown new guards reject. No kernel proof or impossibility claim.',
            'planned':len(eligible)*251,'completed':0,'checks':0,'survivors':[],'failures':Counter(),'failures_by_case':Counter(),'groups':[],'macro_counts':None}
    print('BASELINE',len(c.CASES),dict(m.STATS),flush=True)
    out=Path(__file__).parent/(RESULT_STEM+'.json')
    with out.with_suffix('.jsonl').open('w') as journal:
        for n,dead in enumerate(eligible):
            group={'deleted':int(dead),'failures':[]};result['groups'].append(group)
            for replacement in states:
                if replacement==dead:continue
                table=c.fold(c.T,dead,replacement)
                assert all(table[k]==c.T[k] for k in PROTECTED)
                failure=None
                for _,i in usage[dead]:
                    ok,_,reason=one(table,i);result['checks']+=1
                    if not ok:failure=(i,reason);break
                if failure is None:
                    for i in range(len(c.CASES)):
                        ok,_,reason=one(table,i);result['checks']+=1
                        if not ok:failure=(i,reason);break
                result['completed']+=1
                if failure is None:
                    result['survivors'].append([int(dead),int(replacement)])
                    print('SURVIVOR',dead,replacement,flush=True)
                    raw='#! start 64\n'+''.join(f'{q} {b} {w} {d} {t}\n' for(q,b),(w,d,t) in sorted(table.items(),key=lambda x:(int(x[0][0]),x[0][1])))
                    out.with_name(f'multieffect_fold_{dead}_{replacement}.tm').write_text(raw)
                else:
                    i,reason=failure
                    result['failures'][reason.split("'",2)[1] if "'" in reason else reason]+=1
                    result['failures_by_case'][i]+=1
                    group['failures'].append([int(replacement),i,reason])
                journal.write(json.dumps({'deleted':int(dead),'replacement':int(replacement),'failure':failure})+'\n')
            if n%20==0:
                print('PROGRESS',n,dead,result['completed'],result['checks'],len(result['survivors']),time.monotonic()-begin,flush=True)
    result['elapsed']=time.monotonic()-begin;result['macro_counts']=dict(m.STATS)
    result['failures']=dict(result['failures']);result['failures_by_case']=dict(result['failures_by_case'])
    result['journal_sha256']=hashlib.sha256(out.with_suffix('.jsonl').read_bytes()).hexdigest()
    out.write_text(json.dumps(result,indent=2)+'\n')
    print('DONE',result['completed'],result['checks'],result['survivors'],result['elapsed'],flush=True)

if __name__=='__main__':main()
