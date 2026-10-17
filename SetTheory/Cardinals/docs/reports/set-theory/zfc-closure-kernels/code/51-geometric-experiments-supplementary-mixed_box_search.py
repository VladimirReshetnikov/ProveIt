#!/usr/bin/env python3
"""Mixed-row box merges, finite literal samples then conditional affine cases.

This deliberately extends the repository's uniform protected-state folds.
No sample or oracle accepted here is an unbounded proof of a modified box.
"""
from pathlib import Path
import sys, json, time, hashlib, tempfile, argparse
from collections import Counter

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--repo',type=Path,required=True,
                    help='ProveIt checkout at the pinned inspection commit')
parser.add_argument('--output',type=Path,default=Path(__file__).with_name('mixed_box_results.json'))
args=parser.parse_args()
REPO=args.repo.resolve()
sys.path.insert(0,str(REPO/'Computability/BusyBeaver/Research/ZFC'))
import candidate252_independent_audit as b
import breakthrough_register_permutation as a
import permutation252_spare_fold_search as s

def main():
    start_time=time.monotonic()
    table=b.read_table((REPO/'Computability/BusyBeaver/Research/ZFC/candidate-permutation252/zfc_permutation252_old.tm').read_bytes())
    states=sorted({q for q,_ in table})
    protected_targets={table[k][2] for k in b.BOX_PAIRS}
    deleted=sorted((b.BOX_STATES|protected_targets)-{96})
    cases=list(s.samples()); usage=[]
    for i,c in enumerate(cases):
        ok,reason,used,_=s.run(table,c,2000)
        assert ok,('baseline',i,reason)
        usage.append(used)
    result={'status':'running','description':__doc__,'baseline_samples':len(cases),
            'sources':{'table_sha256':b.EXPECTED_SHA},'tested':0,'failures':[],'sample_survivors':[],
            'conditional_runtime':[],'candidate_samples':0}
    targets=[q for q in states if q!=96]
    recipes=[(q,r,bit) for q in deleted for r in targets if r!=q for bit in (0,1)
             if table[q,bit]!=table[r,bit]]
    result['planned']=len(recipes)
    for dead,target,bit in recipes:
        changed={k:(w,d,target if t==dead else t) for k,(w,d,t) in table.items() if k[0]!=dead}
        w,d,t=table[dead,bit]; changed[target,bit]=(w,d,target if t==dead else t)
        affected={k for k,(_,_,t) in table.items() if k[0]==dead or t==dead}|{(target,bit)}
        order=sorted(range(len(cases)),key=lambda i:not bool(usage[i]&affected))
        fail=None
        for i in order:
            ok,reason,_,ticks=s.run(changed,cases[i],2000,dead,target)
            result['candidate_samples']+=1
            if not ok:fail=[dead,target,bit,i,reason,ticks];break
        result['tested']+=1
        if fail is None:result['sample_survivors'].append([dead,target,bit])
        else:result['failures'].append(fail)
    print('SAMPLES',len(recipes),'survivors',len(result['sample_survivors']),flush=True)
    scratch=Path(tempfile.mkdtemp(prefix='mixed-box-affine-'))
    result['affine_inputs']=a.prepare(REPO,scratch)
    original_oracle=a.strict.oracle
    ordinary={(str(q),bit):(w,d,str(t)) for (q,bit),(w,d,t) in table.items()}
    assert a.certify(ordinary,b.PERM)['passed']
    for dead,target,bit in result['sample_survivors']:
        dead,target=str(dead),str(target)
        def relocated(q,branch,state):
            origins=[q]+([dead] if q==target else [])
            answers=[]
            for origin in origins:
                answer=original_oracle(origin,branch,state)
                if answer is None:continue
                exit_state,effect=answer
                answers.append((target if exit_state==dead else exit_state,effect))
            assert len(set(answers))<=1,('ambiguous macro',dead,target,bit,q,branch,state,answers)
            return answers[0] if answers else None
        a.strict.oracle=relocated
        changed={k:(w,d,target if t==dead else t) for k,(w,d,t) in ordinary.items() if k[0]!=dead}
        w,d,t=ordinary[dead,bit];changed[target,bit]=(w,d,target if t==dead else t)
        check=a.certify(changed,b.PERM)
        record={'deleted':dead,'target':target,'mixed_bit':bit,**check}
        if check['passed']:
            (Path(__file__).parent/f'candidate_{dead}_{target}_{bit}.tm').write_bytes(a.encoded(changed))
            print('RUNTIME SURVIVOR',record,flush=True)
        result['conditional_runtime'].append(record)
    a.strict.oracle=original_oracle
    result['conditional_survivors']=[c for c in result['conditional_runtime'] if c['passed']]
    result['status']='complete';result['elapsed_seconds']=time.monotonic()-start_time
    result['failure_counts']=dict(Counter(f[4] for f in result['failures']))
    out=args.output;out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('status','planned','tested','candidate_samples','elapsed_seconds','failure_counts','conditional_survivors')},indent=2),flush=True)

if __name__=='__main__':main()
