#!/usr/bin/env python3
"""Independent finite proof checker for the eighteen new 208-state layouts.

Uses only the complete one-step incoming census and exact two-cell blocks.
No numpy, random samples, window fixed point, or machine simulator oracle.
The mathematical interpretation of its finite checks is in report.tex.
"""
from pathlib import Path
import argparse, hashlib, json

def require(ok, message):
    if not ok:
        raise ValueError(message)

def read(path,halt=254):
    rows={}
    require(path.read_text().splitlines()[0].strip()=='#! start 0', 'Unexpected initial state declaration')
    for line in path.read_text().splitlines():
        if not line.strip() or line.startswith('#'):
            continue
        q,b,w,d,z=line.split()
        key=int(q),int(b)
        require(key[0]>=0 and key[1] in (0,1),'Bad state or scanned symbol')
        require(key not in rows, 'Duplicate transition')
        require(d in ('L','R'), 'Bad direction')
        rows[key]=int(w),(-1 if d=='L' else 1),int(z)
    states={q for q,b in rows}
    require(all((q,b) in rows for q in states for b in (0,1)), 'Incomplete table')
    require(all(w in (0,1) and z in states|{halt} for w,d,z in rows.values()), 'Invalid transition')
    require(halt not in states, 'Halt has outgoing rows')
    return rows

def canonical(rows):
    names={0:0};queue=[0];result=[]
    for q in queue:
        for b in (0,1):
            w,d,z=rows[q,b]
            if z==254:
                target=-1
            else:
                if z not in names:
                    names[z]=len(names);queue.append(z)
                target=names[z]
            result.append([w,d,target])
    require(len(names)==len(rows)//2, 'Not every working state is graph-reachable')
    return hashlib.sha256(json.dumps(result,separators=(',',':')).encode()).hexdigest()

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1])
    p.add_argument('--output',type=Path)
    args=p.parse_args();root=args.root.resolve()
    history=root/'upstream/U208_ConPA_History_2026-10-29/U208_ConPA_History_2026-10-29/machine'
    experiments=root/'analysis/comparison/double_helper'
    results=[];canonical_hashes=set();baseline_hashes=set()
    for label,part in [('A',''),('B','compatibility_variant')]:
        base=read(history/part/'u208.native.tm')
        require(len(base)==416, 'Wrong baseline size')
        baseline_hashes.add(canonical(base))
        inventory=json.loads((experiments/f'augmented_results_{label}.json').read_text())
        require(len(inventory)==9,'Expected nine donor signatures')
        for item in inventory:
            drop,keep,bit,x0,x1,w0,w1=item['parameters']
            require(drop!=0 and keep!=0 and 500 not in {q for q,b in base}, 'Initial/helper conflict')
            pi=lambda q: keep if q==drop else q
            expected={(q,b):(w,d,pi(z)) for (q,b),(w,d,z) in base.items() if q!=drop}
            expected[keep,bit]=(bit,-1,500)
            expected[500,0]=(w0,1,pi(x0));expected[500,1]=(w1,1,pi(x1))
            directory=root/item['directory']
            path=directory/'machine.native.tm';candidate=read(path)
            require(candidate==expected,'Literal table does not match declared patch')
            require(len(candidate)==416,'Not 208 working states')
            dense_path=directory/'machine.dense.tm'
            if dense_path.exists():
                mapping=json.loads((directory/'dense_state_map.json').read_text())
                rename={int(q):z for q,z in mapping['native_to_dense'].items()}
                require(set(rename)=={q for q,b in candidate} and set(rename.values())==set(range(208)), 'Bad dense bijection')
                require(rename[0]==0 and mapping['dense_halt']==208 and mapping['native_halt']==254, 'Bad dense endpoints')
                dense=read(dense_path,halt=208)
                expected_dense={(rename[q],b):(w,d,208 if z==254 else rename[z])
                                for (q,b),(w,d,z) in candidate.items()}
                require(dense==expected_dense,'Dense/native row mismatch')
                require(hashlib.sha256(dense_path.read_bytes()).hexdigest()==mapping['dense_sha256'],'Dense file hash mismatch')
            tags={};incoming={}
            for q in (drop,keep):
                inc=[(s,b,w,d) for (s,b),(w,d,z) in base.items() if z==q]
                require(inc and all(d==1 for s,b,w,d in inc),'Incoming edge is not a right move')
                values={w for s,b,w,d in inc}
                require(len(values)==1,'No unconditional predecessor-bit tag')
                tags[q]=values.pop();incoming[q]=inc
            blocks=[]
            for q in (drop,keep):
                for b in (0,1):
                    before={-1:tags[q],0:b};tape=dict(before);head=0;state=keep
                    ow,od,oz=base[q,b];target_tape=dict(before);target_tape[0]=ow
                    trace=[]
                    for steps in range(1,128):
                        require(state!=254,'Interior halt')
                        require(head in tape,'Unspecified exterior tape read')
                        scanned=tape[head];w,d,z=candidate[state,scanned]
                        trace.append([state,head,scanned,w,d,z])
                        tape[head]=w;head+=d;state=z
                        if (state,head,tape)==(pi(oz),od,target_tape):
                            break
                    else:
                        raise ValueError('No positive bounded exact match')
                    blocks.append({'old_state':q,'read':b,'left_bit':tags[q],
                                   'steps':steps,'trace':trace})
            for key,row in base.items():
                q,b=key
                if q in (drop,keep):
                    continue
                w,d,z=row
                require(candidate[q,b]==(w,d,pi(z)),'An ordinary row does not commute')
            graph_hash=canonical(candidate)
            require(graph_hash not in canonical_hashes,'Two new graphs are isomorphic')
            require(graph_hash not in baseline_hashes,'New graph equals a baseline')
            canonical_hashes.add(graph_hash)
            results.append({'class':label,'parameters':item['parameters'],
                'machine':str(path.relative_to(root)),
                'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
                'canonical_sha256_checker_serialization':graph_hash,
                'working_states':208,'incoming_census':incoming,'local_blocks':blocks,
                'ordinary_rows_commute':True,'initial_state_preserved':True})
    require(len(canonical_hashes)==18 and len(baseline_hashes)==2,'Graph class count')
    require(not canonical_hashes.intersection(baseline_hashes),'Baseline/new graph overlap')
    report={'status':'PASS','machines':18,'working_states_each':208,
            'distinct_new_graph_classes':18,'proof_method':'one-step incoming tags and exact positive local blocks',
            'all_initial_tapes':True,'no_claim_below_208':True,'results':results}
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='results'},indent=2))

if __name__=='__main__':
    main()
