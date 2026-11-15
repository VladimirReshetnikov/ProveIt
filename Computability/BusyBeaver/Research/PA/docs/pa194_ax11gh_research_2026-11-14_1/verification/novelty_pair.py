#!/usr/bin/env python3
"""Exact action-graph novelty for two candidate TMs against the pinned frontier.

State renaming, arbitrary spanning roots, reflection, global bit exchange,
and ignored terminal-edge write/move effects are all admitted. Graph identity
does not prove semantic novelty or a consistency equivalence.
"""
from pathlib import Path
from collections import Counter
from hashlib import sha256
import argparse, json
import literal_inventory as lib

def invariant(data):
    rows,states,halt=data
    indegree=Counter(t for w,d,t in rows.values() if t in states)
    profile=sorted((indegree[q],sum(rows[q,b][2]==q for b in (0,1)),rows[q,0][2]==rows[q,1][2]) for q in states)
    return profile

def canonical(data,root,reflect=False,complement=False):
    rows,states,halt=data
    labels={root:0};todo=[root];answer=[]
    for q in todo:
        pair=[]
        for b in (0,1):
            w,d,t=rows[q,b^complement]
            if t==halt:
                # Intentionally erase the final write and move.
                pair.append((0,'R',-1));continue
            if t not in labels:labels[t]=len(todo);todo.append(t)
            pair.append((w^complement,('R' if d=='L' else 'L') if reflect else d,labels[t]))
        answer.append(tuple(pair))
    return tuple(answer) if len(todo)==len(states) else None

def compare(candidate,reference):
    if len(candidate[1])!=len(reference[1]):return {'matched':False,'reason':'different working-state counts'}
    if invariant(candidate)!=invariant(reference):return {'matched':False,'reason':'different indegree/self-loop state-profile multisets'}
    c=canonical(candidate,0)
    assert c is not None,'candidate start zero must reach all controls'
    trials=0
    for reflection in (False,True):
        for complementation in (False,True):
            for root in sorted(reference[1]):
                trials+=1
                if canonical(reference,root,reflection,complementation)==c:
                    return {'matched':True,'root':root,'reflection':reflection,'complementation':complementation,'root_mode_trials':trials}
    return {'matched':False,'reason':'exact rooted canonical tuples differ for every root and symmetry','root_mode_trials':trials}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('candidates',nargs='+',type=Path)
    ap.add_argument('--manifest',type=Path,default=Path(__file__).resolve().parent/'search_frontier194/manifest.json')
    ap.add_argument('--output',type=Path,default=Path(__file__).resolve().parent/'novelty_pair_receipt.json')
    a=ap.parse_args();prior=json.loads(a.manifest.read_text())
    references=[]
    for r in prior:
        p=Path(r['table'])
        if not p.exists():p=a.manifest.parent/p.name
        b=p.read_bytes();data=lib.parse_table(b);assert data and len(data[1])==194
        txt=''.join(f'{q} {bit} {w} {d} {t}\n' for (q,bit),(w,d,t) in sorted(data[0].items()))
        assert sha256(txt.encode()).hexdigest()==r['normalized_sha256']
        references.append((r,data))
    result={'snapshot':'1e1a41f799d4658b829cdd0eabae3775a0c8c4a0',
            'scope':__doc__,'reference_spanning_classes':len(references),'candidates':[]}
    candidates=[]
    for path in a.candidates:
        b=path.read_bytes();data=lib.parse_table(b);assert data and len(data[1])==194
        c=canonical(data,0);assert c is not None
        checks=[{'reference_table_class':r['table_class'],'name':r['name'],**compare(data,d)} for r,d in references]
        item={'path':str(path),'sha256':sha256(b).hexdigest(),'states':len(data[1]),'rows':len(data[0]),
              'start':0,'halt':data[2],'matches':sum(x['matched'] for x in checks),
              'root_zero_loose_canonical':c,'invariant_profile':invariant(data),'checks':checks}
        result['candidates'].append(item);candidates.append(data)
    result['pairwise']=[{'left':i,'right':j,**compare(candidates[i],candidates[j])}
                        for i in range(len(candidates)) for j in range(i+1,len(candidates))]
    assert all(c['matches']==0 for c in result['candidates'])
    assert not any(c['matched'] for c in result['pairwise'])
    a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'reference_spanning_classes':len(references),'candidate_sha256s':[c['sha256'] for c in result['candidates']],
       'matches':[c['matches'] for c in result['candidates']],'pairwise':result['pairwise'],
       'exact_tuple_compared_references':[sum('root_mode_trials' in x for x in c['checks']) for c in result['candidates']]},indent=2))
if __name__=='__main__':main()
