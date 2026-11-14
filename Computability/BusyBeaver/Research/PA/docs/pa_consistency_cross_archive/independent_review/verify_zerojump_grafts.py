#!/usr/bin/env python3
"""Independent zero/positive closure and exact edit checks for two grafts."""
from collections import deque
import json
import verify_grafts as v

def successors(code, pc, mask):
    row = code[pc]
    if row[0] == 'halt':
        return ()
    if row[0] == 'jump':
        return ((row[1],mask),)
    bit = 1 << row[1]
    if row[0] == 'inc':
        return ((row[2],mask|bit),)
    v.require(row[0] == 'dec','unknown source command')
    if mask & bit:
        return ((row[3],mask & ~bit),(row[3],mask))
    return ((row[2],mask),)

def closure(code):
    reached = {(25,1)}
    pending = deque(reached)
    while pending:
        pc,mask = pending.popleft()
        for item in successors(code,pc,mask):
            v.require(0<=item[0]<len(code) and 0<=item[1]<512,'abstract state out of range')
            if item not in reached:
                reached.add(item)
                pending.append(item)
    v.require(all(item in reached for pc,mask in reached for item in successors(code,pc,mask)),
              'closure not preserved by every abstract successor')
    return reached

def main():
    for entry in json.loads((v.ROOT/'input_manifest.json').read_text()):
        v.require(v.digest((v.INP/entry['file']).read_bytes())==entry['sha256'],'changed input')
    previous={e['canonical_sha256'] for e in v.get('prior_selected196.json')['tables']}
    for i in range(2):
        previous.add(v.canonical(v.read_machine(v.INP/f'candidate_{i}_machine.tm'),0)[0])
    result=[]
    for i,expected_pairs in enumerate((265964,263244)):
        before=v.load_sites(f'candidate_{i}_sites.json')
        after=v.load_sites(f'zerojump_{i}_sites.json')
        differences=[j for j,(a,b)in enumerate(zip(before,after))if a!=b]
        v.require(len(before)==len(after) and differences==[26],'source edit not confined to26')
        v.require(before[26][1:]==('breakTo',1) and after[26]==(before[26][0],'dec',6),'wrong source26 replacement')
        B,A=v.resolve(before),v.resolve(after)
        v.require(B[26]==('jump',34) and A[26]==('dec',6,34,27),'wrong source26 successors')
        v.require(all(a==b for j,(a,b)in enumerate(zip(A,B))if j!=26),'other resolved edges changed')
        rb,ra=closure(B),closure(A)
        v.require(rb==ra and len(ra)==expected_pairs,'original and changed invariant closures differ')
        masks=sorted(mask for pc,mask in ra if pc==26)
        v.require(masks and all(mask&64==0 for mask in masks),'R6 not always zero at26')
        given=v.get(f'zerojump_{i}_invariant.json')
        v.require(given['pairs']==len(ra) and given['site26_masks']==masks,'reported invariant mismatch')
        # Identical exact source transitions on the common inductive set.
        v.require(all(successors(A,pc,mask)==successors(B,pc,mask)for pc,mask in ra),
                  'abstract transitions differ on the joint invariant')
        native_old=v.read_machine(v.INP/f'candidate_{i}_machine.native.tm')
        native_new=v.read_machine(v.INP/f'zerojump_{i}_machine.native.tm')
        v.require(set(native_old)==set(native_new),'working-state domains changed')
        keys=[key for key in native_old if native_old[key]!=native_new[key]]
        v.require(keys==[(27,1)] and native_old[27,1]==(0,'L',40) and native_new[27,1]==(1,'R',21),
                  'unexpected literal edit')
        labels=v.get(f'zerojump_{i}_labels.json')
        v.require(labels==v.get(f'candidate_{i}_labels.json'),'state naming changed')
        dense=v.read_machine(v.INP/f'zerojump_{i}_machine.tm')
        v.require({(labels[q],b):(w,d,labels[t])for(q,b),(w,d,t)in dense.items()}==native_new,'dense/native map differs')
        h,reach=v.canonical(dense,0)
        v.require(reach==196 and h not in previous,'non-new graph or inaccessible working state')
        previous.add(h)
        result.append({'candidate':i,'source_sites':len(after),'source_change':{'site':26,'before':list(B[26]),'after':list(A[26])},
                       'common_inductive_pairs':len(ra),'site26_masks':masks,'R6_zero_at26':True,
                       'common_inductive_set_sha256':v.digest(json.dumps(sorted(ra),separators=(',',':')).encode()),
                       'working_states':len(dense)//2,'graph_reachable':reach,'action_bisimulation_classes':v.bisimulation(dense),
                       'canonical_sha256':h,'table_sha256':v.digest((v.INP/f'zerojump_{i}_machine.tm').read_bytes()),
                       'startup':v.full_startup(dense,labels,after[25][0],58168)})
    print(json.dumps({'status':'PASS','scope':'Independent exact source edit, common inductive abstraction, table edit, conjugacy, whole-tape startup, and graph checks. Physical instruction simulation and PA-calibration proofs are separate.',
                      'records':result},indent=2))

if __name__=='__main__':
    main()
