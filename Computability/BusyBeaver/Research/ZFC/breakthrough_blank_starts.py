#!/usr/bin/env python3
"""Test exact first-write blank-start classes across64 register permutations.

Every zero-writing prefix leaves the whole tape blank. After the first1 write,
translation to head0 leaves exactly one1 at offset±1 and a known state. Equal
normalized configurations therefore have identical subsequent executions.
An all-zero state cycle never writes1 or halts, even if its head drifts.

No affine audit is repeated: each generated table must match a previously
recorded8391-case permutation success, and allread0 rows must equal baseline.
The frame detector and sufficient Safe certificate have the explicitly limited
scope documented in breakthrough_register_permutation.py. This is finite
search evidence, not a binary/refinement/consistency theorem.
"""
from __future__ import annotations
import argparse
from collections import Counter,defaultdict
import hashlib
import json
from pathlib import Path
import platform
import sys
import tempfile
import time

import breakthrough_register_permutation as perm

ROOT=Path(__file__).resolve().parents[4]
RESULTS=ROOT/'Computability/BusyBeaver/Research/ZFC/results'


def start_classes(table):
    groups=defaultdict(list)
    for start in sorted({q for q,_ in table},key=int):
        q=start;head=0;seen={};path=[]
        while q not in seen:
            if q=='254':
                key=('halt_without_writing',);detail={};break
            seen[q]=len(path)
            w,d,nxt=table[q,0]
            path.append({'state':q,'head_before':head,'read':0,'write':w,'move':d,'target':nxt})
            head+=1 if d=='R' else -1
            if w:
                offset=-1 if d=='R' else 1
                key=(nxt,offset)
                detail={'normalized_state':nxt,'normalized_head':0,'normalized_ones':[offset],
                        'head_translation':head};break
            q=nxt
        else:
            key=('blank_cycle',)
            detail={'cycle_start_index':seen[q],
                    'cycle_head_displacement':head-path[seen[q]]['head_before']}
        groups[key].append({'start':start,'prefix_steps':len(path),'literal_zero_read_path':path,**detail})
    return [{'class':list(k),'members':v} for k,v in groups.items()]


def literal(table,start,offset,mapping,limit):
    # Dense transitions speed only lookup; each loop executes one literal row.
    rows=[None]*255
    for q in {q for q,_ in table}:rows[int(q)]=[table[q,0],table[q,1]]
    rows=[None if r is None else[(w,1 if d=='R' else -1,int(t)) for w,d,t in r] for r in rows]
    q=int(start);head=0;ones={offset};roots=[]
    for steps in range(limit+1):
        if q==96:
            frame=perm.parse_root('96',head,ones,mapping)
            if frame is not None:
                frame['normalized_steps_after_first_write']=steps;roots.append(frame)
                if frame['safe_certificate'] is not None:
                    return {'outcome':'sufficient_Safe_structural_frame','steps':steps,'frame':frame,'roots':roots}
        if q==254:return {'outcome':'halt','steps':steps,'head':head,'one_count':len(ones),'roots':roots}
        if steps==limit:
            return {'outcome':'fuel_limit','steps':steps,'state':q,'head':head,
                    'one_count':len(ones),'ones_sha256':hashlib.sha256(json.dumps(sorted(ones)).encode()).hexdigest(),'roots':roots}
        w,delta,q=rows[q][int(head in ones)]
        if w:ones.add(head)
        else:ones.discard(head)
        head+=delta


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo',type=Path,default=ROOT)
    p.add_argument('--scratch',type=Path)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--limit',type=int,default=1000000)
    args=p.parse_args()
    if not __debug__:p.error('Assertions must remain enabled')
    if args.limit<1:p.error('Positive literal fuel required')
    repo=args.repo.resolve()
    work=args.scratch.resolve() if args.scratch else Path(tempfile.mkdtemp(prefix='zfc-breakthrough-blank-starts-'))
    if work==repo or repo in work.parents or work==Path('/'):p.error('Scratch must be outside repo and not filesystem root')
    work.mkdir(parents=True,exist_ok=True)
    input_files=perm.prepare(repo,work)
    assert perm.safe_classifier is not None
    prior={};audit_sources=[]
    for name in ('breakthrough-register-permutation.json','breakthrough-register-permutation-remaining28.json'):
        source=repo/'Computability/BusyBeaver/Research/ZFC/results'/name
        data=source.read_bytes();evidence=json.loads(data)
        assert evidence['status']=='complete' and evidence['baseline']['passed']
        audit_sources.append({'path':str(source.relative_to(repo)),'sha256':hashlib.sha256(data).hexdigest()})
        for record in evidence['candidates']:
            assert record['affine']['passed'] and record['affine']['cases_passed']==8391
            key=tuple(record['physical_permutation']);assert key not in prior
            prior[key]=record
    assert len(prior)==64
    families=[('identity',list(range(9)))]
    families+=list(perm.family('all36'))+list(perm.family('remaining28'))
    assert len(families)==65 and len({tuple(v) for _,v in families})==65
    classes=start_classes(perm.T)
    first=[g for g in classes if len(g['class'])==2]
    blank=[g for g in classes if g['class']==['blank_cycle']]
    assert len(first)==7 and len(blank)==1
    assert sum(len(g['members']) for g in first)==240
    assert len(blank[0]['members'])==12
    result={'scope':'Exact first-write class collapse plus bounded literal runs; no consistency, general simulation or eventual-initialization claim.',
            'command':[sys.executable,*sys.argv],'python':platform.python_version(),
            'input_files':input_files,'reused_affine_evidence':audit_sources,
            'first_write_classes':classes,'first_write_starts':240,'all_zero_cycle_starts':12,
            'normalized_step_limit':args.limit,'tables':65,'expected_literal_cases':455,
            'state_convention':{'working_states':252,'halt_label':254,'arbitrary_working_start_is_free':True},
            'frame_detector_scope':'Sufficient empty-PC/gap>=40 frame+Safe certificate, all physicalspares recorded. Spare capacity/value interface still needs separate proof for a positive.',
            'cases':[],'status':'running','scratch':str(work)}
    begun=time.monotonic()
    def save():
        result['elapsed_seconds']=time.monotonic()-begun
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    save()
    for name,mapping in families:
        targets={str(perm.SKIP[i]):str(perm.SKIP[mapping[i]]) for i in range(9)}
        table={key:(w,d,targets.get(t,t) if int(key[0]) not in perm.CORE else t)
               for key,(w,d,t) in perm.T.items()}
        assert all(table[q,0]==perm.T[q,0] for q,_ in table)
        data=perm.encoded(table);sha=hashlib.sha256(data).hexdigest()
        if name!='identity':assert prior[tuple(mapping)]['sha256']==sha
        path=work/(name+'.tm');path.write_bytes(data)
        for group in first:
            member=group['members'][0]
            start,offset=group['class']
            case={'name':name,'physical_permutation':mapping,'table_sha256':sha,
                  'table_path':str(path),'normalized_class':group['class'],
                  'representative_blank_start':member['start'],'blank_prefix_steps':member['prefix_steps'],
                  'head_translation':member['head_translation']}
            case['run']=literal(table,start,offset,mapping,args.limit)
            case['actual_blank_steps_for_representative']=member['prefix_steps']+case['run']['steps']
            if case['run']['outcome']=='sufficient_Safe_structural_frame':
                frame=case['run']['frame'];delta=member['head_translation']
                frame['representative_absolute_head']=frame['head']+delta
                frame['representative_absolute_ones']=[x+delta for x in frame['whole_one_positions']]
                winner=work/(name+'-start'+member['start']+'.tm')
                winner_data=data.replace(b'#! start 64\n',('#! start '+member['start']+'\n').encode(),1)
                winner.write_bytes(winner_data)
                case['selected_start_table']=str(winner)
                case['selected_start_table_sha256']=hashlib.sha256(winner_data).hexdigest()
                print('STRUCTURAL SAFE FRAME',json.dumps(case),flush=True)
            result['cases'].append(case);save()
        print(name,dict(Counter(c['run']['outcome'] for c in result['cases'][-7:])),
              'seconds',round(result['elapsed_seconds'],2),flush=True)
    result['status']='complete';save()
    print('Evidence',args.output,flush=True)

if __name__=='__main__':main()
