#!/usr/bin/env python3
"""Continue the 138 folds whose original first failure gains a loop proof.

Each new failing affected source case must either pass the inherited exact
source-block checker or obtain a fresh narrow universal countdown certificate,
complete source matrix endpoint equality, and coverage of its full original
entry domain. A selected positive prefix without coverage is rejected. Cases
whose unchanged baseline trace never visits the deleted state retain that
same trace because all box-support rows remain identical. No untested whole
machine, bootstrap, or formal-kernel claim is made.
"""
from __future__ import annotations
import argparse, hashlib, json, sys, time
from collections import Counter,defaultdict
from pathlib import Path
import check_countdowns as cc

t=cc.t;c=cc.c;ROOT=cc.ROOT;source=t.source;effects=t.effects
sys.path.insert(0,str(ROOT/'loop_experiments'))
import affine_reference_loops as loops

def direct(table,index,frontiers,constraints,fuel):
    effects.bounds=source.bounds;c.strict.oracle=effects.oracle
    return source.check_one(table,index,frontiers,constraints,fuel)

def match(result,reference,bounds):
    if result['status']!='binary_countdown_and_clean_exit_verified':return False
    frame=result['zero_exit']['record'];matrix=cc.reduced_matrix(result['composed_primary_rows'],bounds)
    targets=reference['targets']
    matches=[x for x in targets if x['pc']==frame['pc'] and x['gap_constant']==frame['gap_constant']
             and cc.reduced_matrix(x['register_affine_rows'],bounds)==matrix]
    result['matching_full_matrix_source_targets']=matches
    return result['prefix_covers_original_case'] and bool(matches)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--input',type=Path,default=ROOT/'binary_loop_experiments/certificates/results.json')
    p.add_argument('--references',type=Path,default=ROOT/'binary_loop_experiments/certificates/matrix_reference_targets.json')
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--fuel',type=int,default=1000)
    a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True);start=time.monotonic()
    raw=json.loads(a.input.read_text());initial=raw['first_contract_survivors']
    reference={int(k):v for k,v in json.loads(a.references.read_text())['cases'].items()}
    frontiers,constraints,enabled,_=source.configure(64)
    admitted=[i for i,x in enumerate(enabled) if x];usage=defaultdict(list)
    for index in admitted:
        table=source.Tracking(c.T);ok,cost,_,reason=direct(table,index,frontiers,constraints,a.fuel)
        assert ok,(index,reason)
        for q in {q for q,b in table.used}:usage[q].append((cost,index))
    for q in usage:usage[q].sort()
    jobs=[]
    for x in initial:
        assert x['prefix_covers_original_case'] and x['matching_full_matrix_source_targets']
        dead=str(x['deleted']);replacement=str(x['replacement']);table=c.fold(c.T,dead,replacement)
        assert all(table[k]==c.T[k] for k in source.PROTECTED)
        jobs.append({'deleted':x['deleted'],'replacement':x['replacement'],'table':table,
                     'passed':{x['case']},'initial_case':x['case'],'accelerated':[x['case']],
                     'affected':[i for _,i in usage[dead]],'direct_checks':0,'rounds':0})
    finished=[];round_number=0;fresh_certificates=[];all_case_survivors=[]
    while jobs:
        round_number+=1;pending=[];needed=set()
        for job in jobs:
            job['rounds']+=1
            for index in job['affected']:
                if index in job['passed']:continue
                ok,cost,steps,reason=direct(job['table'],index,frontiers,constraints,a.fuel)
                job['direct_checks']+=1
                if ok:job['passed'].add(index);continue
                trace=t.Analyzer(job['table'],index,constraints[index],frontiers[index],policy='positive').run(a.fuel)
                if trace['status']!='countdown_shape':
                    job['failure']={'case':index,'original_reason':reason,'diagnostic':trace}
                    job['status']='rejected_without_countdown';finished.append(job);break
                candidate={'deleted':job['deleted'],'replacement':job['replacement'],'case':index,
                           'path':c.CASES[index][0],**trace}
                certificate=cc.check_one(candidate,constraints[index],a.fuel)
                fresh_certificates.append({'trace':candidate,'certificate':certificate})
                if certificate['status']!='binary_countdown_and_clean_exit_verified' or not certificate['prefix_covers_original_case']:
                    job['failure']={'case':index,'original_reason':reason,'certificate':certificate}
                    job['status']='rejected_countdown_certificate';finished.append(job);break
                pending.append((job,index,reason,certificate))
                if index not in reference:needed.add(index)
                break
            else:
                job['status']='all_affected_cases_passed'
                # Unaffected traces are unchanged, but record a full direct/loop
                # case inventory explicitly before a machine could be proposed.
                assert len(job['passed'])==len(set(job['affected']))
                job['unaffected_baseline_cases']=len(admitted)-len(job['affected'])
                all_case_survivors.append(job);finished.append(job)
        if needed:
            addition=loops.raw_targets(sorted(needed))
            reference.update({int(k):v for k,v in addition['cases'].items()})
        jobs=[]
        for job,index,reason,certificate in pending:
            if match(certificate,reference[index],constraints[index]):
                job['passed'].add(index);job['accelerated'].append(index);jobs.append(job)
            else:
                job['status']='rejected_source_endpoint'
                job['failure']={'case':index,'original_reason':reason,'certificate':certificate}
                finished.append(job)
        print('ROUND',round_number,'remaining',len(jobs),'finished',len(finished),'seconds',round(time.monotonic()-start,2),flush=True)
    def portable(job):
        return {k:sorted(v) if isinstance(v,set) else v for k,v in job.items() if k!='table'}
    results=[portable(x) for x in finished]
    summary={'scope':__doc__,'input_sha256':hashlib.sha256(a.input.read_bytes()).hexdigest(),
             'baseline_cases':len(admitted),'initial_recipes':len(initial),'completed':len(results),
             'counts':dict(Counter(x['status'] for x in results)),
             'direct_checks':sum(x['direct_checks'] for x in results),
             'new_countdown_candidates':len(fresh_certificates),
             'new_accelerated_cases':sum(len(x['accelerated'])-1 for x in results),
             'all_affected_case_survivors':[portable(x) for x in all_case_survivors],
             'results':results,'fresh_certificates':fresh_certificates,
             'fuel':a.fuel,'rounds':round_number,'seconds':time.monotonic()-start}
    (a.output/'results.json').write_text(json.dumps(summary,separators=(',',':'))+'\n')
    (a.output/'matrix_reference_targets.json').write_text(json.dumps({'cases':reference},separators=(',',':'))+'\n')
    print(json.dumps({k:v for k,v in summary.items() if k not in ('scope','results','fresh_certificates','all_affected_case_survivors')}),flush=True)

if __name__=='__main__':main()
