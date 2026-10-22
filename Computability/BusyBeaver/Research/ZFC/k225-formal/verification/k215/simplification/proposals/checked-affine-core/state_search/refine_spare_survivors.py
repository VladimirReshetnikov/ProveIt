#!/usr/bin/env python3
"""Reject concrete-screen survivors on every supplied source occurrence."""
from search_existential_spares import parse,run
from pathlib import Path
import argparse,json,time,hashlib

def main():
    ap=argparse.ArgumentParser();ap.add_argument('table');ap.add_argument('sites');ap.add_argument('results');ap.add_argument('--out',default='existential_spare_refined.json');ap.add_argument('--limit',type=int,default=20000);a=ap.parse_args()
    t=parse(a.table);sites=json.loads(Path(a.sites).read_text());initial=json.loads(Path(a.results).read_text());surv=[];rejections=[];runs=0;beg=time.time()
    for c in initial['survivors']:
        mutation=(tuple(c['incoming']),tuple(c['replacement']));bad=None;passed=0
        for i,site in enumerate(sites):
            for positive in ([False,True] if site[1]=='CD' else [False]):
                regs=[0]*9
                if positive:regs[site[2]]=1
                runs+=1;ok,steps,used,got=run(t,site,regs,[0],0,a.limit,mutation)
                if not ok:
                    parent,parent_steps,_,parentgot=run(t,site,regs,[0],0,a.limit)
                    assert parent
                    bad={'site_index':i,'site':site,'registers':regs,'spares':[0],'gap':0,'steps':steps,'actual':got,'parent_steps':parent_steps,'parent_output':parentgot};break
                passed+=1
            if bad:break
        if bad:rejections.append({**c,'passed_full_source_cases':passed,'witness':bad})
        else:surv.append({**c,'passed_full_source_cases':passed})
        print('candidate',c['removed'],c['replacement'],'PASS' if not bad else 'REJECT',passed,round(time.time()-beg,2),flush=True)
    result={'status':'BOUNDED_CONCRETE_REFINEMENT_ONLY','table_sha256':hashlib.sha256(Path(a.table).read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(Path(a.sites).read_bytes()).hexdigest(),'input_receipt_sha256':hashlib.sha256(Path(a.results).read_bytes()).hexdigest(),'transition_bound':a.limit,'survivors':surv,'rejections':rejections,'sample_runs':runs,'seconds':time.time()-beg}
    Path(a.out).write_text(json.dumps(result,indent=2)+'\n');print('DONE',len(surv),'survivors')
if __name__=='__main__':main()
