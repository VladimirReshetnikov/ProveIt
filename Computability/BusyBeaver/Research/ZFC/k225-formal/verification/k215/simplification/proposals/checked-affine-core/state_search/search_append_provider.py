#!/usr/bin/env python3
"""Targeted spare-aware reuse of an existing provider for deleted state189.

First find right-moving redirects of66/0 preserving all sampled non-CI
operations. For each surviving provider p, synthesize its read-zero row,
then check all sampled instructions under the relaxed spare postcondition.
This is a bounded concrete screen and makes no universality claim.
"""
from search_existential_spares import parse,run
from pathlib import Path
import argparse,json,time,hashlib

def main():
    ap=argparse.ArgumentParser();ap.add_argument('table');ap.add_argument('sites');ap.add_argument('--out',default='append_provider_results.json');ap.add_argument('--limit',type=int,default=5000);a=ap.parse_args();t=parse(a.table);sites=json.loads(Path(a.sites).read_text());short={};beg=time.time()
    for site in sites:
        key=tuple(site[1:])
        if key not in short or len(site[0])<len(short[key][0]):short[key]=site
    tests=[]
    for site in short.values():
        for regs,spares,gap in [([0]*9,[0],0),([1]*9,[0,2,1],3),([i%3 for i in range(9)],[2],0)]:
            tests.append((site,regs,spares,gap))
    noninc=[x for x in tests if x[0][1]!='CI'];inc=[x for x in tests if x[0][1]=='CI'];providers=[];attempts=0;surv=[]
    for p in range(215):
        if p in (66,189):continue
        for w in (0,1):
          for d in (-1,1):
            mutation={(66,0):(w,d,p)};ok=True
            for site,regs,spares,gap in noninc:
                if not run(t,site,regs,spares,gap,a.limit,mutation)[0]:ok=False;break
            if ok:providers.append([w,d,p])
    print('providers',providers,flush=True)
    for incoming in providers:
        p=incoming[2]
        for z in range(215):
            if z==189:continue
            for w in (0,1):
              for d in (-1,1):
                attempts+=1;mutation={(66,0):tuple(incoming),(p,0):(w,d,z)};ok=True
                for site,regs,spares,gap in inc+noninc:
                    if not run(t,site,regs,spares,gap,a.limit,mutation)[0]:ok=False;break
                if ok:surv.append({'incoming_replacement':incoming,'provider':p,'zero_row':[w,d,z]})
        print('provider',incoming,'attempts',attempts,'survivors',len(surv),round(time.time()-beg,2),flush=True)
    result={'status':'BOUNDED_CONCRETE_SCREEN_ONLY','table_sha256':hashlib.sha256(Path(a.table).read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(Path(a.sites).read_bytes()).hexdigest(),'transition_bound':a.limit,'nonincrement_samples':len(noninc),'increment_samples':len(inc),'initial_redirects':852,'providers':providers,'provider_row_candidates':attempts,'survivors':surv,'seconds':time.time()-beg,'scope':'Redirect66/0 to p !=66,189; provider must first preserve non-CI samples with existing rows; then vary only p/0. Arbitrary valid spare suffix accepted at first clean redispatch; later-return contracts are not tested.'}
    Path(a.out).write_text(json.dumps(result,indent=2)+'\n');print('DONE',len(surv))
if __name__=='__main__':main()
