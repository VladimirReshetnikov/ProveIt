#!/usr/bin/env python3
"""Exact whole-action-graph comparison by canonical singleton refinement.

The candidate must have a discrete stable action-bisimulation partition, even
after erasing halt-entry write/move decorations. If another table does not, it
cannot be isomorphic to the candidate. If it does, its canonical color labels
give a unique whole-table serialization. Equality is compared as actual bytes,
not merely as hashes. This avoids fixing or guessing a start state.

Candidate forms include both directions of tape reflection and bit exchange.
Bit exchange is used only as a strengthened graph-novelty test, not a claim
about preserving the zero-blank initial condition.
"""
from pathlib import Path
import argparse, collections, hashlib, io, json, zipfile
from census import parse_text, TEXT_EXT, COMMIT

def canonical(table, mirror=False, complement=False, loose=True):
    rows,states,halt,*_=table
    ts={}
    for q in states:
        for b in (0,1):
            w,d,t=rows[q,b^int(complement)]
            if complement:w^=1
            if mirror:d='R' if d=='L' else 'L'
            if loose and t==halt:w,d=0,'R'
            ts[q,b]=(w,d,t)
    labels={q:0 for q in states};count=1;rounds=0
    while True:
        sig={q:(labels[q],tuple((ts[q,b][0],ts[q,b][1],-1 if ts[q,b][2]==halt else labels[ts[q,b][2]]) for b in (0,1))) for q in states}
        rank={s:i for i,s in enumerate(sorted(set(sig.values())))}
        new={q:rank[sig[q]] for q in states};rounds+=1
        stable=len(rank)==count;labels=new;count=len(rank)
        if stable:break
    if count!=len(states):return None,{'classes':count,'rounds':rounds}
    order=sorted(states,key=lambda q:labels[q]);out=[]
    for q in order:
        for b in (0,1):
            w,d,t=ts[q,b];out.append((w,d,-1 if t==halt else labels[t]))
    return json.dumps(out,separators=(',',':')).encode(),{'classes':count,'rounds':rounds}

def scan(repo):
    seen_zip=set();raws={};occurrences=collections.Counter();bad=[]
    def add(data,name):
        ext=Path(name).suffix.lower()
        if ext=='.zip':
            h=hashlib.sha256(data).digest()
            if h in seen_zip:return
            seen_zip.add(h)
            with zipfile.ZipFile(io.BytesIO(data)) as z:
                for info in z.infolist():
                    if info.is_dir():continue
                    if Path(info.filename).suffix.lower() in TEXT_EXT|{'.zip'}:
                        add(z.read(info),name+'!'+info.filename)
        else:
            h=hashlib.sha256(data).hexdigest()
            if h in raws:
                occurrences[h]+=1;return
            t=parse_text(data)
            if t:
                occurrences[h]+=1;raws[h]=(t,name,data)
            elif ext=='.tm':bad.append(name)
    for base in (repo/'Computability/BusyBeaver/Research/PA',repo/'docs/incoming'):
        if base.exists():
            for p in sorted(base.rglob('*')):
                if p.is_file() and p.suffix.lower() in TEXT_EXT|{'.zip'}:
                    add(p.read_bytes(),str(p.relative_to(repo)))
    return raws,occurrences,bad,len(seen_zip)

def main():
    ap=argparse.ArgumentParser();group=ap.add_mutually_exclusive_group(required=True);group.add_argument('--repo',type=Path);group.add_argument('--corpus',type=Path);ap.add_argument('--candidate',type=Path,action='append',required=True);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--representatives',type=Path)
    a=ap.parse_args();a.out.parent.mkdir(exist_ok=True,parents=True)
    candidates=[];controls=[]
    for p in a.candidate:
        t=parse_text(p.read_bytes());assert t and len(t[1])==194
        forms=[]
        for mirror in (False,True):
            for comp in (False,True):
                b,cert=canonical(t,mirror,comp)
                assert b is not None,(str(p),cert)
                forms.append((b,{'mirror':mirror,'bit_exchange':comp,'stable_partition':cert}))
        rr,ss,hh,st,decl=t
        rename={q:10000+37*i for i,q in enumerate(sorted(ss))};newhalt=999999
        renamed=({(rename[q],b):(w,d,newhalt if n==hh else rename[n]) for (q,b),(w,d,n) in rr.items()},set(rename.values()),newhalt,None if st is None else rename[st],decl)
        assert canonical(renamed)[0]==forms[0][0]
        redecorated=({key:((1-w,'L' if d=='R' else 'R',n) if n==hh else (w,d,n)) for key,(w,d,n) in rr.items()},ss,hh,st,decl)
        assert canonical(redecorated)[0]==forms[0][0]
        controls.append({'candidate':str(p),'arbitrary_state_rename':'pass','erased_halt_action_change':'pass'})
        candidates.append({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'forms':forms,'matches':[]})
    if a.repo:
        raws,occ,bad,zips=scan(a.repo)
    else:
        raws={};occ=collections.Counter();bad=[];zips=0
        for p in sorted(a.corpus.glob('*.tm')):
            data=p.read_bytes();t=parse_text(data)
            assert t is not None, str(p)
            h=hashlib.sha256(data).hexdigest();raws[h]=(t,str(p.name),data);occ[h]+=1
    n194=0;skipped=[];forms=set();class_list=[]
    if a.representatives:a.representatives.mkdir(exist_ok=True,parents=True)
    for h,(t,name,data) in raws.items():
        if len(t[1])!=194:continue
        n194+=1;b,cert=canonical(t)
        if b is None:
            skipped.append({'sha256':h,'path':name,'partition':cert})
            if a.representatives:(a.representatives/('nonminimal_'+h+'.tm')).write_bytes(data)
            continue
        forms.add(b)
        if a.representatives:(a.representatives/(hashlib.sha256(b).hexdigest()+'.tm')).write_bytes(data)
        class_list.append({'sha256':h,'path':name,'canonical_sha256':hashlib.sha256(b).hexdigest(),'partition':cert})
        for c in candidates:
            for cb,kind in c['forms']:
                if cb==b:c['matches'].append({'source_sha256':h,'source':name,**kind})
    results=[]
    for c in candidates:
        results.append({k:v for k,v in c.items() if k!='forms'}|{'novel':not c['matches'],'form_sha256s':[hashlib.sha256(x[0]).hexdigest() for x in c['forms']]})
    mutual=[]
    for i,c in enumerate(candidates):
        for d in candidates[i+1:]:
            same=bool({b for b,k in c['forms']} & {b for b,k in d['forms']})
            mutual.append({'first':c['path'],'second':d['path'],'isomorphic_under_any_allowed_symmetry':same})
    result={'commit':COMMIT,'comparison':'Whole action graph; arbitrary state renaming/start, reflection, bit exchange, and erased halt-entry actions. Actual canonical byte equality; singleton stable-partition proof; nonminimal corpus tables cannot match minimal candidate.',
        'recognized_byte_forms_all_sizes':len(raws),'recognized_occurrences_all_sizes':sum(occ.values()),'unique_zip_payloads':zips,
        '194_byte_forms':n194,'194_loose_action_classes_among_minimal_graphs':len(forms),'nonminimal_194_byte_forms':skipped,
        'tm_recognizer_failures':bad,'candidates':results,'mutual_comparison':mutual,'positive_controls':controls,'class_index':class_list}
    a.out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('class_index','nonminimal_194_byte_forms')},indent=2))

if __name__=='__main__':main()
