#!/usr/bin/env python3
"""Reconcile every recognized literal table in the pinned PA/incoming trees.

The parser and graph routines in audit_helpers.py / novelty_helpers.py are
attributed copies from the incoming symmetric-witness package.  This new
driver adds exact Git blob verification of local source payloads, scans
nested archives, and uses git show when the working file differs from the pin.
No generator or manuscript is executed to infer unprovided machines.
"""
from pathlib import Path
import csv,hashlib,io,json,zipfile,subprocess,re,sys,argparse
from collections import Counter
import audit_helpers as ah
import novelty_helpers as nh

HERE=Path(__file__).resolve().parent
PIN='7c0bb454cf73c29ca1c385f9fec856ddd236a7cb'
sha=lambda b:hashlib.sha256(b).hexdigest()
gitsha=lambda b:hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--repo',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();REPO=args.repo;OUT=args.output
    OUT.mkdir(parents=True,exist_ok=True)
    (OUT/'tables194').mkdir(exist_ok=True)
    entries=[]
    for v in subprocess.check_output(['git','-C',str(REPO),'ls-tree','-r','-z',PIN]).split(b'\0'):
        if not v:continue
        meta,p=v.decode().split('\t',1)
        mode,typ,h=meta.split()
        if typ=='blob' and p.startswith(('Computability/BusyBeaver/Research/PA/','docs/incoming/')) and p.endswith(('.tm','.json','.txt','.zip')):
            entries.append((p,h))
    occurrences=[];tables={};zips={};seenjson={};errors=[];verified=[];stats=Counter()
    def add(loc,item,source_hash):
        rows,states,start,declared=item;b=ah.table_bytes(rows);h=sha(b)
        tables.setdefault(h,{'rows':rows,'states':states,'data':b})
        occurrences.append(dict(locator=loc,normalized_sha256=h,source_sha256=source_hash,
                                states=len(states),start=start,declared_start=declared))
    def inspect(data,loc):
        stats['payloads']+=1;h=sha(data)
        if loc.endswith('.zip'):
            stats['archive_references']+=1
            if h in zips:stats['duplicate_archive_references']+=1;return
            zips[h]=loc
            try:
                with zipfile.ZipFile(io.BytesIO(data)) as z:
                    for n in z.namelist():
                        if n.endswith(('.tm','.json','.txt','.zip')):inspect(z.read(n),loc+'!'+n)
            except Exception as e:errors.append(dict(locator=loc,error=repr(e)))
        elif loc.endswith(('.tm','.txt')):
            try:add(loc,ah.parse(data),h)
            except Exception as e:
                if loc.endswith('.tm'):errors.append(dict(locator=loc,error=repr(e)))
        elif loc.endswith('.json'):
            if h not in seenjson:
                if b'"L"' not in data and b'"R"' not in data and not re.search(rb'\b[LR]\b',data):
                    seenjson[h]=[];return
                try:seenjson[h]=list(ah.json_tables(json.loads(data)))
                except Exception as e:errors.append(dict(locator=loc,error=repr(e)));return
            for sub,item in seenjson[h]:add(loc+'#'+sub,item,h)
    for i,(path,h) in enumerate(entries):
        candidates=[REPO/path]
        data=None;source=None
        for p in candidates:
            if not p.is_file():continue
            b=p.read_bytes()
            if gitsha(b)==h:data=b;source='local exact blob';break
        if data is None:
            data=subprocess.check_output(['git','-C',str(REPO),'show',PIN+':'+path])
            if gitsha(data)!=h:raise ValueError('Git data mismatch: '+path)
            source='pinned git show'
        verified.append(dict(path=path,git_blob=h,sha256=sha(data),size_bytes=len(data),access=source))
        inspect(data,path)
        if i%1500==0:print('read',i,'/',len(entries),'tables',len(tables),flush=True)
    print('classifying',len(tables),'normalized tables',flush=True)
    classes={};nonspanning=[]
    for i,(h,t) in enumerate(tables.items()):
        rows,states=t['rows'],t['states'];c=nh.canonical(rows,states)
        if c is None:
            nonspanning.append(h);t['class']=None
            if len(states)==194:(OUT/'tables194'/('nonspanning_'+h+'.tm')).write_bytes(t['data'])
            continue
        ch=sha(ah.encode(c));t['class']=ch
        if ch not in classes:
            strong=nh.strong(rows,states) if len(states)==194 else None
            classes[ch]=dict(states=len(states),normalized_table=h,
                strong_class=sha(ah.encode(strong)) if strong else None,
                ordinary_bisimulation_states=nh.bisimulation_count(rows,states) if len(states)==194 else None)
            if len(states)==194:(OUT/'tables194'/(ch+'.tm')).write_bytes(t['data'])
        if i%150==0:print('classified',i,'/',len(tables),flush=True)
    for o in occurrences:o['class']=tables[o['normalized_sha256']]['class']
    with (OUT/'occurrences.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(occurrences[0]));w.writeheader();w.writerows(occurrences)
    (OUT/'classes.json').write_text(json.dumps(classes,indent=2)+'\n')
    (OUT/'verified_sources.json').write_text(json.dumps(verified,indent=2)+'\n')
    summary=dict(pin=PIN,tracked_selected_files=len(entries),verified_source_payloads=len(verified),
        occurrences=len(occurrences),normalized_tables=len(tables),spanning_classes=len(classes),
        nonspanning_tables=nonspanning,
        classes_by_state_count=dict(sorted(Counter(r['states'] for r in classes.values()).items())),
        unique_archive_payloads=len(zips),archive_sources=zips,errors=errors,**stats,
        scope='Every tracked .tm/.json/.txt/.zip under PA and incoming; recognized numeric five-column tables and four explicit JSON encodings, recursively inside ZIPs, deduplicated byte-identical archive payloads. No generators/prose interpreted. Graph classes are not correctness claims.')
    (OUT/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps({k:v for k,v in summary.items() if k not in ('archive_sources','errors','nonspanning_tables')},indent=2))
    print('errors',len(errors),'nonspanning',len(nonspanning))

if __name__=='__main__':main()
