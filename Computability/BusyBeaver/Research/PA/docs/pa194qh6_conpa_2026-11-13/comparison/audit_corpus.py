#!/usr/bin/env python3
"""Reproducible numeric-table census; graph equivalence uses exact tuples.

Searches complete five-column binary tables in .tm/.txt/.tsv/.csv files.
Nested ZIP contents are traversed without extracting. Classifies full tables
when at least one control reaches every row-state; retains rootless fixtures
separately. A declared start is read from '# ... start N', else dense 0..n-1
uses start 0. Source code/JSON-only machines are outside the literal scope.
"""
import argparse, csv, hashlib, io, json, re, zipfile, subprocess
from collections import Counter, defaultdict
from pathlib import Path


def parse(data):
    rows={}; start=None
    try: txt=data.decode('ascii')
    except UnicodeDecodeError: raise ValueError('non-ASCII content')
    for l in txt.splitlines():
        l=l.strip()
        if not l: continue
        if l.startswith('#'):
            m=re.search(r'\bstart\s*(\d+)',l)
            if m and start is None: start=int(m[1])
            continue
        xs=l.split()
        if len(xs)!=5: raise ValueError('not five columns')
        q,b,w,d,n=xs
        try: q,b,w,n=map(int,(q,b,w,n))
        except ValueError: raise ValueError('nonnumeric control/symbol')
        if b not in (0,1) or w not in (0,1) or d not in ('L','R') or (q,b) in rows:
            raise ValueError('invalid/duplicate transition')
        rows[q,b]=(w,d,n)
    qs=set(q for q,b in rows)
    if not qs or any((q,b) not in rows for q in qs for b in (0,1)):
        raise ValueError('incomplete binary table')
    hs=set(n for w,d,n in rows.values())-qs
    if start is None and sorted(qs)==list(range(len(qs))): start=0
    if start is not None and start not in qs: raise ValueError('invalid start')
    return rows,qs,start,hs


def canonical(rows,qs,start,mirror=False,swap=False):
    ix={start:0}; todo=[start]; out=[]
    for q in todo:
        for b in (0,1):
            w,d,n=rows[q,b^swap]; w^=swap
            if mirror: d='L' if d=='R' else 'R'
            if n in qs:
                if n not in ix: ix[n]=len(ix);todo.append(n)
                t=ix[n]
            else: t=-1
            out.append((w,d,t))
    return tuple(out),len(todo)


def digest(t):return hashlib.sha256(json.dumps(t,separators=(',',':')).encode()).hexdigest()

def classify(rows,qs,start):
    roots=[]
    for q in sorted(qs):
        c,n=canonical(rows,qs,q)
        if n==len(qs): roots.append((q,c))
    if not roots:return None
    table=min(c for q,c in roots)
    sym=min(canonical(rows,qs,q,m,s)[0] for q,c in roots for m in (False,True) for s in (False,True))
    rooted=canonical(rows,qs,start)[0] if start is not None else None
    return {'table_class':digest(table),'symmetry_class':digest(sym),
        'machine_class':digest(rooted) if rooted else None,
        'spanning_roots':len(roots),'canonical':table,'symmetry_canonical':sym,
        'reachable':len(rooted)//2 if rooted else len(qs)}


def main():
    p=argparse.ArgumentParser();p.add_argument('--repo',type=Path,required=True)
    p.add_argument('--out',type=Path,required=True);p.add_argument('--verify-inputs-only',action='store_true');args=p.parse_args();args.out.mkdir(parents=True,exist_ok=True)
    pin='2e00058366845a6e2e0368004fd9ed2050a06a9a'
    head=subprocess.check_output(['git','-C',str(args.repo),'rev-parse','HEAD']).decode().strip()
    if head!=pin:raise ValueError('checkout must be pinned to '+pin)
    seenzip=set();raw={};occs=[];invalid=[];archives=[]
    def add(name,data):
        h=hashlib.sha256(data).hexdigest();suffix=Path(name).suffix.lower()
        if suffix=='.zip':
            if h in seenzip:return
            seenzip.add(h);archives.append({'path':name,'sha256':h,'bytes':len(data)})
            try:
                z=zipfile.ZipFile(io.BytesIO(data))
                for info in z.infolist():
                    if info.is_dir():continue
                    if Path(info.filename).suffix.lower() in ('.tm','.txt','.tsv','.csv','.zip'):
                        add(name+'!'+info.filename,z.read(info))
            except zipfile.BadZipFile as ex:invalid.append({'path':name,'reason':str(ex)})
            return
        if suffix not in ('.tm','.txt','.tsv','.csv'):return
        try: rows,qs,start,hs=parse(data)
        except ValueError as ex:
            if suffix=='.tm':invalid.append({'path':name,'reason':str(ex)})
            return
        occ={'path':name,'sha256':h,'states':len(qs),'start':start,'halt_labels':sorted(hs)}
        occs.append(occ)
        if h not in raw:raw[h]=(data,rows,qs,start,hs)
    # Enumerate tracked input blobs, so sparse checkouts and untracked files
    # cannot silently alter the pinned corpus. Verify every materialized blob.
    tree=subprocess.check_output(['git','-C',str(args.repo),'ls-tree','-rz','HEAD','--','Computability/BusyBeaver/Research/PA','docs/incoming'])
    tracked=0
    for item in tree.split(b'\0'):
        if not item:continue
        metadata,name=item.split(b'\t',1);name=name.decode()
        mode,kind,blob=metadata.decode().split()
        if kind!='blob' or Path(name).suffix.lower() not in ('.tm','.txt','.tsv','.csv','.zip'):continue
        f=args.repo/name
        data=f.read_bytes() if f.is_file() else subprocess.check_output(['git','-C',str(args.repo),'show','HEAD:'+name])
        actual=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        if actual!=blob:raise ValueError('materialized file differs from pinned blob: '+name)
        tracked+=1;add(name,data)
    if args.verify_inputs_only:
        print(json.dumps({'status':'PASS','snapshot':pin,'tracked_selected_files':tracked,'recognized_occurrences':len(occs),'recognized_byte_forms':len(raw),'unique_zip_payloads':len(archives),'all_materialized_blobs_match_git':True},indent=2))
        return
    classes={};symclasses={};unclassified=[];info={}
    for h,(data,rows,qs,start,hs) in raw.items():
        if len(hs)!=1:
            unclassified.append({'sha256':h,'states':len(qs),'reason':'not exactly one undefined halt','halts':sorted(hs)})
            continue
        c=classify(rows,qs,start)
        if c is None:
            unclassified.append({'sha256':h,'states':len(qs),'reason':'no spanning root'})
            continue
        info[h]={k:v for k,v in c.items() if k not in ('canonical','symmetry_canonical')}
        k=c['canonical'];sk=c['symmetry_canonical']
        classes.setdefault(k,[]).append(h);symclasses.setdefault(sk,[]).append(h)
    for o in occs:o.update(info.get(o['sha256'],{}))
    byhash=defaultdict(list)
    for o in occs:byhash[o['sha256']].append(o['path'])
    classlist=[]
    for k,hs in classes.items():
        hs=sorted(hs);paths=sorted(p for h in hs for p in byhash[h]);h=hs[0]
        classlist.append({'table_class':digest(k),'states':len(k)//2,'byte_forms':len(hs),'occurrences':len(paths),
            'symmetry_class':info[h]['symmetry_class'],'representative_sha256':h,'representative_path':paths[0],
            'sha256s':hs,'paths':paths})
    classlist.sort(key=lambda c:(c['states'],c['table_class']))
    summary={'snapshot':'2e00058366845a6e2e0368004fd9ed2050a06a9a','literal_occurrences':len(occs),
        'byte_forms':len(raw),'complete_one_halt_spanning_table_classes':len(classes),
        'classes_modulo_reflection_and_bit_exchange':len(symclasses),
        'classes_by_states':dict(sorted(Counter(len(k)//2 for k in classes).items())),
        '194_classes':sum(len(k)//2==194 for k in classes),'archives':len(archives),
        'unclassified_byte_forms':len(unclassified),'invalid_tm_files':len(invalid),
        'scope':'All files with numeric complete five-column binary tables in .tm/.txt/.tsv/.csv and nested ZIPs under PA and docs/incoming; source/JSON-only tables excluded. Includes rejected designs and diagnostic controls.'}
    (args.out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    (args.out/'census.json').write_text(json.dumps({'summary':summary,'classes':classlist,'occurrences':occs,'archives':archives,'unclassified':unclassified,'invalid_tm_files':invalid},indent=2)+'\n')
    (args.out/'class_canonical.json').write_text(json.dumps({digest(k):k for k in classes},separators=(',',':'))+'\n')
    with (args.out/'classes.csv').open('w') as f:
        fields=['table_class','states','byte_forms','occurrences','symmetry_class','representative_sha256','representative_path']
        w=csv.DictWriter(f,fieldnames=fields);w.writeheader();w.writerows({k:c[k] for k in fields} for c in classlist)
    with (args.out/'occurrences.csv').open('w') as f:
        fields=['path','sha256','states','start','halt_labels','table_class','symmetry_class','machine_class','spanning_roots','reachable']
        w=csv.DictWriter(f,fieldnames=fields);w.writeheader();w.writerows(occs)
    print(json.dumps(summary,indent=2))
if __name__=='__main__':main()
