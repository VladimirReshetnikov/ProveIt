#!/usr/bin/env python3
"""Read-only numeric table census of filed PA packets and new incoming packets.

No assertion of semantic correctness is made by this recognizer. It inventories
complete deterministic 2-symbol numeric tables with one undefined halt label.
"""
import argparse,collections,hashlib,io,json,re,subprocess,zipfile
from pathlib import Path

SUFFIXES=('.tm','.txt','.tsv','.csv')

def digest(b): return hashlib.sha256(b).hexdigest()

def parse(b):
    try: s=b.decode('utf-8')
    except UnicodeError: return None
    rows={}
    for line in s.splitlines():
        line=line.strip()
        if not line or line.startswith(('#','//',';')): continue
        p=line.split()
        if len(p)!=5 or not p[0].isdigit() or p[1] not in ('0','1') or p[2] not in ('0','1') or p[3] not in ('L','R') or not p[4].isdigit(): return None
        q,r,w,d,t=p; key=int(q),int(r)
        if key in rows:return None
        rows[key]=int(w),d,int(t)
    states={q for q,r in rows}
    if not states or set(rows)!={(q,r) for q in states for r in (0,1)}:return None
    halts={t for w,d,t in rows.values()}-states
    if len(halts)!=1:return None
    return rows,states,next(iter(halts))

def canonical(table,root,mirror=False,complement=False):
    rows,states,halt=table
    labels={root:0};queue=[root];answer=[]
    for q in queue:
        rr=[]
        for bit in (0,1):
            w,d,t=rows[q,bit ^ int(complement)]
            if complement:w ^=1
            if mirror:d='L' if d=='R' else 'R'
            if t==halt:k=-1
            else:
                if t not in labels:labels[t]=len(queue);queue.append(t)
                k=labels[t]
            rr.append([w,d,k])
        answer.append(rr)
    if len(queue)!=len(states):return None
    return json.dumps(answer,separators=(',',':')).encode()

def rootfree(table,mirror=False,complement=False):
    vals=[v for q in sorted(table[1]) if (v:=canonical(table,q,mirror,complement)) is not None]
    return (digest(min(vals)),len(vals)) if vals else (None,0)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--new-packets',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);args=ap.parse_args()
    repo=args.repo.resolve();out=args.out.resolve();out.mkdir(parents=True,exist_ok=True);(out/'tables').mkdir(exist_ok=True)
    pa='Computability/BusyBeaver/Research/PA'
    commit=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD']).decode().strip()
    paths=subprocess.check_output(['git','-C',str(repo),'ls-tree','-r','--name-only','HEAD',pa]).decode().splitlines()
    raws={};occurrences=[];errors=[];archives=[];archive_refs=[];seen_archives=set();numeric_suffix_files=0;nonparsed_tm=[]
    def add(b,path):
        nonlocal numeric_suffix_files
        numeric_suffix_files+=1;t=parse(b)
        if t is None:
            if path.lower().endswith('.tm'): nonparsed_tm.append(path)
            return
        h=digest(b);n=len(t[1]);occurrences.append({'path':path,'sha256':h,'states':n,'halt':t[2]})
        if h not in raws:
            raws[h]={'table':t,'first_path':path,'bytes':b}
            (out/'tables'/f'{h}.tm').write_bytes(b)
    def scan_zip(b,path,depth=0):
        h=digest(b);archive_refs.append({'path':path,'sha256':h,'depth':depth})
        if h in seen_archives:return
        seen_archives.add(h)
        try:z=zipfile.ZipFile(io.BytesIO(b))
        except Exception as e:errors.append({'path':path,'error':repr(e)});return
        archives.append({'path':path,'sha256':h,'bytes':len(b),'members':len(z.infolist()),'depth':depth})
        for i in z.infolist():
            if i.is_dir():continue
            loc=path+'!'+i.filename
            if i.filename.lower().endswith('.zip'):scan_zip(z.read(i),loc,depth+1)
            elif i.filename.lower().endswith(SUFFIXES):add(z.read(i),loc)
    for p in paths:
        if not p.lower().endswith(SUFFIXES+('.zip',)): continue
        f=repo/p
        b=f.read_bytes() if f.exists() else subprocess.check_output(['git','-C',str(repo),'show','HEAD:'+p])
        if p.lower().endswith('.zip'):scan_zip(b,p)
        else:add(b,p)
    for f in sorted(args.new_packets.glob('*.zip')):
        # The five new archives are exactly named repository files.
        p='docs/incoming/'+f.name
        git_oid=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD:'+p]).decode().strip()
        b=f.read_bytes();actual=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        assert actual==git_oid,(p,git_oid,actual)
        scan_zip(b,p)
    print('Parsed files',numeric_suffix_files,'tables',len(occurrences),'unique bytes',len(raws),flush=True)
    groups=collections.defaultdict(list);raw_records=[]
    for i,(h,d) in enumerate(sorted(raws.items())):
        t=d['table'];gh,root_count=rootfree(t);groups[(len(t[1]),gh)].append(h)
        row={'sha256':h,'states':len(t[1]),'halt':t[2],'root_free_sha256':gh,'full_reaching_roots':root_count,'first_path':d['first_path']}
        if len(t[1])==194:
            row['cosmetic_class_sha256']=min(rootfree(t,m,c)[0] for m in (False,True) for c in (False,True))
        raw_records.append(row)
        if (i+1)%100==0:print('Canonicalized',i+1,'/',len(raws),flush=True)
    classes=[{'states':n,'root_free_sha256':g,'raw_sha256s':hs,'paths':[x['path'] for x in occurrences if x['sha256'] in hs]}for(n,g),hs in sorted(groups.items(),key=lambda x:(x[0][0],x[0][1] or ''))]
    summary={'commit':commit,'scope':'All tracked .tm/.txt/.tsv/.csv files under PA, including the 36 filed historical packets and imported upstream tables; all six filed nested ZIP references recursively, deduplicated by archive bytes; five new incoming pa194 packets recursively. Numeric complete binary tables with one undefined halt target only. This scope preserves every numerical machine-table identity from old archives because filed packets omit only identical upstream/sibling copies and logs/manifests. Occurrence counts refer to this file/ZIP traversal, not the old incoming-only census.',
        'filed_packet_directories':len([p for p in (repo/pa/'docs').iterdir() if p.is_dir()]),'new_incoming_archives':len(list(args.new_packets.glob('*.zip'))),'recognized_table_occurrences':len(occurrences),'unique_table_bytes':len(raws),'root_free_graph_classes':sum(g is not None for n,g in groups),'unrootable_unique_tables':sum(r['root_free_sha256'] is None for r in raw_records),'suffix_file_occurrences_read':numeric_suffix_files,'distinct_recursive_zip_bodies':len(archives),'zip_references':len(archive_refs),'states_histogram_occurrences':dict(sorted(collections.Counter(x['states'] for x in occurrences).items())),'states_histogram_raw_tables':dict(sorted(collections.Counter(x['states'] for x in raw_records).items())),'states_histogram_graphs':dict(sorted(collections.Counter(n for n,g in groups if g is not None).items())),'errors':errors}
    result={'summary':summary,'archives':archives,'archive_references':archive_refs,'occurrences':occurrences,'raw_tables':raw_records,'classes':classes,'tm_files_outside_recognizer':nonparsed_tm}
    (out/'census.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(summary,indent=2));print('194 classes:')
    for r in raw_records:
        if r['states']==194:print(r)

if __name__=='__main__':main()
