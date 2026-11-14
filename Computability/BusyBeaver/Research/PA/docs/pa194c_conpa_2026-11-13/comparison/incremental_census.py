#!/usr/bin/env python3
"""Extend the frozen 32-archive census by an exact, audited Git commit delta.

The baseline inventory is inherited, not recomputed. This program freshly parses
all complete numeric binary .tm/.txt members in the two additional archives.
Canonical serialization matches the baseline census.py (read 0 then 1, BFS,
lexicographic minimum over every control reaching the complete graph).
"""
import argparse, collections, hashlib, io, json, zipfile
from pathlib import Path

sha=lambda b:hashlib.sha256(b).hexdigest()

def parse(b):
    try:s=b.decode('utf8')
    except UnicodeDecodeError:return
    rows={}
    for l in s.splitlines():
        l=l.strip()
        if not l or l.startswith(('#','//',';')):continue
        p=l.split()
        if len(p)!=5 or p[1] not in ('0','1') or p[2] not in ('0','1') or p[3] not in ('L','R') or not p[0].isdigit() or not p[4].isdigit():return
        q,r,w,d,t=p;key=int(q),int(r)
        if key in rows:return
        rows[key]=int(w),d,int(t)
    states={q for q,r in rows}
    if not states or set(rows)!={(q,r)for q in states for r in (0,1)}:return
    halts={t for w,d,t in rows.values()}-states
    if len(halts)!=1:return
    return rows,states,next(iter(halts))

def canonical(data,root,reflect=False):
    rows,states,halt=data;labels={root:0};todo=[root];ans=[]
    for q in todo:
        rr=[]
        for bit in (0,1):
            w,d,t=rows[q,bit]
            if reflect:d='L'if d=='R'else'R'
            if t==halt:k=-1
            else:
                if t not in labels:labels[t]=len(todo);todo.append(t)
                k=labels[t]
            rr.append([w,d,k])
        ans.append(rr)
    if len(todo)!=len(states):return
    return json.dumps(ans,separators=(',',':')).encode()

def classify(data,reflect=False):
    enc=[c for q in sorted(data[1])if(c:=canonical(data,q,reflect))is not None]
    return (sha(min(enc))if enc else None),len(enc)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--base-census',type=Path,required=True)
    ap.add_argument('--commit-comparison',type=Path,required=True)
    ap.add_argument('--listing',type=Path,required=True)
    ap.add_argument('--new-archive',type=Path,action='append',required=True)
    ap.add_argument('--candidate',type=Path)
    ap.add_argument('--output',type=Path,required=True)
    a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=True)
    base=json.loads(a.base_census.read_text());delta=json.loads(a.commit_comparison.read_text());listing=json.loads(a.listing.read_text())
    assert base['summary']['commit']==delta['base']
    assert delta['status']=='ahead'
    assert not[f for f in delta['files']if f['filename'].startswith('Computability/BusyBeaver/Research/PA/')and f['filename'].endswith(('.tm','.txt'))]
    changes=[f for f in delta['files']if f['filename'].startswith('docs/incoming/')and f['filename'].endswith('.zip')]
    assert all(f['status']=='added'for f in changes)
    added_names={Path(f['filename']).name for f in changes};assert added_names=={p.name for p in a.new_archive}
    old_names={Path(x['path']).name for x in base['archive_references']if x['depth']==0}
    metadata={x['name']:x for x in listing if x['name'].endswith('.zip')}
    assert set(metadata)==old_names|added_names
    archives=list(base['archives']);refs=list(base['archive_references']);tables=list(base['tables'])
    raw={x['sha256']:dict(x)for x in base['raw_tables']};seen={x['sha256']for x in archives}
    members=base['summary']['distinct_archive_body_member_occurrences'];new_tables=[];new_raw=[];new_archives=[];errors=[]
    def add_table(b,path):
        z=parse(b)
        if z is None:return
        rows,states,halt=z;h=sha(b);rec={'path':path,'sha256':h,'states':len(states),'halt':halt};tables.append(rec);new_tables.append(rec)
        if h not in raw:
            g,n=classify(z)
            r={'sha256':h,'states':len(states),'halt':halt,'root_free_sha256':g,'full_reaching_roots':n,'first_path':path}
            raw[h]=r;new_raw.append(r)
            if len(states)<=195:(a.output/'new_frontier_tables').mkdir(exist_ok=True);(a.output/'new_frontier_tables'/(h+'.tm')).write_bytes(b)
    def scan(b,path,depth):
        nonlocal members
        h=sha(b);refs.append({'path':path,'sha256':h,'depth':depth})
        if h in seen:return
        seen.add(h)
        with zipfile.ZipFile(io.BytesIO(b))as z:
            rec={'path':path,'sha256':h,'bytes':len(b),'depth':depth,'file_count':sum(not i.is_dir()for i in z.infolist())}
            archives.append(rec);new_archives.append(rec)
            for i in z.infolist():
                if i.is_dir():continue
                members+=1;p=path+'!'+i.filename
                if i.filename.lower().endswith('.zip'):scan(z.read(i),p,depth+1)
                elif i.filename.lower().endswith(('.tm','.txt')):add_table(z.read(i),p)
    for p in sorted(a.new_archive):
        b=p.read_bytes();m=metadata[p.name];assert len(b)==m['bytes']
        gh=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert gh==m['git_blob_sha1']
        scan(b,'docs/incoming/'+p.name,0)
    classes={(x['states'],x['root_free_sha256'])for x in raw.values()if x['root_free_sha256']is not None}
    hist=lambda values:dict(sorted(collections.Counter(values).items()))
    summary={'commit':delta['head'],'baseline_commit':delta['base'],'method':'Incremental extension of inherited frozen census; baseline bytes and direct tables unchanged by exact Git comparison; fresh parse/canonicalization of added archives only.','baseline_census_sha256':sha(a.base_census.read_bytes()),'top_level_archives':len(metadata),'distinct_archive_bodies':len(archives),'archive_references':len(refs),'max_nested_depth':max(x['depth']for x in refs),'distinct_archive_body_member_occurrences':members,'complete_table_occurrences':len(tables),'distinct_raw_table_bytes':len(raw),'root_free_graph_classes':len(classes),'unrootable_raw_tables':sum(x['root_free_sha256']is None for x in raw.values()),'states_histogram_table_occurrences':hist(x['states']for x in tables),'states_histogram_raw_tables':hist(x['states']for x in raw.values()),'states_histogram_root_free_classes':hist(n for n,g in classes),'fresh_delta':{'top_level_archives':len(a.new_archive),'distinct_archive_bodies':len(new_archives),'table_occurrences':len(new_tables),'new_raw_tables':len(new_raw),'new_graph_classes':len(classes)-base['summary']['root_free_graph_classes']},'errors':errors}
    frontier=[]
    for n,g in sorted(classes):
        if n not in (194,195):continue
        hs={h for h,r in raw.items()if r['states']==n and r['root_free_sha256']==g}
        frontier.append({'states':n,'graph_hash':g,'raw_hashes':sorted(hs),'occurrences':[x['path']for x in tables if x['sha256']in hs]})
    output={'summary':summary,'inherited_summary':base['summary'],'new_archives':new_archives,'new_tables':new_tables,'new_raw_tables':new_raw,'frontier_classes':frontier}
    if a.candidate:
        b=a.candidate.read_bytes();z=parse(b);assert z is not None
        g,roots=classify(z);rg,_=classify(z,True);n=len(z[1])
        matching=[x for x in raw.values()if x['states']==n and x['root_free_sha256']in(g,rg)]
        output['candidate_novelty']={'candidate_name':a.candidate.name,'candidate_sha256':sha(b),'states':n,'root_free_sha256':g,'reflected_root_free_sha256':rg,'full_reaching_roots':roots,'matching_corpus_tables':matching,'different_from_every_class_under_renaming_and_reflection':not matching,'action_counts':dict(sorted(collections.Counter(str(w)+d for w,d,t in z[0].values()).items()))}
    (a.output/'incremental_census.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({'summary':summary,'candidate_novelty':output.get('candidate_novelty')},indent=2))

if __name__=='__main__':main()
