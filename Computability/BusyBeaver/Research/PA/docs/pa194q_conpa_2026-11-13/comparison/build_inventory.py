#!/usr/bin/env python3
"""Read-only inventory of literal numeric binary TM tables in a git snapshot.

Recognizes complete five-column state/read/write/LR/target .tm and .txt files,
with exactly one undefined terminal state. It does not infer correctness from
file names. The action graph certificate is canonical BFS from every root
which reaches every working state, with the lexicographic minimum retained.
"""
import argparse,collections,hashlib,io,json,os,pathlib,re,subprocess,zipfile

def sha(b): return hashlib.sha256(b).hexdigest()
def parse(b):
    try: lines=b.decode('utf-8-sig').splitlines()
    except UnicodeDecodeError: return None
    t={}
    for line in lines:
        s=line.strip()
        if not s or s.startswith('#'):continue
        x=s.split()
        if len(x)!=5 or x[1] not in ('0','1') or x[2] not in ('0','1') or x[3] not in ('L','R'):return None
        try:q,a,w,d,n=int(x[0]),int(x[1]),int(x[2]),x[3],int(x[4])
        except ValueError:return None
        if (q,a) in t:return None
        t[q,a]=(w,d,n)
    if not t:return None
    states={q for q,a in t}
    if len(t)!=2*len(states) or any((q,a) not in t for q in states for a in (0,1)):return None
    terminal={v[2] for v in t.values()}-states
    if len(terminal)!=1:return None
    return t,states,next(iter(terminal))

def canon(parsed,reflect=False,complement=False):
    t,states,halt=parsed
    best=None;roots=0
    for root in sorted(states):
        order=[root];index={root:0};data=[]
        for q in order:
            for a in (0,1):
                w,d,n=t[q,a^complement]
                if n==halt:k=-1
                else:
                    if n not in index:index[n]=len(order);order.append(n)
                    k=index[n]
                data.extend((w^complement, (d=='R')^reflect,k))
        if len(order)!=len(states):continue
        roots+=1
        z=tuple(map(int,data))
        if best is None or z<best:best=z
    if best is None:return None,roots
    return sha(json.dumps(best,separators=(',',':')).encode()),roots

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--repo',required=True);ap.add_argument('--output',required=True);ap.add_argument('--ref',default='HEAD');args=ap.parse_args()
    out=pathlib.Path(args.output);out.mkdir(parents=True,exist_ok=True);(out/'tables').mkdir(exist_ok=True)
    env=os.environ.copy();env['GIT_NO_LAZY_FETCH']='1'
    def git(*xs):return subprocess.check_output(['git','-C',args.repo,*xs],env=env)
    commit=git('rev-parse',args.ref).decode().strip()
    rows=git('ls-tree','-r','-z',args.ref,'Computability/BusyBeaver/Research/PA','docs/incoming').split(b'\0')
    objects=collections.defaultdict(list)
    for row in rows:
        if not row:continue
        pre,nb=row.split(b'\t',1);mode,typ,gh=pre.decode().split();name=nb.decode()
        if name.endswith(('.tm','.txt','.zip')):objects[gh].append(name)
    raw={};occurrences=[];archives=[];seen_zips=set();errors=[]
    def table(b,path):
        p=parse(b)
        if p is None:return
        h=sha(b)
        rec={'path':path,'sha256':h,'states':len(p[1]),'halt':p[2]};occurrences.append(rec)
        if h not in raw:
            g,k=canon(p)
            r=rec.copy();r.pop('path');r['first_path']=path;r['action_graph_sha256']=g;r['full_reaching_roots']=k;r['bytes']=len(b)
            if len(p[1])==194:
                r['reflected_action_graph_sha256']=canon(p,True)[0]
                r['complemented_action_graph_sha256']=canon(p,False,True)[0]
                r['reflected_complemented_action_graph_sha256']=canon(p,True,True)[0]
            raw[h]=r
            (out/'tables'/f'{h}.tm').write_bytes(b)
    def archive(b,path,depth):
        h=sha(b);dup=h in seen_zips
        archives.append({'path':path,'sha256':h,'bytes':len(b),'depth':depth,'duplicate_payload':dup})
        if dup:return
        seen_zips.add(h)
        try:z=zipfile.ZipFile(io.BytesIO(b))
        except Exception as e:errors.append({'path':path,'error':str(e)});return
        for item in z.infolist():
            if item.is_dir():continue
            f=item.filename;target=path+'!'+f
            if f.lower().endswith('.zip'):archive(z.read(item),target,depth+1)
            elif f.lower().endswith(('.tm','.txt')):table(z.read(item),target)
    for i,(gh,names) in enumerate(objects.items()):
        try:b=git('cat-file','blob',gh)
        except subprocess.CalledProcessError:errors.append({'git_blob':gh,'paths':names,'error':'not locally available'});continue
        for name in names:
            if name.endswith('.zip'):archive(b,name,0)
            else:table(b,name)
        if i%200==0:print('objects',i,'tables',len(occurrences),'raw',len(raw),flush=True)
    classes=collections.defaultdict(list)
    for r in raw.values():classes[(r['states'],r['action_graph_sha256'])].append(r['sha256'])
    counts=collections.Counter(r['states'] for r in raw.values())
    summary={'commit':commit,'scope':'Current git tree PA .tm/.txt files plus all current incoming ZIPs and recursively encountered archive payloads; archive bodies traversed once by SHA256. Includes reference copies, rejected experiments, synthetic controls and ancestor machines. Counts are not supported Con(PA) theorem counts.','table_occurrences':len(occurrences),'raw_tables':len(raw),'action_graph_classes':sum(g is not None for n,g in classes),'unclassified_disconnected_raw_tables':sum(r['action_graph_sha256'] is None for r in raw.values()),'distinct_archive_payloads':len(seen_zips),'archive_references':len(archives),'raw_counts_by_state':dict(sorted(counts.items())),'errors':errors}
    result={'summary':summary,'archives':archives,'tables':occurrences,'raw_tables':list(raw.values()),'classes':[{'states':n,'action_graph_sha256':g,'raw_hashes':hs} for (n,g),hs in classes.items()]}
    (out/'inventory.json').write_text(json.dumps(result,indent=2)+'\n')
    (out/'frontier194.json').write_text(json.dumps({'summary':summary,'tables':[r for r in occurrences if r['states']==194],'raw_tables':[r for r in raw.values() if r['states']==194]},indent=2)+'\n')
    print(json.dumps(summary,indent=2),flush=True)

if __name__=='__main__':main()
