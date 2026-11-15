#!/usr/bin/env python3
"""Reproducible pinned PA table census, without executing source generators.

Inputs: repo_tables (all tracked .tm files, exact Git-blob checked), the six
current incoming ZIPs recursively (.tm and four literal JSON table encodings).
Every complete table's unrooted spanning action graph is canonicalized. Declared
or conventional starts are separately recorded, never used to discard other
root choices. Disconnected graphs are reported separately, not conflated with
truncated reachable subgraphs. Global symbol exchange is used only for the
stronger structural novelty comparison, not as blank-zero execution equivalence.
"""
from pathlib import Path
from collections import Counter,defaultdict
import hashlib,json,io,zipfile,re,csv,argparse
BASE=Path(__file__).resolve().parents[1]
PIN='7c0bb454cf73c29ca1c385f9fec856ddd236a7cb'
def sha(b):return hashlib.sha256(b).hexdigest()
def encode(x):return json.dumps(x,separators=(',',':')).encode()
def parse(data):
    if isinstance(data,bytes):data=data.decode('utf-8')
    rows={};start=None
    for line in data.splitlines():
        if not line.strip():continue
        if line.lstrip().startswith('#'):
            m=re.search(r'\bstart\s*(\d+)',line)
            if m and start is None:start=int(m[1])
            continue
        q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
        if b not in (0,1) or w not in (0,1) or d not in ('L','R') or (q,b) in rows:raise ValueError('bad row')
        rows[q,b]=(w,d,n)
    states=sorted({q for q,b in rows})
    if not states or len(rows)!=2*len(states):raise ValueError('incomplete table')
    if start is not None and start not in states:raise ValueError('declared start missing')
    return rows,states,start

def normalized(rows):return ''.join(f'{q} {b} {w} {d} {n}\n' for (q,b),(w,d,n) in sorted(rows.items())).encode()
def traverse(rows,states,start,mirror=False,flip=False,loose=False):
    ss=set(states);ix={start:0};order=[start];out=[]
    for q in order:
        for b in (0,1):
            w,d,n=rows[q,b^flip];w^=flip
            if mirror:d='L' if d=='R' else 'R'
            if n in ss:
                if n not in ix:ix[n]=len(ix);order.append(n)
                out.append((w,d,ix[n]))
            else:out.append((0,'R',-1) if loose else (w,d,-1))
    return tuple(out),len(order)
def canonical(rows,states,mirror=False,flip=False,loose=False):
    """Exact minimum BFS serialization over spanning roots; prefix pruning."""
    ss=set(states);best=None
    for start in states:
        ix={start:0};order=[start];out=[];cmp=0;rejected=False
        for q in order:
            for b in (0,1):
                w,d,n=rows[q,b^flip];w^=flip
                if mirror:d='L' if d=='R' else 'R'
                if n in ss:
                    if n not in ix:ix[n]=len(ix);order.append(n)
                    item=(w,d,ix[n])
                else:item=(0,'R',-1) if loose else (w,d,-1)
                if best is not None and cmp==0:
                    if item>best[len(out)]:rejected=True;break
                    if item<best[len(out)]:cmp=-1
                out.append(item)
            if rejected:break
        if not rejected and len(order)==len(states):
            t=tuple(out)
            if best is None or t<best:best=t
    return best

def immediate_congruence(rows,states):
    ss=set(states);blocks={q:0 for q in states}
    while True:
        sig={q:tuple((w,d,blocks[n] if n in ss else -1) for b in (0,1) for w,d,n in [rows[q,b]]) for q in states}
        labels={s:i for i,s in enumerate(sorted(set(sig.values())))}
        nxt={q:labels[sig[q]] for q in states}
        if len(set(nxt.values()))==len(set(blocks.values())):return len(labels)
        blocks=nxt

def json_tables(obj,path='$'):
    if isinstance(obj,str):
        if '\n' in obj and re.search(r'\b[LR]\b',obj):
            try:yield path,parse(obj)
            except (ValueError,UnicodeError):pass
    elif isinstance(obj,list):
        attempt=None
        if obj and all(isinstance(x,list) and len(x)==5 for x in obj):attempt='\n'.join(' '.join(map(str,x)) for x in obj)
        elif obj and all(isinstance(x,str) and len(x.split())==5 for x in obj):attempt='\n'.join(obj)
        if attempt:
            try:yield path,parse(attempt);return
            except (ValueError,UnicodeError):pass
        for i,x in enumerate(obj):
            if isinstance(x,(dict,list,str)):yield from json_tables(x,path+'/'+str(i))
    elif isinstance(obj,dict):
        attempt=[]
        for k,v in obj.items():
            m=re.fullmatch(r'\(?\s*(\d+)\s*[, :/]\s*([01])\s*\)?',k)
            if not m or not isinstance(v,list) or len(v)!=3:break
            attempt.append(' '.join([m[1],m[2],*map(str,v)]))
        else:
            if attempt:
                try:yield path,parse('\n'.join(attempt));return
                except (ValueError,UnicodeError):pass
        for k,v in obj.items():
            if isinstance(v,(dict,list,str)):yield from json_tables(v,path+'/'+k)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--incoming-only',action='store_true');ap.add_argument('--output',type=Path,default=BASE/'census_work'/'results');args=ap.parse_args()
    out=args.output;out.mkdir(parents=True,exist_ok=True);(out/'frontier194').mkdir(exist_ok=True)
    tables={};occ=[];zip_seen={};json_seen={};stats=Counter();errors=[];archive_refs=[]
    def add(loc,datahash,item,kind):
        rows,states,declared=item;nb=normalized(rows);h=sha(nb)
        tables.setdefault(h,{'rows':rows,'states':states,'bytes':nb})
        conv=0 if states==list(range(len(states))) else None
        occ.append({'locator':loc,'payload_sha256':datahash,'normalized_sha256':h,'states':len(states),'declared_start':declared,'conventional_start':declared if declared is not None else conv,'start_status':'declared' if declared is not None else 'dense convention only; verify provenance' if conv is not None else 'unresolved','encoding':kind})
    def inspect(data,loc,depth=0):
        stats['payload_occurrences']+=1;h=sha(data)
        if loc.endswith('.zip'):
            if depth>12:raise ValueError('archive nesting limit')
            archive_refs.append({'locator':loc,'sha256':h,'duplicate_of':zip_seen.get(h)})
            if h in zip_seen:return
            zip_seen[h]=loc
            with zipfile.ZipFile(io.BytesIO(data)) as z:
                for m in z.infolist():
                    if m.filename.endswith(('.tm','.json','.zip')):inspect(z.read(m),loc+'!'+m.filename,depth+1)
        elif loc.endswith('.tm'):
            try:add(loc,h,parse(data),'tm')
            except Exception as e:errors.append({'locator':loc,'error':repr(e)})
        elif loc.endswith('.json'):
            if h not in json_seen:
                found=[]
                if b'"L"' in data or b'"R"' in data or re.search(rb'\b[LR]\b',data):
                    try:found=list(json_tables(json.loads(data)))
                    except Exception as e:errors.append({'locator':loc,'error':repr(e)})
                json_seen[h]=found
            for sub,item in json_seen[h]:add(loc+'#'+sub,h,item,'explicit_json')
    if not args.incoming_only:
        fetch=json.loads((BASE/'census_work'/'fetch_tables_result.json').read_text())
        assert not fetch['errors'],fetch['errors']
        for e in json.loads((BASE/'census_work'/'repo_table_sources.json').read_text()):
            p=BASE/'census_work'/'repo_tables'/e['path'];data=p.read_bytes()
            assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']
            inspect(data,e['path'])
    if not args.incoming_only:
        for e in json.loads((BASE/'census_work'/'repo_archive_sources.json').read_text()):
            p=BASE/'census_work'/'repo_archives'/e['path'];data=p.read_bytes()
            assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']
            inspect(data,e['path'])
    for p in sorted((BASE/'incoming_downloads').glob('*.zip')):inspect(p.read_bytes(),'docs/incoming/'+p.name)
    print('parsed occurrences',len(occ),'normalized',len(tables),'archives',len(zip_seen),flush=True)
    classes={};nonspanning=[]
    for i,(h,t) in enumerate(tables.items()):
        c=canonical(t['rows'],t['states']);ch=sha(encode(c)) if c is not None else None;t['class']=ch
        if ch is None:
            nonspanning.append({'normalized_sha256':h,'states':len(t['states'])});continue
        if ch not in classes:
            strong=None;mirror=None;cong=None
            if len(t['states'])==194:
                mirror=min(c,canonical(t['rows'],t['states'],mirror=True))
                strong=min(canonical(t['rows'],t['states'],mirror=m,flip=f,loose=True) for m in (False,True) for f in (False,True))
                cong=immediate_congruence(t['rows'],t['states'])
                (out/'frontier194'/(ch+'.tm')).write_bytes(t['bytes'])
            classes[ch]={'states':len(t['states']),'normalized_sha256':h,'mirror_class':sha(encode(mirror)) if mirror else None,'strong_class':sha(encode(strong)) if strong else None,'immediate_congruence_controls':cong}
        if (i+1)%100==0:print('classified',i+1,'/',len(tables),flush=True)
    for o in occ:
        t=tables[o['normalized_sha256']];o['graph_class']=t['class'];s=o['conventional_start']
        if s is not None:
            c,r=traverse(t['rows'],t['states'],s);o['rooted_action_class']=sha(encode(c));o['reachable']=r
        else:o['rooted_action_class']=None;o['reachable']=None
    cols=list(occ[0]);
    with (out/'occurrences.csv').open('w') as f:
        w=csv.DictWriter(f,fieldnames=cols);w.writeheader();w.writerows(occ)
    (out/'classes.json').write_text(json.dumps(classes,indent=2)+'\n')
    (out/'archives.json').write_text(json.dumps(archive_refs,indent=2)+'\n')
    (out/'errors.json').write_text(json.dumps(errors,indent=2)+'\n')
    (out/'nonspanning.json').write_text(json.dumps(nonspanning,indent=2)+'\n')
    byclass=defaultdict(list)
    for o in occ:byclass[o['graph_class']].append(o['locator'])
    byclass.pop(None,None)
    (out/'class_occurrences.json').write_text(json.dumps(byclass,indent=2)+'\n')
    summary={'pin':PIN,'incoming_only':args.incoming_only,'tracked_tm_files':0 if args.incoming_only else fetch['files'],'tracked_pa_archives':0 if args.incoming_only else len(json.loads((BASE/'census_work'/'repo_archive_sources.json').read_text())),'current_incoming_archives':len(list((BASE/'incoming_downloads').glob('*.zip'))),'unique_recursively_inspected_archives':len(zip_seen),'table_occurrences':len(occ),'normalized_tables':len(tables),'spanning_classes':len(classes),'classes_by_working_states':dict(sorted(Counter(x['states'] for x in classes.values()).items())),'frontier194_mirror_classes':len({x['mirror_class'] for x in classes.values() if x['states']==194}),'frontier194_strong_classes':len({x['strong_class'] for x in classes.values() if x['states']==194}),'nonspanning_normalized_tables':nonspanning,'explicit_json_occurrences':sum(o['encoding']=='explicit_json' for o in occ),'errors':len(errors),'scope':'All tracked PA .tm and .zip plus recursively recognized .tm and explicit JSON tables in current incoming ZIPs. Direct tracked JSON generators and prose are outside this census. Root-convention status is explicit; full-class novelty permits all spanning roots.'}
    (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2),flush=True)
if __name__=='__main__':main()
