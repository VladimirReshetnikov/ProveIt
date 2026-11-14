#!/usr/bin/env python3
"""Read-only corpus inventory of complete binary numeric five-column TMs.
Independent parser and canonicalization; no candidate is deemed correct by census.
"""
import argparse,csv,hashlib,io,json,re,zipfile
from collections import Counter,defaultdict,deque
from pathlib import Path

ROW=re.compile(rb'^\s*\d+\s+[01]\s+[01]\s+[LR]\s+\d+\s*$')

def parse(data):
    lines=[l.strip() for l in data.splitlines() if l.strip() and not l.lstrip().startswith(b'#')]
    if not lines or any(ROW.fullmatch(l) is None for l in lines): return None
    delta={}
    for l in lines:
        q,r,w,d,t=l.split();q,r,w,t=map(int,(q,r,w,t));d=d.decode()
        if (q,r) in delta: return None
        delta[q,r]=(w,d,t)
    states=sorted({q for q,r in delta})
    if len(delta)!=2*len(states) or any((q,r) not in delta for q in states for r in (0,1)): return None
    halt=sorted({t for w,d,t in delta.values()}-set(states))
    if len(halt)!=1:return None
    declared=re.search(rb'\bstart\s*(\d+)',b'\n'.join(l for l in data.splitlines() if l.lstrip().startswith(b'#')),re.I)
    start=int(declared[1]) if declared else (0 if states==list(range(len(states))) else None)
    return delta,states,halt[0],start

def rooted(delta,states,start,mirror=False,complement=False):
    seen={start:0};queue=[start];rows=[]
    for q in queue:
        for b in (0,1):
            w,d,t=delta[q,b^complement]
            if t in states:
                if t not in seen:seen[t]=len(seen);queue.append(t)
                k=seen[t]
            else:k=-1
            rows.append((w^complement,('R' if d=='L' else 'L') if mirror else d,k))
    raw=json.dumps(rows,separators=(',',':')).encode()
    return hashlib.sha256(raw).hexdigest(),len(queue)

def classify(parsed):
    delta,qlist,halt,start=parsed;states=set(qlist)
    rr=[rooted(delta,states,q) for q in qlist];reach=max(n for h,n in rr)
    rootfree=min(h for h,n in rr if n==reach)
    root_h,root_n=rooted(delta,states,start) if start is not None else (None,None)
    orbit=[]
    for mir,comp in [(False,False),(True,False),(False,True),(True,True)]:
        hs=[rooted(delta,states,q,mir,comp) for q,(h,n) in zip(qlist,rr) if n==reach]
        orbit.extend(h for h,n in hs)
    return {'working_states':len(qlist),'rows':len(delta),'start':start,'halt_label':halt,
            'max_graph_reachable':reach,'start_graph_reachable':root_n,'rooted_sha256':root_h,
            'rootfree_sha256':rootfree,'symmetry_rootfree_sha256':min(orbit)}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--incoming',type=Path);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--cache',type=Path);a=ap.parse_args();a.out.mkdir(parents=True,exist_ok=True)
    prior={}
    if a.cache and a.cache.exists():
        prior={v['sha256']:{k:x for k,x in v.items() if k not in ['sha256','size_bytes','locators','packets']} for v in json.loads(a.cache.read_text())}
    entries=[];payloads={};archive_entries=[];archive_seen=set();probes=Counter();cache={}
    def file(data,loc,packet):
        suf=Path(loc.split('!')[-1]).suffix.lower()
        if suf=='.zip':
            zsha=hashlib.sha256(data).hexdigest();archive_entries.append({'locator':loc,'sha256':zsha,'packet':packet})
            if zsha in archive_seen:return
            archive_seen.add(zsha)
            try:
                with zipfile.ZipFile(io.BytesIO(data)) as z:
                    for zi in z.infolist():
                        if zi.is_dir():continue
                        if Path(zi.filename).suffix.lower() in ['.tm','.txt','.tsv','.csv','.zip']:
                            file(z.read(zi),loc+'!'+zi.filename,packet)
            except Exception as e:archive_entries[-1]['error']=str(e)
            return
        if suf not in ['.tm','.txt','.tsv','.csv']:return
        probes[suf]+=1
        if len(data)>2000000:return
        sha=hashlib.sha256(data).hexdigest()
        if sha not in cache:cache[sha]=parse(data)
        parsed=cache[sha]
        if parsed is None:return
        if sha not in payloads:
            payloads[sha]={'sha256':sha,'size_bytes':len(data),**(prior[sha] if sha in prior else classify(parsed)),'locators':[],'packets':[]}
        v=payloads[sha];v['locators'].append(loc)
        if packet not in v['packets']:v['packets'].append(packet)
        entries.append({'locator':loc,'packet':packet,'sha256':sha,'working_states':v['working_states'],'rootfree_sha256':v['rootfree_sha256'],'symmetry_rootfree_sha256':v['symmetry_rootfree_sha256']})
    root=a.repo/'Computability/BusyBeaver/Research/PA'
    for p in sorted(root.rglob('*')):
        if p.is_file() and p.suffix.lower() in ['.tm','.txt','.tsv','.csv','.zip']:
            rel=p.relative_to(a.repo).as_posix();r=p.relative_to(root).parts
            packet=('filed/'+r[1]) if r[0]=='docs' and len(r)>2 else ('direct/'+r[0])
            file(p.read_bytes(),rel,packet)
    if a.incoming and a.incoming.exists():
        for p in sorted(a.incoming.glob('*.zip')):file(p.read_bytes(),'docs/incoming/'+p.name,'incoming/'+p.name)
    vals=list(payloads.values())
    summary={'scope':'complete numeric five-column binary tables in .tm/.txt/.tsv/.csv; ZIPs recursively; excludes pure source and JSON-only encodings; table count includes diagnostics/rejected inputs',
      'repo':str(a.repo),'probed_extensions':dict(probes),'table_occurrences':len(entries),'byte_forms':len(vals),
      'labeled_tables':len({json.dumps(sorted((str(k),v) for k,v in cache[x['sha256']][0].items())) for x in vals}),
      'rootfree_classes':len({v['rootfree_sha256'] for v in vals}),'rootfree_symmetry_classes':len({v['symmetry_rootfree_sha256'] for v in vals}),
      'byte_forms_by_states':dict(sorted(Counter(v['working_states'] for v in vals).items())),
      'rootfree_classes_by_states':dict(sorted((s,len({v['rootfree_sha256'] for v in vals if v['working_states']==s})) for s in {v['working_states'] for v in vals})),
      'archives':archive_entries}
    for name,obj in [('summary.json',summary),('tables.json',vals),('occurrences.json',entries)]: (a.out/name).write_text(json.dumps(obj,indent=2)+'\n')
    with (a.out/'frontier194.csv').open('w',newline='') as f:
        cols=['working_states','sha256','rooted_sha256','rootfree_sha256','symmetry_rootfree_sha256','start','max_graph_reachable','locator','packets']
        w=csv.DictWriter(f,fieldnames=cols);w.writeheader()
        grouped=defaultdict(list)
        for v in vals:
            if v['working_states']==194:grouped[v['rootfree_sha256']].append(v)
        for h,g in sorted(grouped.items()):
            v=next((v for v in g if v['start']==0),g[0]);row={k:v.get(k) for k in cols};row['locator']=v['locators'][0];row['packets']=' | '.join(sorted({p for v in g for p in v['packets']}));w.writerow(row)
    print(json.dumps({k:v for k,v in summary.items() if k!='archives'},indent=2))
if __name__=='__main__':main()
