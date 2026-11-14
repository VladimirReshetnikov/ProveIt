"""Read-only literal-table inventory for the PA research corpus.

Recognizes complete five-column numeric binary whitespace-separated .tm/.txt/.tsv/.csv tables with exactly
one undefined halting target. Such recognition is not a correctness claim.
Canonical graph comparison forgets the designated start but keeps action labels.
"""
from pathlib import Path
import argparse, collections, hashlib, io, json, subprocess, zipfile

def digest(b): return hashlib.sha256(b).hexdigest()

def parse_table(b):
    try: text = b.decode('utf-8')
    except UnicodeDecodeError: return None
    rows = {}
    for line in text.splitlines():
        line = line.strip()
        if not line or line.startswith(('#', '//', ';')): continue
        p = line.split()
        if (len(p) != 5 or not p[0].isdigit() or p[1] not in ('0','1')
                or p[2] not in ('0','1') or p[3] not in ('L','R')
                or not p[4].isdigit()): return None
        q,b,w,d,t = p
        key = int(q),int(b)
        if key in rows: return None
        rows[key] = int(w),d,int(t)
    states = {q for q,b in rows}
    if not states or set(rows) != {(q,b) for q in states for b in (0,1)}:
        return None
    halts = {t for w,d,t in rows.values()} - states
    if len(halts) != 1: return None
    return rows, states, next(iter(halts))

def canonical(data, root, reflect=False, complement=False):
    rows,states,halt = data
    labels = {root:0}; todo = [root]; ans = []
    for q in todo:
        rr = []
        for bit in (0,1):
            w,d,t = rows[q, bit ^ complement]
            if t == halt: k = -1
            else:
                if t not in labels: labels[t] = len(todo); todo.append(t)
                k = labels[t]
            rr.append((w ^ complement, ('R' if d == 'L' else 'L') if reflect else d, k))
        ans.append(tuple(rr))
    return tuple(ans) if len(todo) == len(states) else None

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True); args=ap.parse_args()
    repo=args.repo.resolve(); out=args.output.resolve();out.mkdir(parents=True,exist_ok=True)
    raw_dir=out/'tables';raw_dir.mkdir(exist_ok=True)
    inventory=[];raw={};archives=[];archive_refs=[];seen_archives=set();errors=[]
    def add_table(b,path):
        data = parse_table(b)
        if data is None: return
        h=digest(b); n=len(data[1]); inventory.append(dict(path=path,sha256=h,states=n,halt=data[2]))
        if h not in raw:
            raw[h]=dict(data=data,first_path=path,bytes=len(b))
            if n<=196:(raw_dir/(h+'.tm')).write_bytes(b)
    def scan_archive(b,path,depth):
        h=digest(b);archive_refs.append(dict(path=path,sha256=h,depth=depth))
        if h in seen_archives:return
        seen_archives.add(h)
        try:
            with zipfile.ZipFile(io.BytesIO(b)) as z:
                archives.append(dict(path=path,sha256=h,bytes=len(b),depth=depth,members=len(z.infolist())))
                for item in z.infolist():
                    if item.is_dir():continue
                    p=path+'!'+item.filename; ext=Path(item.filename).suffix.lower()
                    if ext=='.zip':scan_archive(z.read(item),p,depth+1)
                    elif ext in ('.tm','.txt','.tsv','.csv'):add_table(z.read(item),p)
        except Exception as e:errors.append(dict(path=path,error=str(e)))
    incoming=repo/'docs/incoming'
    for p in sorted(incoming.glob('*.zip')):
        print('incoming',p.name,flush=True);scan_archive(p.read_bytes(),str(p.relative_to(repo)),0)
    pa=repo/'Computability/BusyBeaver/Research/PA'
    paths=subprocess.check_output(['rg','--files','--hidden',str(pa)]).decode().splitlines()
    for name in sorted(paths):
        p=Path(name); ext=p.suffix.lower(); rel=str(p.relative_to(repo))
        if ext=='.zip':scan_archive(p.read_bytes(),rel,0)
        elif ext in ('.tm','.txt','.tsv','.csv'):add_table(p.read_bytes(),rel)
    records=[]; norm_cache={}
    for i,(h,item) in enumerate(raw.items()):
        data=item['data'];rows,states,halt=data
        labeled=tuple(sorted(rows.items()))
        if labeled not in norm_cache:
            forms=[c for q in sorted(states) if (c:=canonical(data,q)) is not None]
            canon=min(forms) if forms else None
            # Exact action-preserving graph class; alternate transformations are
            # emitted for the small frontier only, to support cosmetic checks.
            gs=digest(repr(canon).encode()) if canon is not None else None
            cosmetic=gs
            if len(states)<=196 and canon is not None:
                forms.extend(c for r,cx in ((True,False),(False,True),(True,True))
                             for q in sorted(states)
                             if (c:=canonical(data,q,r,cx)) is not None)
                cosmetic=digest(repr(min(forms)).encode())
            norm_cache[labeled]=(gs,cosmetic)
        gs,cosmetic=norm_cache[labeled]
        records.append(dict(sha256=h,states=len(states),halt=halt,bytes=item['bytes'],
                            graph_hash=gs,cosmetic_hash=cosmetic,first_path=item['first_path']))
        if i%100==0:print('classified',i+1,'/',len(raw),flush=True)
    classes=collections.defaultdict(list)
    for x in records:classes[x['states'],x['graph_hash']].append(x['sha256'])
    result=dict(snapshot=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD']).decode().strip(),
        scope=__doc__,summary=dict(top_level_incoming_archives=len(list(incoming.glob('*.zip'))),
        direct_pa_files=len(paths),distinct_archive_payloads=len(archives),archive_references=len(archive_refs),
        literal_table_occurrences=len(inventory),literal_byte_identities=len(raw),
        root_free_graph_classes=sum(g is not None for n,g in classes),
        unclassified_byte_identities=sum(x['graph_hash'] is None for x in records),
        occurrences_by_state_count=dict(sorted(collections.Counter(x['states'] for x in inventory).items())),
        identities_by_state_count=dict(sorted(collections.Counter(x['states'] for x in records).items())),
        graphs_by_state_count=dict(sorted(collections.Counter(n for n,g in classes if g is not None).items())),
        errors=errors),archives=archives,archive_references=archive_refs,occurrences=inventory,
        identities=records,classes=[dict(states=n,graph_hash=g,sha256s=hs,
            paths=[x['path'] for x in inventory if x['sha256'] in hs]) for (n,g),hs in classes.items()])
    (out/'census.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result['summary'],indent=2))
    for c in result['classes']:
        if c['states']<=195:print(c['states'],c['graph_hash'],len(c['sha256s']),c['paths'][0])

if __name__=='__main__':main()
