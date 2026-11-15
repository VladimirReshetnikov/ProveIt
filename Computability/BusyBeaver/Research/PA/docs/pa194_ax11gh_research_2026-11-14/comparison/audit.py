#!/usr/bin/env python3
"""Read-only pinned table census; numeric five-column .tm and explicit JSON rows.

JSON recognition: whole multi-line table strings, lists of five-field rows,
lists of row strings, or dictionaries keyed by '(state,read)' / 'state read'
whose values are three-field (write, direction, successor) arrays. It does
not execute generators or parse tables buried in prose, Lean, or JSONL.
"""
import argparse, csv, hashlib, io, json, re, subprocess, zipfile
from pathlib import Path
from collections import Counter

def sha(b): return hashlib.sha256(b).hexdigest()

def parse(data):
    if isinstance(data, bytes): data=data.decode('utf-8')
    rows={}; declared=None
    for line in data.splitlines():
        if not line.strip(): continue
        if line.lstrip().startswith('#'):
            m=re.search(r'\bstart\s*(\d+)',line)
            if m and declared is None: declared=int(m[1])
            continue
        q,b,w,d,n=line.split()
        q,b,w,n=map(int,(q,b,w,n))
        if b not in (0,1) or w not in (0,1) or d not in ('L','R') or (q,b) in rows:
            raise ValueError('bad row')
        rows[q,b]=(w,d,n)
    states=sorted({q for q,b in rows})
    if not states or len(rows)!=2*len(states): raise ValueError('incomplete')
    halts={n for w,d,n in rows.values()}-set(states)
    if len(halts)!=1: raise ValueError('not one external halt')
    if declared is not None and declared not in states: raise ValueError('bad start')
    start=declared if declared is not None else 0 if states==list(range(len(states))) else None
    return rows,states,start,declared is not None

def table_bytes(rows):
    return ''.join(f'{q} {b} {w} {d} {n}\n' for (q,b),(w,d,n) in sorted(rows.items())).encode()

def rooted(rows,states,start,mirror=False,flip=False,loose=False):
    index={start:0}; order=[start]; out=[]
    for q in order:
        for b in (0,1):
            w,d,n=rows[q,b^flip]
            w^=flip
            if mirror: d='L' if d=='R' else 'R'
            if n in states:
                if n not in index: index[n]=len(index);order.append(n)
                out.append((w,d,index[n]))
            else: out.append((0,'R',-1) if loose else (w,d,-1))
    return tuple(out),len(order)

def encode(t): return json.dumps(t,separators=(',',':')).encode()

def canonical(rows,states,**opts):
    ss=set(states); vals=[rooted(rows,ss,q,**opts) for q in states]
    vals=[v for v,n in vals if n==len(states)]
    return min(vals) if vals else None

def bisimulation_count(rows,states):
    """Greatest immediate-action congruence, halt kept separate."""
    ss=set(states);block={q:0 for q in states}
    while True:
        signatures={q:tuple((w,d,block[n] if n in ss else -1)
                    for b in (0,1) for w,d,n in [rows[q,b]]) for q in states}
        ids={v:i for i,v in enumerate(sorted(set(signatures.values())))}
        new={q:ids[signatures[q]] for q in states}
        if len(set(new.values()))==len(set(block.values())):return len(ids)
        block=new

def json_tables(obj,path='$'):
    if isinstance(obj,str):
        if '\n' in obj and re.search(r'\b[LR]\b',obj):
            try: yield path,parse(obj)
            except (ValueError,UnicodeError): pass
    elif isinstance(obj,list):
        attempt=None
        if obj and all(isinstance(x,list) and len(x)==5 for x in obj):
            attempt='\n'.join(' '.join(map(str,x)) for x in obj)
        elif obj and all(isinstance(x,str) and len(x.split())==5 for x in obj):
            attempt='\n'.join(obj)
        if attempt is not None:
            try: yield path,parse(attempt); return
            except (ValueError,UnicodeError): pass
        for i,x in enumerate(obj):
            if isinstance(x,(dict,list,str)): yield from json_tables(x,path+'/'+str(i))
    elif isinstance(obj,dict):
        attempt=[]
        for k,v in obj.items():
            m=re.fullmatch(r'\(?\s*(\d+)\s*[, :/]\s*([01])\s*\)?',k)
            if not m or not isinstance(v,list) or len(v)!=3: break
            attempt.append(' '.join([m[1],m[2],*map(str,v)]))
        else:
            if attempt:
                try: yield path,parse('\n'.join(attempt)); return
                except (ValueError,UnicodeError): pass
        for k,v in obj.items():
            if isinstance(v,(dict,list,str)): yield from json_tables(v,path+'/'+k)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,required=True)
    ap.add_argument('--pin',default='32d0d8b7d93a63ad4106c18cdb29b37927acdad2')
    ap.add_argument('--output',type=Path,required=True);ap.add_argument('--candidate',type=Path)
    ap.add_argument('--tm-only',action='store_true',help='Omit direct JSON files; archives still inspect explicit JSON tables.')
    a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=True)
    (a.output/'tables').mkdir(exist_ok=True)
    tree=subprocess.check_output(['git','ls-tree','-r',a.pin,'Computability/BusyBeaver/Research/PA','docs/incoming'],cwd=a.repo,text=True)
    entries=[]
    for line in tree.splitlines():
        meta,p=line.split('\t',1);mode,typ,h=meta.split()
        if typ=='blob' and p.endswith(('.tm','.zip') if a.tm_only else ('.tm','.zip','.json')): entries.append((p,h))
    # This enumeration never asks a promisor remote for absent objects.
    local=subprocess.check_output(['git','cat-file','--batch-all-objects','--batch-check=%(objectname)'],cwd=a.repo,text=True)
    available=set(local.splitlines()); missing=[]; occurrences=[]; tables={}; zips={}; errors=[]
    seen_payload={}; stats=Counter()
    def add(loc,item,source_hash):
        rows,states,start,declared=item; b=table_bytes(rows);h=sha(b)
        tables.setdefault(h,{'rows':rows,'states':states,'data':b})
        occurrences.append({'locator':loc,'normalized_sha256':h,'source_sha256':source_hash,'states':len(states),'start':start,'declared_start':declared})
    def inspect(data,loc):
        stats['payloads']+=1; h=sha(data)
        if loc.endswith('.zip'):
            stats['archive_references']+=1
            if h in zips:
                stats['duplicate_archive_references']+=1;return
            zips[h]=loc
            try:
                with zipfile.ZipFile(io.BytesIO(data)) as z:
                    for n in z.namelist():
                        if n.endswith(('.tm','.json','.zip')):inspect(z.read(n),loc+'!'+n)
            except Exception as e:errors.append({'locator':loc,'error':repr(e)})
        elif loc.endswith('.tm'):
            try:add(loc,parse(data),h)
            except Exception as e:errors.append({'locator':loc,'error':repr(e)})
        elif loc.endswith('.json'):
            if h in seen_payload:
                for sub,item in seen_payload[h]:add(loc+'#'+sub,item,h)
                return
            if b'"L"' not in data and b'"R"' not in data and not re.search(rb'\b[LR]\b',data):return
            try:
                obj=json.loads(data)
                found=list(json_tables(obj));seen_payload[h]=found
                for sub,item in found:add(loc+'#'+sub,item,h)
            except Exception as e:errors.append({'locator':loc,'error':repr(e)})
    p=subprocess.Popen(['git','cat-file','--batch'],cwd=a.repo,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
    for i,(path,h) in enumerate(entries):
        if h not in available:
            missing.append({'path':path,'git_blob':h});continue
        p.stdin.write((h+'\n').encode());p.stdin.flush()
        hdr=p.stdout.readline().decode().split()
        if len(hdr)!=3: raise RuntimeError(hdr)
        data=p.stdout.read(int(hdr[2]));assert p.stdout.read(1)==b'\n'
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==h
        inspect(data,path)
        if i%1000==0: print('read',i,'/',len(entries),'tables',len(tables),flush=True)
    p.stdin.close();p.wait()
    (a.output/'missing.json').write_text(json.dumps(missing,indent=2))
    print('classifying',len(tables),'normalized tables',flush=True)
    classes={}; nonspanning=[]
    for i,(h,t) in enumerate(tables.items()):
        rows,states=t['rows'],t['states'];c=canonical(rows,states)
        t['canonical']=c
        if c is None:
            nonspanning.append(h);t['class']=None;continue
        ch=sha(encode(c));t['class']=ch
        if ch not in classes:
            strong=min(canonical(rows,states,mirror=m,flip=f,loose=True) for m in (False,True) for f in (False,True)) if len(states)==194 else None
            classes[ch]={'states':len(states),'normalized_table':h,'strong_class':sha(encode(strong)) if strong else None,'self_loops':sum(q==n for (q,b),(w,d,n) in rows.items()),'immediate_action_bisimulation_states':bisimulation_count(rows,states) if len(states)==194 else None}
            if len(states)==194:(a.output/'tables'/(ch+'.tm')).write_bytes(t['data'])
        if i%100==0: print('classified',i,'/',len(tables),flush=True)
    for o in occurrences:o['class']=tables[o['normalized_sha256']]['class']
    with (a.output/'occurrences.csv').open('w') as f:
        w=csv.DictWriter(f,fieldnames=list(occurrences[0]) if occurrences else []);w.writeheader();w.writerows(occurrences)
    (a.output/'classes.json').write_text(json.dumps(classes,indent=2))
    summary={'pin':a.pin,'tm_only':a.tm_only,'tracked_selected_files':len(entries),'missing_tracked_files':len(missing),'occurrences':len(occurrences),'normalized_tables':len(tables),'spanning_classes':len(classes),'nonspanning_tables':nonspanning,'classes_by_state_count':dict(sorted(Counter(c['states'] for c in classes.values()).items())),'archive_payloads':len(zips),'archive_sources':zips,'errors':errors,**stats}
    if a.candidate:
        data=a.candidate.read_bytes();rows,states,start,declared=parse(data)
        c=canonical(rows,states);strong=min(canonical(rows,states,mirror=m,flip=f,loose=True) for m in (False,True) for f in (False,True))
        ch=sha(encode(c));sh=sha(encode(strong))
        novelty={'path':str(a.candidate),'sha256':sha(data),'states':len(states),'rows':len(rows),'start':start,'declared_start':declared,'reachable':rooted(rows,set(states),start)[1] if start is not None else None,'class':ch,'strong_class':sh,'matches':[k for k,v in classes.items() if k==ch or v['strong_class']==sh],'complete_selected_inputs':not missing,'immediate_action_bisimulation_states':bisimulation_count(rows,states),'scope':'All spanning roots, state renaming, mirror, global bit swap, ignore halt action; explicit encodings only.'}
        (a.output/'novelty.json').write_text(json.dumps(novelty,indent=2));summary['novelty']=novelty
    (a.output/'summary.json').write_text(json.dumps(summary,indent=2));print(json.dumps({k:v for k,v in summary.items() if k not in ('archive_sources','errors')},indent=2))
    if missing:raise SystemExit('Incomplete input snapshot: missing tracked blobs are listed in missing.json.')
    if any(e['locator'].endswith('.zip') for e in errors):raise SystemExit('An archive failed to open; inspect summary.json.')
if __name__=='__main__':main()
