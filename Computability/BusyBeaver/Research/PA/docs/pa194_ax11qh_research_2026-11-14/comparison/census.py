#!/usr/bin/env python3
"""Inventory literal binary L/R TMs and compare complete 193/194-state graphs.

Only explicit data are recognized; arbitrary generators and prose are not run.
Evidence classifications are imported annotations, never correctness verdicts.
No table is modified. Canonical forms enumerate every spanning initial root,
reading symbol 0 before 1. Optional broad equivalence additionally allows tape
reflection, global symbol interchange, and ignores write/move into halt.
"""
from pathlib import Path
import argparse,collections,csv,hashlib,io,json,re,zipfile,time

def validate(rows):
    if not rows:return None
    qs={q for q,b in rows}
    if any((q,b) not in rows for q in qs for b in (0,1)):return None
    if any(b not in (0,1) or w not in (0,1) or d not in ('L','R') or not isinstance(t,int) or t<0 for (q,b),(w,d,t) in rows.items()):return None
    hs={t for w,d,t in rows.values()}-qs
    if len(hs)!=1:return None
    return rows,qs,next(iter(hs))
def parse_text(data):
    try:s=data.decode('ascii')
    except UnicodeDecodeError:return None
    rows={}
    for l in s.splitlines():
        l=l.strip()
        if not l or l.startswith('#'):continue
        m=re.fullmatch(r'(\d+)\s+([01])\s+([01])\s+([LR])\s+(\d+)',l)
        if not m:return None
        q,b,w,d,t=m.groups();key=(int(q),int(b))
        if key in rows:return None
        rows[key]=(int(w),d,int(t))
    return validate(rows)
def isint(x):return isinstance(x,int) and not isinstance(x,bool) and x>=0
def move(x):return ('L' if x==-1 else 'R' if x==1 else x) if x in ('L','R',-1,1) and not isinstance(x,bool) else None
def action(x):return isinstance(x,(list,tuple)) and len(x)==3 and x[0] in (0,1) and move(x[1]) is not None and isint(x[2])
def normal(x):return (int(x[0]),move(x[1]),int(x[2]))
def record(x):
    if not isinstance(x,dict):return None
    keys=[('state','source','q','current_state','from'),('read','symbol','read_bit','read_symbol','b'),('write','write_bit','write_symbol','w'),('direction','move','dir','d'),('next','target','next_state','to','t')]
    v=[next((x[k] for k in choices if k in x),None) for choices in keys]
    return v if isint(v[0]) and v[1] in (0,1) and action(v[2:]) else None
def parse_json_node(x):
    rows={}
    if isinstance(x,str) and '\n' in x:return parse_text(x.encode('utf-8'))
    if isinstance(x,list) and len(x)>1:
        if all(isinstance(a,list) and len(a)==5 and isint(a[0]) and a[1] in (0,1) and action(a[2:]) for a in x):
            for q,b,w,d,t in x:
                if (q,b) in rows:return None
                rows[q,b]=normal([w,d,t])
        elif all(isinstance(a,list) and len(a)==2 and all(action(b) for b in a) for a in x):rows={(q,b):normal(a) for q,p in enumerate(x) for b,a in enumerate(p)}
        elif len(x)%2==0 and all(action(a) for a in x):rows={(i//2,i%2):normal(a) for i,a in enumerate(x)}
        elif all(record(a) is not None for a in x):
            for q,b,w,d,t in map(record,x):
                if (q,b) in rows:return None
                rows[q,b]=normal([w,d,t])
    elif isinstance(x,dict) and x:
        if all(k.isdigit() and isinstance(v,list) and len(v)==2 and all(action(a) for a in v) for k,v in x.items()):rows={(int(q),b):normal(a) for q,p in x.items() for b,a in enumerate(p)}
        elif all(re.fullmatch(r'\(?\s*\d+\s*[,;:]\s*[01]\s*\)?',k) and action(v) for k,v in x.items()):
            for k,v in x.items():
                q,b=map(int,re.findall(r'\d+',k));rows[q,b]=normal(v)
    return validate(rows)
def normalized_text(data):return ''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(data[0].items()))
def rooted_form(data,start,mirror=False,complement=False,loose=False):
    rows,qs,halt=data;order=[start];index={start:0};out=[]
    for q in order:
        for b in (0,1):
            w,d,t=rows[q,b^int(complement)];w^=int(complement)
            if mirror:d='L' if d=='R' else 'R'
            if t==halt:
                out.extend((0,0,-1) if loose else (w,1 if d=='R' else 0,-1))
            else:
                if t not in index:index[t]=len(order);order.append(t)
                out.extend((w,1 if d=='R' else 0,index[t]))
    return tuple(out),len(order)
def canonical_form(data,broad=False):
    # A complete spanning root is required, so disconnected diagnostics never
    # compare equal merely through a shared reachable component.
    best=None
    for q in sorted(data[1]):
        _,n=rooted_form(data,q)
        if n!=len(data[1]):continue
        variants=((False,False),) if not broad else ((False,False),(False,True),(True,False),(True,True))
        for mir,comp in variants:
            f,_=rooted_form(data,q,mir,comp,broad)
            if best is None or f<best:best=f
    return best
def fingerprint(form):return hashlib.sha256(json.dumps(form,separators=(',',':')).encode()).hexdigest() if form is not None else None

def run(roots,out):
    out.mkdir(parents=True,exist_ok=True);(out/'representatives').mkdir(exist_ok=True)
    seenzip=set();occ=[];unique={};errors=[];scanned=collections.Counter();excluded_fragments=0
    def add(data,path,source_hash,ptr=None):
        nonlocal excluded_fragments
        if len(data[1])==1 and ptr is not None:excluded_fragments+=1;return
        txt=normalized_text(data);h=hashlib.sha256(txt.encode()).hexdigest();unique.setdefault(h,data)
        occ.append({'path':path,'json_pointer':ptr,'source_sha256':source_hash,'normalized_sha256':h,'states':len(data[1]),'halt':data[2]})
    def inspect(b,path,ext):
        scanned[ext]+=1;h=hashlib.sha256(b).hexdigest()
        if ext=='.zip':
            if h in seenzip:return
            seenzip.add(h)
            try:
                with zipfile.ZipFile(io.BytesIO(b)) as z:
                    for m in z.infolist():
                        e=Path(m.filename).suffix.lower()
                        if not m.is_dir() and e in ('.zip','.tm','.txt','.tsv','.csv','.json'):inspect(z.read(m),path+'!'+m.filename,e)
            except Exception as e:errors.append({'path':path,'error':str(e)})
            return
        if ext in ('.tm','.txt','.tsv','.csv'):
            data=parse_text(b)
            if data:add(data,path,h)
            elif ext=='.tm':errors.append({'path':path,'error':'not a complete one-halt numeric binary L/R table'})
        elif ext=='.json':
            if not (b'"L"' in b or b'"R"' in b or b' L ' in b or b' R ' in b or b'"table"' in b or b'"transitions"' in b or re.search(rb'\[\s*\d+\s*,\s*[01]\s*,\s*[01]\s*,\s*-?1\s*,',b)):return
            try:obj=json.loads(b)
            except Exception as e:errors.append({'path':path,'error':str(e)});return
            stack=[('$',obj)]
            while stack:
                ptr,x=stack.pop();data=parse_json_node(x)
                if data:add(data,path,h,ptr);continue
                if isinstance(x,dict):stack.extend((ptr+'/'+str(k),v) for k,v in x.items() if isinstance(v,(list,dict,str)))
                elif isinstance(x,list):stack.extend((ptr+'/'+str(i),v) for i,v in enumerate(x) if isinstance(v,(list,dict,str)))
    # Incoming archives, not their separately extracted copies, avoid duplicate
    # counting of the same archived file while retaining member provenance.
    for root in roots:
        for p in sorted(root.rglob('*')):
            ext=p.suffix.lower()
            if p.is_file() and ext in ('.zip','.tm','.txt','.tsv','.csv','.json'):inspect(p.read_bytes(),str(p),ext)
    print('Scanned',dict(scanned),'normalized identities',len(unique),'occurrences',len(occ),flush=True)
    (out/'occurrences.json').write_text(json.dumps(occ,indent=2))
    classes={};all_ids=[];cachefile=out/'form_cache.json';cache=json.loads(cachefile.read_text()) if cachefile.exists() else {}
    items=list(unique.items())
    for i,(h,data) in enumerate(items):
        n=len(data[1]);d={'normalized_sha256':h,'states':n,'halt':data[2]}
        if n in (193,194):
            if h not in cache:
                strict=canonical_form(data);broad=canonical_form(data,True)
                cache[h]={'strict_graph':fingerprint(strict),'broad_graph':fingerprint(broad),'spanning':strict is not None}
            d.update(cache[h]);g=d['strict_graph'] or 'disconnected:'+h
            if g not in classes:
                classes[g]={**d,'normalized_identities':[]};(out/'representatives'/(g.replace(':','_')+'.tm')).write_text(normalized_text(data))
            classes[g]['normalized_identities'].append(h)
        all_ids.append(d)
        if (i+1)%100==0:print('Classified',i+1,len(items),flush=True);cachefile.write_text(json.dumps(cache))
    cachefile.write_text(json.dumps(cache))
    byhash=collections.defaultdict(list)
    for x in occ:byhash[x['normalized_sha256']].append(x)
    for g,c in classes.items():c['sources']=[x for h in c['normalized_identities'] for x in byhash[h]]
    stats={'scanned_files_by_extension':dict(scanned),'unique_zip_payloads':len(seenzip),'recognized_occurrences':len(occ),'normalized_tables':len(unique),'classes193':sum(c['states']==193 for c in classes.values()),'classes194':sum(c['states']==194 for c in classes.values()),'spanning194':sum(c['states']==194 and c['spanning'] for c in classes.values()),'broad194':len({c['broad_graph'] for c in classes.values() if c['states']==194 and c['spanning']}),'json_fragments_excluded':excluded_fragments,'parse_errors':errors}
    (out/'identities.json').write_text(json.dumps(all_ids,indent=2));(out/'frontier.json').write_text(json.dumps(list(classes.values()),indent=2));(out/'summary.json').write_text(json.dumps(stats,indent=2));print(json.dumps(stats,indent=2),flush=True)
if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('roots',nargs='+',type=Path);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();run(a.roots,a.output)
