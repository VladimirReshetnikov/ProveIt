#!/usr/bin/env python3
"""Supplementary literal JSON transition-table recognizer.

Recognizes row arrays [q,b,w,L/R,t] (also signed moves -1/+1), dense arrays of pairs of action triples,
dense flat arrays of action triples, numeric-state dictionaries of paired
actions, row-record objects, transition-key dictionaries, and embedded whole
text tables. Does not execute program generators or treat source grammars as
physical transition tables. Results are inventory, not correctness claims.
"""
from pathlib import Path
import argparse, collections, hashlib, importlib.util, io, json, re, sys, zipfile

ROOT=Path(__file__).resolve().parent
SCANNER=ROOT/'literal_inventory.py'
spec=importlib.util.spec_from_file_location('census_scanner',SCANNER)
lib=importlib.util.module_from_spec(spec);spec.loader.exec_module(lib)

def integer(x):
    return isinstance(x,int) and not isinstance(x,bool) and x>=0
def direction(x):
    return x in ('L','R',-1,1) and not isinstance(x,bool)
def normalized(x):
    w,d,t=x
    return w,('L' if d == -1 else 'R' if d == 1 else d),t
def action(x):
    return isinstance(x,list) and len(x)==3 and x[0] in (0,1) and direction(x[1]) and integer(x[2])
def validate(rows):
    if not rows:return None
    states={q for q,b in rows}
    if any((q,b) not in rows for q in states for b in (0,1)):return None
    halts={t for w,d,t in rows.values()}-states
    if len(halts)!=1:return None
    return rows,states,next(iter(halts))
def rowrecord(x):
    if not isinstance(x,dict):return None
    def get(names):
        for k in names:
            if k in x:return x[k]
        return None
    q=get(['state','source','q','current_state','from']); b=get(['read','symbol','read_bit','read_symbol','b'])
    w=get(['write','write_bit','write_symbol','w']); d=get(['direction','move','dir','d'])
    t=get(['next','target','next_state','to','t'])
    if integer(q) and b in (0,1) and w in (0,1) and direction(d) and integer(t):return q,b,w,d,t
def decode(node):
    if isinstance(node,str) and '\n' in node:
        return lib.parse_table(node.encode())
    rows={}
    if isinstance(node,list) and len(node)>=2:
        if all(isinstance(x,list) and len(x)==5 and integer(x[0]) and x[1] in (0,1) and x[2] in (0,1) and direction(x[3]) and integer(x[4]) for x in node):
            for q,b,w,d,t in node:
                if (q,b) in rows:return None
                rows[q,b]=normalized((w,d,t))
        elif all(isinstance(x,list) and len(x)==2 and all(action(a) for a in x) for x in node):
            rows={(q,b):normalized(a) for q,pair in enumerate(node) for b,a in enumerate(pair)}
        elif len(node)%2==0 and all(action(x) for x in node):
            rows={(i//2,i%2):normalized(x) for i,x in enumerate(node)}
        elif all(rowrecord(x) is not None for x in node):
            for q,b,w,d,t in map(rowrecord,node):
                if (q,b) in rows:return None
                rows[q,b]=normalized((w,d,t))
    elif isinstance(node,dict) and node:
        if all(k.isdigit() and isinstance(v,list) and len(v)==2 and all(action(a) for a in v) for k,v in node.items()):
            rows={(int(q),b):normalized(a) for q,pair in node.items() for b,a in enumerate(pair)}
        elif all(re.fullmatch(r'\(?\s*\d+\s*[,;:]\s*[01]\s*\)?',k) and action(v) for k,v in node.items()):
            for k,v in node.items():
                q,b=map(int,re.findall(r'\d+',k));rows[q,b]=normalized(v)
    return validate(rows)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('repo',type=Path)
    ap.add_argument('--output',type=Path,default=ROOT/'json_census')
    args=ap.parse_args()
    repo=args.repo.resolve();out=args.output.resolve();out.mkdir(parents=True,exist_ok=True)
    (out/'tables').mkdir(exist_ok=True)
    seen_zip=set();files=[];occ=[];raw={};errors=[];direction_files=[];excluded_fragments=[]
    def inspect(b,path):
        files.append({'path':path,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
        if not (b'"L"' in b or b'"R"' in b or b' L ' in b or b' R ' in b or b'"table"' in b or b'"transitions"' in b or re.search(rb'\[\s*\d+\s*,\s*[01]\s*,\s*[01]\s*,\s*-?1\s*,',b)):return
        direction_files.append(path)
        try:obj=json.loads(b)
        except Exception as e:errors.append({'path':path,'error':str(e)});return
        stack=[('$',obj)]
        while stack:
            ptr,node=stack.pop();data=decode(node)
            if data:
                rows,states,halt=data
                if len(states)<2:
                    excluded_fragments.append({'path':path,'json_pointer':ptr,'states':len(states),'reason':'one-state subtable/redirected-row fragment, not an identified whole-machine artifact'})
                    continue
                txt=''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(rows.items()))
                h=hashlib.sha256(txt.encode()).hexdigest()
                occ.append({'path':path,'json_pointer':ptr,'states':len(states),'sha256':h,'halt':halt})
                if h not in raw:
                    raw[h]=data;(out/'tables'/(h+'.tm')).write_text(txt)
                continue
            if isinstance(node,dict):stack.extend((ptr+'/'+str(k),v) for k,v in node.items() if isinstance(v,(dict,list,str)))
            elif isinstance(node,list):stack.extend((ptr+'/'+str(i),v) for i,v in enumerate(node) if isinstance(v,(dict,list,str)))
    def scan_zip(b,path):
        h=hashlib.sha256(b).hexdigest()
        if h in seen_zip:return
        seen_zip.add(h)
        with zipfile.ZipFile(io.BytesIO(b)) as z:
            for n in z.namelist():
                if n.lower().endswith('.json'):inspect(z.read(n),path+'!'+n)
                elif n.lower().endswith('.zip'):scan_zip(z.read(n),path+'!'+n)
    pa=repo/'Computability/BusyBeaver/Research/PA'
    for p in sorted(pa.rglob('*.json')):inspect(p.read_bytes(),str(p.relative_to(repo)))
    for p in sorted(pa.rglob('*.zip')):scan_zip(p.read_bytes(),str(p.relative_to(repo)))
    for p in sorted((repo/'docs/incoming').glob('*.zip')):scan_zip(p.read_bytes(),str(p.relative_to(repo)))
    identities=[]
    for i,(h,data) in enumerate(raw.items()):
        forms=[c for q in sorted(data[1]) if (c:=lib.canonical(data,q)) is not None]
        canon=min(forms) if forms else None
        gh=hashlib.sha256(repr(canon).encode()).hexdigest() if canon else None
        identities.append({'sha256':h,'states':len(data[1]),'graph_hash':gh})
        print('classified JSON',i+1,len(raw),flush=True)
    result={'scope':__doc__,'json_files_examined':len(files),'json_files_with_possible_table_tokens':len(direction_files),'occurrences':occ,'identities':identities,'errors':errors,'files':files,'direction_files':direction_files,'excluded_fragments':excluded_fragments}
    (out/'census.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('files','direction_files','occurrences','identities')},indent=2))
    print('occurrences',len(occ),'identities',len(raw))
if __name__=='__main__':main()
