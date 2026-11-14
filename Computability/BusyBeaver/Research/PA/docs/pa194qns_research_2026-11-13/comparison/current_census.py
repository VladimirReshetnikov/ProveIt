#!/usr/bin/env python3
"""Literal five-column table inventory for the pinned PA research corpus.

This identifies whole control graphs, not computation semantics. A full
spanning root is required for the symmetry quotient. It compares exact
canonical tuples; SHA-256 digests are only printed identifiers.
"""
from __future__ import annotations
import argparse, csv, hashlib, io, json, re, subprocess, zipfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parent / 'ProveIt'
TEXT_SUFFIXES = {'.tm', '.txt', '.csv', '.tsv'}
ROW = re.compile(r'^(\d+)\s+([01])\s+([01])\s+([LR])\s+(\d+)$')

def parse_table(data):
    try: text=data.decode('ascii')
    except UnicodeDecodeError: return None
    rows={}; declared=None
    for line in text.splitlines():
        line=line.strip()
        if not line: continue
        if line.startswith('#'):
            m=re.search(r'\bstart\s*(\d+)',line)
            if m and declared is None: declared=int(m.group(1))
            continue
        m=ROW.fullmatch(line)
        if not m: return None
        q,b,w,d,t=m.groups(); key=(int(q),int(b))
        if key in rows: return None
        rows[key]=(int(w),d,int(t))
    states={q for q,b in rows}
    if not states or any((q,b) not in rows for q in states for b in (0,1)): return None
    undefined={t for w,d,t in rows.values()}-states
    if len(undefined)>1: return None
    start=declared if declared is not None else (0 if sorted(states)==list(range(len(states))) else None)
    if start is not None and start not in states: return None
    return rows,states,start,undefined

def rooted_tuple(rows,states,start,mirror=False,complement=False):
    idx={start:0}; order=[start]; out=[]
    for q in order:
        for b in (0,1):
            w,d,t=rows[q,b ^ complement]
            w ^= complement
            if mirror: d='L' if d=='R' else 'R'
            if t in states:
                if t not in idx: idx[t]=len(idx);order.append(t)
                out.extend((w,0 if d=='L' else 1,idx[t]))
            else: out.extend((w,0 if d=='L' else 1,-1))
    return tuple(out),len(order)

def canonical(rows,states):
    best=None; roots=0
    for q in states:
        t,n=rooted_tuple(rows,states,q)
        if n!=len(states): continue
        roots+=1
        if best is None or t<best: best=t
        for mirror,complement in ((True,False),(False,True),(True,True)):
            t,_=rooted_tuple(rows,states,q,mirror,complement)
            if t<best: best=t
    return best,roots

def graph_digest(c):
    return hashlib.sha256(json.dumps(c,separators=(',',':')).encode()).hexdigest() if c is not None else None

def collect():
    occurrences=[]; by_sha={}; archives={}; visited=set(); failures=[]
    def visit(data,locator,suffix):
        digest=hashlib.sha256(data).hexdigest()
        if suffix=='.zip':
            archives.setdefault(digest,{'sha256':digest,'locators':[],'size':len(data)})['locators'].append(locator)
            if digest in visited:return
            visited.add(digest)
            try:
                with zipfile.ZipFile(io.BytesIO(data)) as z:
                    for info in z.infolist():
                        ext=Path(info.filename).suffix.lower()
                        if not info.is_dir() and (ext in TEXT_SUFFIXES or ext=='.zip'):
                            visit(z.read(info),locator+'::'+info.filename,ext)
            except Exception as e: failures.append({'path':locator,'error':repr(e)})
            return
        if suffix not in TEXT_SUFFIXES:return
        p=parse_table(data)
        if p is None:return
        rows,states,start,undefined=p
        occurrences.append({'locator':locator,'sha256':digest,'states':len(states),'start':start})
        if digest not in by_sha:
            by_sha[digest]={'sha256':digest,'states':len(states),'rows':len(rows),'start':start,'halt_targets':sorted(undefined),'locators':[],'table':p}
        by_sha[digest]['locators'].append(locator)
    proc=subprocess.run(['rg','--files','-g','*.tm','-g','*.txt','-g','*.csv','-g','*.tsv','-g','*.zip','Computability/BusyBeaver/Research/PA'],cwd=REPO,check=True,capture_output=True,text=True)
    for name in proc.stdout.splitlines():
        p=REPO/name
        visit(p.read_bytes(),name,p.suffix.lower())
    for name in ('PA194NS_research.zip','pa194haz_research_2026-11-14.zip','pa194qn_research_2026-11-13.zip'):
        visit((ROOT/name).read_bytes(),'docs/incoming/'+name,'.zip')
    return occurrences,by_sha,archives,failures

def run_scan():
    occurrences,by_sha,archives,failures=collect()
    rootgroups={}; frontier=[]
    for i,item in enumerate(by_sha.values()):
        rows,states,start,undefined=item.pop('table')
        if len(states)==194:
            c,roots=canonical(rows,states)
            item['whole_graph_sha256']=graph_digest(c);item['spanning_roots']=roots
            if c is not None:
                g=rootgroups.setdefault(c,{'whole_graph_sha256':graph_digest(c),'states':len(states),'byte_sha256':[],'locators':[],'canonical':list(c)})
                g['byte_sha256'].append(item['sha256']);g['locators']+=item['locators']
        if start is not None:
            t,n=rooted_tuple(rows,states,start)
            item['start_reachable']=n
        if len(states)==194:frontier.append(item)
    counts={}
    for item in by_sha.values():
        s=str(item['states']);counts[s]=counts.get(s,0)+1
    out={'commit':'317b07268681b44ff352d173a162e2a8c241b2fe','scope':'Complete numeric five-column binary L/R .tm/.txt/.csv/.tsv tables in all PA tree files and all three incoming archives, recursively including ZIPs; identical ZIP payloads visited once. All complete tables retained, including rejected candidates and fixtures. JSON/code-only definitions are not recognized.','table_occurrences':len(occurrences),'byte_distinct_tables':len(by_sha),'archives_distinct':len(archives),'194_byte_forms':len(frontier),'194_whole_graph_classes_up_to_root_mirror_complement':len(rootgroups),'byte_forms_by_states':counts,'archives':list(archives.values()),'failures':failures,'tables':list(by_sha.values()),'occurrences':occurrences}
    (ROOT/'current_census.json').write_text(json.dumps(out,indent=2)+'\n')
    (ROOT/'current_frontier194.json').write_text(json.dumps(list(rootgroups.values()),indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('archives','tables','occurrences')},indent=2))

def compare(candidate):
    data=Path(candidate).read_bytes();p=parse_table(data)
    if p is None:raise ValueError('Not a complete numeric binary table')
    rows,states,start,undefined=p;c,roots=canonical(rows,states)
    old=json.loads((ROOT/'current_frontier194.json').read_text())
    matches=[{k:v for k,v in x.items() if k!='canonical'} for x in old if tuple(x['canonical'])==c]
    result={'candidate':str(Path(candidate).resolve()),'states':len(states),'rows':len(rows),'start':start,'halt_targets':sorted(undefined),'sha256':hashlib.sha256(data).hexdigest(),'spanning_roots':roots,'whole_graph_sha256':graph_digest(c),'compared_classes':len(old),'matches':matches,'scope':'Exact complete action tuple comparison under state renaming, any spanning root, global L/R reflection, and global symbol complementation; not semantic inequivalence or a consistency proof.'}
    print(json.dumps(result,indent=2))
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('candidate',nargs='?');a=p.parse_args()
    compare(a.candidate) if a.candidate else run_scan()
