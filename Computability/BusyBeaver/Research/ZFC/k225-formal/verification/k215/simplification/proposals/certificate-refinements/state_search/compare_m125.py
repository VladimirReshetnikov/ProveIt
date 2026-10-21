#!/usr/bin/env python3
"""Compare the literal M125 patch against checked-out TM files and ZIP members."""
from pathlib import Path
import argparse,hashlib,json,re,zipfile,subprocess

def parse(data):
    if len(data)>2000000:raise ValueError('too large')
    text=data.decode('utf-8');T={};start=None
    for l in text.splitlines():
        m=re.fullmatch(r'#!\s*start\s+(\d+)\s*',l)
        if m:start=int(m[1])
        if not l.strip() or l.lstrip().startswith('#'):continue
        q,b,w,d,z=l.split()
        if d not in ('L','R'):raise ValueError('direction')
        q,b,w,z=map(int,(q,b,w,z))
        if b not in (0,1)or w not in (0,1)or(q,b)in T:raise ValueError('row')
        T[q,b]=(w,-1 if d=='L'else 1,z)
    Q={q for q,b in T};halt={z for w,d,z in T.values()}-Q
    if len(Q)!=215 or len(T)!=430 or len(halt)!=1:raise ValueError('not a complete 215-state table')
    if start is None:start=0;explicit=False
    else:explicit=True
    if start not in Q:raise ValueError('invalid start')
    if any((q,b)not in T for q in Q for b in(0,1)):raise ValueError('incomplete')
    return T,start,next(iter(halt)),explicit

def iso(A,B,reflect):
    X,sx,hx,_=A;Y,sy,hy,_=B;f={sx:sy,hx:hy};rev={sy:sx,hy:hx};todo=[sx];visited=set()
    for x in todo:
        if x in visited:continue
        visited.add(x);y=f[x]
        if x==hx:
            if y!=hy:return False
            continue
        if y==hy:return False
        for b in(0,1):
            a=X[x,b];c=Y[y,b]
            if a[:2]!=(c[0],c[1]*reflect):return False
            x1,y1=a[2],c[2]
            if (x1 in f and f[x1]!=y1)or(y1 in rev and rev[y1]!=x1):return False
            if x1 not in f:f[x1]=y1;rev[y1]=x1
            if x1!=hx and x1 not in visited:todo.append(x1)
    return len(visited)==215 and len(f)==216

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    bp=a.repo/'Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.native.tm';base=parse(bp.read_bytes());T=dict(base[0])
    T.update({(110,0):(0,1,124),(124,0):(0,-1,127),(127,0):(0,1,8),(127,1):(1,1,125)})
    target=(T,*base[1:]);matches=[];count=0;valid=0;explicit=0;unique=set();unknown=[]
    def check(name,data):
        nonlocal count,valid,explicit
        count+=1
        try:p=parse(data)
        except (ValueError,UnicodeDecodeError):return
        valid+=1;explicit+=p[3];unique.add(hashlib.sha256(data).hexdigest())
        if not p[3]:unknown.append(name)
        for sign in(1,-1):
            if iso(target,p,sign):matches.append({'path':name,'reflection':sign==-1,'explicit_start':p[3],'sha256':hashlib.sha256(data).hexdigest()})
    for p in sorted(a.repo.rglob('*.tm')):check(str(p.relative_to(a.repo)),p.read_bytes())
    archives=sorted((a.repo/'docs/incoming').glob('*.zip'));zipmembers=0
    for p in archives:
        with zipfile.ZipFile(p)as z:
            for n in z.infolist():
                if n.filename.endswith('.tm') and n.file_size<2000000:
                    check(str(p.relative_to(a.repo))+'::'+n.filename,z.read(n));zipmembers+=1
    tracked=[x.decode()for x in subprocess.check_output(['git','ls-tree','-r','--name-only','-z','HEAD'],cwd=a.repo).split(b'\0')if x.endswith(b'.tm')]
    missing=[x for x in tracked if not(a.repo/x).exists()]
    report={'status':'MATCH_FOUND'if matches else'NO_ROOTED_ISOMORPHIC_MATCH_IN_INSPECTED_CORPUS','repository_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=a.repo,text=True).strip(),'tracked_tm_paths_total':len(tracked),'missing_tracked_tm_paths':missing,'baseline_sha256':hashlib.sha256(bp.read_bytes()).hexdigest(),'patch':[[q,b,w,d,z]for(q,b),(w,d,z)in sorted(T.items())if base[0][q,b]!=(w,d,z)],'tm_entries_examined':count,'zip_archives_examined':len(archives),'zip_tm_members_examined':zipmembers,'complete_215_tables':valid,'unique_215_byte_strings':len(unique),'tables_with_explicit_start':explicit,'startless_files_assumed_zero':unknown,'matches':matches,'scope':'All physically checked-out .tm files and direct .tm members of docs/incoming ZIPs. Tracked path coverage is recorded explicitly. Only numeric complete 215-state tables enter comparison. Rooted state bijections preserve read/write labels and allow one global direction reflection. No new mathematical idea or global novelty claim follows.'}
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items()if k!='startless_files_assumed_zero'},indent=2))
if __name__=='__main__':main()
