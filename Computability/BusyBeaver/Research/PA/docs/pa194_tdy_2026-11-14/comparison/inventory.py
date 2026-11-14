#!/usr/bin/env python3
"""Reproducible census of the filed catalogue and incoming numeric TM tables.

No computation in this file proves consistency calibration. Machine starts inferred
from dense numbering are explicitly marked as conventions. Structural comparisons
include all states only when a spanning root exists. Disconnected diagnostics are
counted separately and never merged by a partial reachable-subgraph fingerprint.
"""
import argparse, collections, csv, hashlib, io, json, pathlib, re, zipfile

EXT={".tm",".txt",".tsv",".csv"}
def digest(data): return hashlib.sha256(data).hexdigest()
def parse(data):
    try: text=data.decode("ascii")
    except UnicodeDecodeError: return None
    rows={}; declared=None
    for line in text.splitlines():
        s=line.strip()
        if not s: continue
        if s.startswith("#"):
            m=re.search(r"\bstart\s*(\d+)",s)
            if m and declared is None: declared=int(m[1])
            continue
        t=s.split()
        if len(t)!=5: return None
        try:q,b,w,n=int(t[0]),int(t[1]),int(t[2]),int(t[4])
        except ValueError:return None
        d=t[3]
        if b not in (0,1) or w not in (0,1) or d not in ("L","R") or (q,b) in rows:return None
        rows[q,b]=(w,d,n)
    st=set(q for q,b in rows)
    if not st or any((q,b) not in rows for q in st for b in (0,1)):return None
    start=declared if declared is not None else (0 if sorted(st)==list(range(len(st))) else None)
    if start is not None and start not in st:return None
    return rows,st,start,declared

def rooted(m,q,mirror=False,flip=False,loose=False):
    rows,st,_,_=m;order=[q];ix={q:0};out=[]
    for q in order:
        for b in (0,1):
            w,d,n=rows[q,b^flip]
            if flip:w^=1
            if mirror:d="L" if d=="R" else "R"
            if n in st:
                if n not in ix:ix[n]=len(order);order.append(n)
                out.append((w,d,ix[n]))
            else:out.append((0,"R",-1) if loose else (w,d,-1))
    return len(order),json.dumps(out,separators=(",",":"))

def canonical(m,extended=False,loose=False):
    most=0;best=None
    opts=[(False,False),(True,False),(False,True),(True,True)] if extended else [(False,False)]
    for q in m[1]:
        n,s=rooted(m,q)
        if n<len(m[1]):continue
        for mirror,flip in opts:
            n,s=rooted(m,q,mirror,flip,loose)
            if best is None or s<best:best=s
    return best

def write_csv(path,rows,fields):
    with path.open("w",newline="") as f:
        w=csv.DictWriter(f,fieldnames=fields,extrasaction="ignore");w.writeheader();w.writerows(rows)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--input",type=pathlib.Path,default=pathlib.Path(__file__).resolve().parent/"source_census")
    ap.add_argument("--incoming",type=pathlib.Path)
    ap.add_argument("--repo",type=pathlib.Path)
    ap.add_argument("--corpus",type=pathlib.Path,help="replay frozen recognized-table bytes instead of rereading source archives")
    ap.add_argument("--candidate",type=pathlib.Path,required=True)
    ap.add_argument("--output",type=pathlib.Path,default=pathlib.Path(__file__).resolve().parent)
    a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=True)
    tables={};stats=collections.Counter();archives={};failures=[];packets=[]
    def consume(data,path):
        ext=pathlib.PurePosixPath(path).suffix.lower()
        if ext==".zip":
            h=digest(data);stats["archive_references"]+=1
            if h in archives:archives[h]["paths"].append(path);return
            archives[h]={"paths":[path],"bytes":len(data)}
            try:
                with zipfile.ZipFile(io.BytesIO(data)) as z:
                    names=[n for n in z.infolist() if not n.is_dir()]
                    archives[h]["members"]=len(names)
                    for n in names:consume(z.read(n),path+"!"+n.filename)
            except Exception as e:failures.append({"path":path,"error":str(e)})
            return
        if ext not in EXT:return
        m=parse(data)
        if m is None:return
        stats["recognized_table_occurrences"]+=1;h=digest(data)
        if h not in tables:tables[h]={"data":data,"parsed":m,"paths":[]}
        tables[h]["paths"].append(path)
    if a.corpus:
        for r in json.loads(a.corpus.read_text()):
            data=r["text"].encode("ascii")
            assert digest(data)==r["sha256"]
            for path in r["paths"]:consume(data,path)
    else:
        for f in sorted(a.input.glob("filed_tables_*.json")):
            for r in json.loads(f.read_text()):
                consume(r["text"].encode(),r["record"]["kept_file"])
    if a.incoming:
        for f in sorted(a.incoming.rglob("*.zip")):
            consume(f.read_bytes(),"docs/incoming/"+str(f.relative_to(a.incoming)))
    if a.repo:
        root=a.repo/"Computability/BusyBeaver/Research/PA"
        for f in sorted(root.rglob("*")):
            if f.is_file() and f.suffix.lower() in EXT|{".zip"}:
                consume(f.read_bytes(),str(f.relative_to(a.repo)))
    candidate=parse(a.candidate.read_bytes())
    if candidate is None:raise ValueError("candidate not complete numeric binary table")
    candidate_key=canonical(candidate,True,True)
    assert candidate_key is not None
    records=[];groups=collections.defaultdict(list);extended_cache={};matched=[]
    for i,(h,t) in enumerate(tables.items()):
        m=t["parsed"];key=canonical(m);spanning=key is not None
        n=len(m[1]);extkey=None
        if n==len(candidate[1]) and spanning:
            extkey=canonical(m,True,True)
            if extkey==candidate_key:matched.extend(t["paths"])
        rec={"sha256":h,"states":n,"transition_rows":len(m[0]),"spanning_root":spanning,
             "external_target_count":len({target for _,_,target in m[0].values()}-m[1]),
             "external_targets":sorted({target for _,_,target in m[0].values()}-m[1]),
             "start":m[2],"start_status":"declared" if m[3] is not None else ("dense_convention" if m[2] is not None else "unknown"),
             "canonical_sha256":digest(key.encode()) if key is not None else None,
             "occurrences":len(t["paths"]),"paths":t["paths"],"sample_path":t["paths"][0]}
        records.append(rec);groups[key if key is not None else "disconnected:"+h].append(rec)
        if i%100==0:print(f"classified {i} / {len(tables)}",flush=True)
    cls=[]
    for key,rs in groups.items():
        rep=rs[0];cls.append({**{k:v for k,v in rep.items() if k not in ("occurrences","paths")},
            "byte_forms":len(rs),"occurrences":sum(r["occurrences"] for r in rs),
            "external_target_counts":sorted(set(r["external_target_count"] for r in rs)),
            "paths":sorted(set(p for r in rs for p in r["paths"]))})
    cls.sort(key=lambda r:(r["states"],r["canonical_sha256"] or r["sha256"]))
    summary={
        "snapshot":"4be5c6e3a10292a7466f5d3687e3b39615ff049b",
        "counts":{**dict(stats),"distinct_table_bytes":len(tables),"spanning_table_classes":sum(r["spanning_root"] for r in cls),"disconnected_byte_forms":sum(not r["spanning_root"] for r in cls)},
        "spanning_classes_by_states":dict(sorted(collections.Counter(r["states"] for r in cls if r["spanning_root"]).items())),
        "candidate_sha256":digest(a.candidate.read_bytes()),"candidate_states":len(candidate[1]),
        "candidate_canonical_sha256":digest(candidate_key.encode()),"candidate_matches":matched,
        "comparison_symmetries":["all spanning roots","working-state renaming","left/right reflection","global bit exchange","ignore final halt-edge write and move"],
        "failures":failures,
        "scope":"535 filed catalogue representative tables plus recursively scanned provided archives and local PA files. Parser: complete numeric five-column binary .tm/.txt/.tsv/.csv; arbitrary code-only and JSON-only encodings excluded unless supplied as literal tables. Candidate comparison uses full canonical tuple equality, hashes only identify results. No historical consistency calibration or runtime proof is inferred from this census.",
    }
    for name,obj in [("literal_tables.json",records),("literal_classes.json",cls),("archives.json",archives),("census_summary.json",summary)]:
        (a.output/name).write_text(json.dumps(obj,indent=2)+"\n")
    (a.output/"corpus_tables.json").write_text(json.dumps([
        {"sha256":h,"text":t["data"].decode("ascii"),"paths":t["paths"]}
        for h,t in tables.items()],separators=(",",":"))+"\n")
    write_csv(a.output/"literal_classes.csv",cls,["states","canonical_sha256","spanning_root","byte_forms","occurrences","start","start_status","sample_path"])
    print(json.dumps(summary,indent=2))
if __name__=="__main__":main()

