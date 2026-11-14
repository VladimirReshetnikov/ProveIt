#!/usr/bin/env python3
"""Read-only census of submitted binary TM tables, including nested ZIPs.

No submitted code is executed. A table is not classified as a successful
consistency construction merely because its transition rows are well formed.
"""
from __future__ import annotations
import argparse, collections, csv, hashlib, io, json, re, zipfile
from pathlib import Path

PIN = "906367250a7f96c923147b10df392294bced7be5"

def digest(data):
    return hashlib.sha256(data).hexdigest()

def parse_table(data):
    text=data.decode("utf-8-sig")
    rows={}; starts=[]; ignored=[]
    for line_no, original in enumerate(text.splitlines(),1):
        line=original.strip()
        if not line: continue
        if line.startswith(("#","//",";")):
            m=re.search(r"\bstart(?:_state)?\s*(?:[:=]|is)?\s*(\d+)",line,re.I)
            if m: starts.append(int(m[1]))
            continue
        line=line.split("#",1)[0].strip()
        t=line.split()
        if len(t)!=5: raise ValueError(f"line {line_no}: not five columns")
        q,b,w,d,n=t
        q,b,w,n=map(int,(q,b,w,n))
        if b not in (0,1) or w not in (0,1) or d not in ("L","R") or (q,b) in rows:
            raise ValueError(f"line {line_no}: invalid or repeated transition")
        rows[q,b]=(w,d,n)
    if not rows: raise ValueError("no transition rows")
    states={q for q,b in rows}; targets={n for w,d,n in rows.values()}
    halts=sorted(targets-states)
    complete=set(rows)=={(q,b) for q in states for b in (0,1)}
    transitions=[[q,b,*rows[q,b]] for q,b in sorted(rows)]
    # A structural hash preserves literal labels. Rooted isomorphism below is
    # used only for independently designated machines, not guessed native starts.
    result={"working_states":len(states),"rows":len(rows),"complete":complete,
            "terminal_labels":halts,"minimum_state":min(states),"maximum_state":max(states),
            "declared_starts":starts,"dense_working_labels":states==set(range(len(states))),
            "transition_sha256":digest(json.dumps(transitions,separators=(",",":")).encode())}
    return result, rows

def canonical_root(rows,start):
    states={q for q,b in rows}
    if start not in states: raise ValueError("start is not a working state")
    order=[start]; ix={start:0}; canon=[]
    for q in order:
        for b in (0,1):
            w,d,n=rows[q,b]
            if n in states and n not in ix: ix[n]=len(ix); order.append(n)
            canon.append((w,d,ix[n] if n in states else -1))
    return {"start":start,"reachable_working_states":len(order),
            "rooted_graph_sha256":digest(json.dumps(canon,separators=(",",":")).encode())}

def main():
    ap=argparse.ArgumentParser();ap.add_argument("repository",type=Path);ap.add_argument("output",type=Path)
    a=ap.parse_args(); a.output.mkdir(parents=True,exist_ok=True)
    (a.output/"tables_by_raw_hash").mkdir(exist_ok=True)
    (a.output/"reports").mkdir(exist_ok=True)
    archives={}; archive_aliases=[]; tables=[]; errors=[]; reports=[]
    def addtable(data,source,member,archive_sha=None):
        raw=digest(data)
        record={"source":source,"member":member,"archive_sha256":archive_sha,"raw_sha256":raw,"bytes":len(data)}
        try:
            p,rows=parse_table(data);record.update(p)
            # Header is evidence of the start. Dense-label convention is not
            # silently imposed: a separate curated census supplies its starts.
            if len(set(p["declared_starts"]))==1:record.update(canonical_root(rows,p["declared_starts"][0]))
            target=a.output/"tables_by_raw_hash"/(raw+".tm")
            if not target.exists(): target.write_bytes(data)
        except Exception as e:
            record["parse_error"]=str(e);errors.append(record)
        tables.append(record)
    def walkzip(data,location,depth):
        raw=digest(data)
        archive_aliases.append({"location":location,"sha256":raw,"depth":depth})
        if raw in archives: return
        if depth>30: raise ValueError("nested archive depth exceeds 30")
        z=zipfile.ZipFile(io.BytesIO(data))
        record={"first_location":location,"sha256":raw,"bytes":len(data),"depth":depth,"members":len(z.infolist()),"tm_members":0,"nested_zip_members":0}
        archives[raw]=record
        for info in z.infolist():
            name=info.filename
            if info.is_dir():continue
            suffix=Path(name).suffix.lower()
            if suffix==".tm":
                record["tm_members"]+=1;addtable(z.read(info),location,name,raw)
            elif suffix==".zip":
                record["nested_zip_members"]+=1;walkzip(z.read(info),location+"!"+name,depth+1)
            elif depth==0 and (suffix==".tex" or Path(name).name.lower().startswith("readme")) and len(Path(name).parts)<=4:
                payload=z.read(info);ph=digest(payload)
                target=a.output/"reports"/(Path(location).name.replace(" ","_").replace(".zip","")+"__"+name.replace("/","__"))
                target.write_bytes(payload)
                reports.append({"source":location,"member":name,"sha256":ph,"local_path":str(target)})
    incoming=a.repository/"docs/incoming"
    for p in sorted(incoming.glob("*.zip")):
        walkzip(p.read_bytes(),str(p.relative_to(a.repository)),0)
    pa=a.repository/"Computability/BusyBeaver/Research/PA"
    for p in sorted(pa.rglob("*.tm")):
        if any(x in p.parts for x in (".git",".lake")): continue
        addtable(p.read_bytes(),"repository",str(p.relative_to(a.repository)))
    out={"commit":PIN,"scope":"Every .tm member of every top-level incoming ZIP, recursively, with repeated ZIP payloads scanned once; all .tm files under Research/PA. Table census includes experiments, controls and rejected constructions.",
         "top_level_archives":len(list(incoming.glob("*.zip"))),"distinct_archive_payloads":len(archives),"archive_occurrences":len(archive_aliases),"maximum_nesting_depth":max(x["depth"] for x in archive_aliases),
         "all_table_occurrences":len(tables),"archive_table_occurrences":sum(x["archive_sha256"] is not None for x in tables),"repository_table_occurrences":sum(x["archive_sha256"] is None for x in tables),
         "raw_distinct_tables":len({x["raw_sha256"] for x in tables}),"transition_distinct_tables":len({x["transition_sha256"] for x in tables if "transition_sha256" in x}),"parse_errors":len(errors),
         "working_state_histogram_occurrences":dict(sorted(collections.Counter(x["working_states"] for x in tables if "working_states" in x).items())),
         "working_state_histogram_unique_transitions":dict(sorted(collections.Counter(x["working_states"] for x in {x["transition_sha256"]:x for x in tables if "transition_sha256" in x}.values()).items()))}
    for name,value in [("summary",out),("archives",list(archives.values())),("archive_occurrences",archive_aliases),("tables",tables),("parse_errors",errors),("report_members",reports)]:
        (a.output/(name+".json")).write_text(json.dumps(value,indent=2,sort_keys=True)+"\n")
    with (a.output/"tables.csv").open("w",newline="") as f:
        fields=["source","member","raw_sha256","transition_sha256","working_states","rows","complete","terminal_labels","declared_starts","dense_working_labels","archive_sha256"]
        w=csv.DictWriter(f,fieldnames=fields,extrasaction="ignore");w.writeheader();w.writerows(tables)
    print(json.dumps(out,indent=2))

if __name__=="__main__": main()
