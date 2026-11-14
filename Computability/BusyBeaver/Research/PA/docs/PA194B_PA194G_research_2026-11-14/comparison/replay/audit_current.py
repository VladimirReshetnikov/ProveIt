#!/usr/bin/env python3
"""Pinned literal/JSON table census. Recognition is not machine correctness.

Uses the attributed literal/JSON recognizers from the PA194 Q-radix packet.
Reads tracked PA files and every incoming ZIP, including nested payloads.
Does not execute generators or infer semantics from a graph class.
"""
from pathlib import Path
import argparse, collections, hashlib, io, json, re, subprocess, sys, zipfile
import literal_inventory as lit
import json_inventory as js

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--repo',type=Path,required=True)
parser.add_argument('--output',type=Path,default=Path.cwd()/'census-replay')
arguments=parser.parse_args()
REPO=arguments.repo.resolve()
OUT=arguments.output.resolve()
OUT.mkdir(parents=True,exist_ok=True)
(OUT/'frontier_tables').mkdir(exist_ok=True)
PIN='4be5c6e3a10292a7466f5d3687e3b39615ff049b'
assert subprocess.check_output(['git','-C',str(REPO),'rev-parse','HEAD'],text=True).strip()==PIN
occurrences=[]; tables={}; byte_forms={}; archive_refs=[]; archive_contents=[]
seen_archive=set(); inspected_files=[]; errors=[]; fragments=[]

def sha(b): return hashlib.sha256(b).hexdigest()
def add(data,path,raw,pointer=None):
    rows,states,halt=data
    normalized=''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(rows.items())).encode()
    h=sha(normalized)
    declared=None
    if pointer is None:
        m=re.search(rb'(?m)^\s*#.*?\bstart\s*(\d+)',raw)
        if m:declared=int(m.group(1))
    conventional=0 if states==set(range(len(states))) else None
    occurrences.append(dict(path=path,json_pointer=pointer,states=len(states),halt=halt,
        normalized_sha256=h,raw_sha256=sha(raw),declared_start=declared,
        conventional_dense_start=conventional))
    byte_forms[sha(raw)]=len(raw)
    if h not in tables:tables[h]=dict(data=data,raw=normalized,first_path=path,json_pointer=pointer)

def inspect_json(raw,path):
    if not (b'"L"' in raw or b'"R"' in raw or b' L ' in raw or b' R ' in raw or
        b'"table"' in raw or b'"transitions"' in raw or
        re.search(rb'\[\s*\d+\s*,\s*[01]\s*,\s*[01]\s*,\s*-?1\s*,',raw)):
        return
    try:obj=json.loads(raw)
    except Exception as e:errors.append(dict(path=path,error=str(e)));return
    todo=[('$',obj)]
    while todo:
        ptr,node=todo.pop(); data=js.decode(node)
        if data:
            if len(data[1])<2:
                fragments.append(dict(path=path,pointer=ptr,states=len(data[1])));continue
            add(data,path,raw,ptr);continue
        if isinstance(node,dict):todo.extend((ptr+'/'+str(k),v) for k,v in node.items() if isinstance(v,(dict,list,str)))
        elif isinstance(node,list):todo.extend((ptr+'/'+str(i),v) for i,v in enumerate(node) if isinstance(v,(dict,list,str)))

def inspect(raw,path,ext):
    inspected_files.append(dict(path=path,bytes=len(raw),sha256=sha(raw)))
    if ext=='.json':inspect_json(raw,path)
    else:
        data=lit.parse_table(raw)
        if data:add(data,path,raw)

def archive(raw,path,depth=0):
    h=sha(raw);archive_refs.append(dict(path=path,sha256=h,depth=depth))
    if h in seen_archive:return
    seen_archive.add(h)
    try:
        with zipfile.ZipFile(io.BytesIO(raw)) as z:
            archive_contents.append(dict(path=path,sha256=h,bytes=len(raw),members=len(z.infolist())))
            for member in z.infolist():
                if member.is_dir():continue
                ext=Path(member.filename).suffix.lower();p=path+'!'+member.filename
                if ext=='.zip':archive(z.read(member),p,depth+1)
                elif ext in ('.tm','.txt','.csv','.tsv','.json'):inspect(z.read(member),p,ext)
    except Exception as e:errors.append(dict(path=path,error=str(e)))

tree=subprocess.check_output(['git','-C',str(REPO),'ls-tree','-rz',PIN,
    'Computability/BusyBeaver/Research/PA','docs/incoming'])
tracked=[]
for entry in tree.split(b'\0'):
    if not entry:continue
    meta,name=entry.split(b'\t');mode,kind,obj=meta.decode().split();name=name.decode()
    if kind!='blob':continue
    ext=Path(name).suffix.lower()
    if ext not in ('.tm','.txt','.csv','.tsv','.json','.zip'):continue
    p=REPO/name
    raw=p.read_bytes() if p.is_file() else subprocess.check_output(['git','-C',str(REPO),'show',PIN+':'+name])
    if hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()!=obj:
        raw=subprocess.check_output(['git','-C',str(REPO),'show',PIN+':'+name])
    assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==obj,name
    tracked.append(dict(path=name,git_blob_sha1=obj,bytes=len(raw),sha256=sha(raw)))
    if ext=='.zip':archive(raw,name)
    else:inspect(raw,name,ext)
print('scanned',len(tracked),'tracked files;',len(occurrences),'table occurrences;',len(tables),'normalized identities',flush=True)

identities=[]; classes=collections.defaultdict(list)
for i,(h,t) in enumerate(tables.items()):
    data=t['data'];rows,states,halt=data
    forms=[c for q in sorted(states) if (c:=lit.canonical(data,q)) is not None]
    canonical=min(forms) if forms else None
    graph=sha(repr(canonical).encode()) if canonical else None
    cosmetic=graph
    if len(states)==194 and canonical:
        for refl,comp in ((True,False),(False,True),(True,True)):
            forms.extend(c for q in sorted(states) if (c:=lit.canonical(data,q,refl,comp)) is not None)
        cosmetic=sha(repr(min(forms)).encode())
    item=dict(normalized_sha256=h,states=len(states),halt=halt,graph_hash=graph,
        cosmetic_hash=cosmetic,first_path=t['first_path'],json_pointer=t['json_pointer'])
    identities.append(item)
    if graph:
        classes[len(states),graph].append(h)
        if 193<=len(states)<=196:
            (OUT/'frontier_tables'/(graph+'.tm')).write_bytes(t['raw'])
    if i%100==0:print('classified',i+1,'/',len(tables),flush=True)

records=[]
for (n,g),hs in classes.items():
    o=[x for x in occurrences if x['normalized_sha256'] in hs]
    records.append(dict(states=n,graph_hash=g,normalized_identities=hs,occurrences=o))
summary=dict(snapshot=PIN,tracked_files_verified=len(tracked),file_payloads_inspected=len(inspected_files),
    top_level_incoming_archives=sum(x['path'].startswith('docs/incoming/') for x in archive_refs if x['depth']==0),
    distinct_archive_payloads=len(archive_contents),archive_references=len(archive_refs),
    table_occurrences=len(occurrences),normalized_table_identities=len(tables),
    graph_classes=len(records),no_spanning_root_identities=sum(x['graph_hash'] is None for x in identities),
    graph_classes_by_state_count=dict(sorted(collections.Counter(x['states'] for x in records).items())),
    excluded_json_fragments=len(fragments),errors=errors)
result=dict(summary=summary,scope=__doc__,identities=identities,classes=records,
    occurrences=occurrences,archives=archive_contents,archive_references=archive_refs,
    tracked_files=tracked,excluded_json_fragments=fragments)
(OUT/'census.json').write_text(json.dumps(result,indent=2)+'\n')
(OUT/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2),flush=True)
