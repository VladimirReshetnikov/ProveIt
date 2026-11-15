#!/usr/bin/env python3
"""Read the pinned Git tree, including nested ZIPs and explicit JSON TM encodings.

This is a table inventory, not a halting-equivalence proof. Literal parsers are
adapted unchanged from the attributed PA194 q-radix packet; classification uses
the repository's machine_classes.py definition, with explicit start caveats.
"""
from pathlib import Path
from collections import Counter, defaultdict
from hashlib import sha256
import csv, io, json, re, subprocess, sys, zipfile
import literal_inventory as lit
import json_inventory as js
import machine_classes as mc

HERE = Path(__file__).resolve().parent
REPO = Path(sys.argv[1]) if len(sys.argv)>1 else Path.cwd()/'ProveIt'
REF = sys.argv[2] if len(sys.argv)>2 else '1e1a41f799d4658b829cdd0eabae3775a0c8c4a0'
OUT = HERE/'census'
OUT.mkdir(exist_ok=True)
(OUT/'tables').mkdir(exist_ok=True)
prefixes = ('Computability/BusyBeaver/Research/PA/', 'docs/incoming/')
tree = subprocess.check_output(['git','-C',str(REPO),'ls-tree','-rlz',REF]).split(b'\0')
entries=[]
for line in tree:
    if not line:continue
    meta,path=line.split(b'\t',1)
    mode,kind,oid,size=meta.split(); path=path.decode()
    if kind==b'blob' and path.startswith(prefixes):
        entries.append((path,oid.decode(),int(size)))
batch=subprocess.Popen(['git','-C',str(REPO),'cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
def blob(oid):
    batch.stdin.write((oid+'\n').encode());batch.stdin.flush()
    head=batch.stdout.readline().split()
    if len(head)!=3:raise RuntimeError(head)
    data=batch.stdout.read(int(head[2]));assert batch.stdout.read(1)==b'\n'
    return data

occurrences=[]; normalized={}; files=[]; archives=[]; archive_refs=[]
seen_zip=set(); parsed_json={}; errors=[]; excluded_fragments=0
def add_table(data,path,format_,pointer=None,raw=None):
    rows,states,halt=data
    txt=''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(rows.items()))
    digest=sha256(txt.encode()).hexdigest()
    rec={'path':path,'format':format_,'normalized_sha256':digest,'states':len(states),'halt':halt}
    if pointer is not None:rec['json_pointer']=pointer
    if raw is not None:rec['raw_sha256']=sha256(raw).hexdigest()
    occurrences.append(rec)
    if digest not in normalized:
        normalized[digest]=(data,txt,path)
        if len(states)<=196:(OUT/'tables'/(digest+'.tm')).write_text(txt)

def inspect_json(data,path):
    global excluded_fragments
    h=sha256(data).hexdigest()
    if h in parsed_json:
        for pointer,tm in parsed_json[h]:add_table(tm,path,'json',pointer)
        return
    parsed_json[h]=[]
    # A conservative prefilter, identical in substance to the prior recognizer.
    if not (b'"L"' in data or b'"R"' in data or b' L ' in data or b' R ' in data or
            b'"table"' in data or b'"transitions"' in data or
            re.search(rb'\[\s*\d+\s*,\s*[01]\s*,\s*[01]\s*,\s*-?1\s*,',data)):return
    try:obj=json.loads(data)
    except Exception as e:errors.append({'path':path,'error':str(e)});return
    stack=[('$',obj)]
    while stack:
        pointer,node=stack.pop()
        try:tm=js.decode(node)
        except (ValueError,TypeError,KeyError):tm=None
        if tm:
            if len(tm[1])<2:
                excluded_fragments+=1
                continue
            parsed_json[h].append((pointer,tm));add_table(tm,path,'json',pointer)
            continue
        if isinstance(node,dict):stack.extend((pointer+'/'+str(k),v) for k,v in node.items() if isinstance(v,(dict,list,str)))
        elif isinstance(node,list):stack.extend((pointer+'/'+str(i),v) for i,v in enumerate(node) if isinstance(v,(dict,list,str)))

def inspect(data,path):
    suffix=Path(path).suffix.lower()
    if suffix=='.zip':scan_zip(data,path);return
    files.append({'path':path,'bytes':len(data),'sha256':sha256(data).hexdigest()})
    if suffix=='.json':inspect_json(data,path)
    elif suffix in ('.tm','.txt','.tsv','.csv'):
        table=lit.parse_table(data)
        if table:add_table(table,path,'text',raw=data)

def scan_zip(data,path):
    h=sha256(data).hexdigest();archive_refs.append({'path':path,'sha256':h})
    if h in seen_zip:return
    seen_zip.add(h)
    try:
        with zipfile.ZipFile(io.BytesIO(data)) as z:
            archives.append({'path':path,'sha256':h,'bytes':len(data),'members':len(z.infolist())})
            for info in z.infolist():
                if not info.is_dir() and Path(info.filename).suffix.lower() in ('.zip','.tm','.txt','.tsv','.csv','.json'):
                    inspect(z.read(info),path+'!'+info.filename)
    except Exception as e:errors.append({'path':path,'error':str(e)})

for i,(path,oid,size) in enumerate(entries):
    if Path(path).suffix.lower() in ('.zip','.tm','.txt','.tsv','.csv','.json'):
        inspect(blob(oid),path)
    if i%5000==0:print('scanned',i,len(entries),'recognized',len(occurrences),flush=True)
batch.stdin.close();batch.wait()
print('classifying',len(normalized),'normalized tables',flush=True)
def has_spanning_root(data):
    rows,states,halt=data
    def visit(q,seen):
        todo=[q]
        while todo:
            v=todo.pop()
            if v in seen:continue
            seen.add(v)
            todo.extend(t for b in (0,1) if (t:=rows[v,b][2]) in states and t not in seen)
    seen=set();last=None
    for q in sorted(states):
        if q not in seen:last=q;visit(q,seen)
    check=set();visit(last,check)
    return len(check)==len(states)
identities=[]; groups=defaultdict(list)
for i,(h,(data,txt,path)) in enumerate(normalized.items()):
    c=mc.classify(txt.encode())
    rec={'normalized_sha256':h,'states':len(data[1]),'table_class':c['table'],
         'graph_root_reachability':c['reachable'],'start_by_dense_convention':c['start'],
         'first_path':path,'raw_rooted_class':c.get('machine'),
         'has_spanning_root':has_spanning_root(data)}
    # Literal inventory's exact root-free canonical tuples give a second,
    # independently represented identity for the 193/194 frontier.
    if 193<=len(data[1])<=194:
        forms=[v for q in sorted(data[1]) if (v:=lit.canonical(data,q)) is not None]
        if forms:
            rec['root_free_canonical_sha256']=sha256(repr(min(forms)).encode()).hexdigest()
            for reflect,complement in ((True,False),(False,True),(True,True)):
                forms.extend(v for q in sorted(data[1]) if (v:=lit.canonical(data,q,reflect,complement)) is not None)
            rec['cosmetic_class']=sha256(repr(min(forms)).encode()).hexdigest()
    identities.append(rec);groups[c['table']].append(rec)
    if i%100==0:print('classified',i+1,len(normalized),flush=True)

official=list(csv.DictReader((HERE/'official_MACHINES.tsv').open(),delimiter='\t'))
official_by={r['table_class']:r for r in official}
classes=[]
for table_class,rs in groups.items():
    hashes={r['normalized_sha256'] for r in rs}
    os=[o for o in occurrences if o['normalized_sha256'] in hashes]
    n=rs[0]['states']
    item={'table_class':table_class,'states':n,'normalized_sha256s':sorted(hashes),
          'occurrences':os,'representative':min(rs,key=lambda r:r['first_path']),
          'has_spanning_root':any(r['has_spanning_root'] for r in rs),
          'status':'table inventory; correctness not inferred'}
    if table_class in official_by:item['official_catalogue']=official_by[table_class]
    if rs[0].get('cosmetic_class'):item['cosmetic_class']=rs[0]['cosmetic_class']
    classes.append(item)
classes.sort(key=lambda c:(c['states'],c['table_class']))
summary={'commit':REF,'file_paths_scanned':len(entries),'recognized_occurrences':len(occurrences),
         'text_occurrences':sum(o['format']=='text' for o in occurrences),
         'json_occurrences':sum(o['format']=='json' for o in occurrences),
         'normalized_tables':len(normalized),'table_classes':len(groups),
         'classes_by_state_count':dict(sorted(Counter(c['states'] for c in classes).items())),
         'spanning_graph_classes':sum(c['has_spanning_root'] for c in classes),
         'spanning_by_state_count':dict(sorted(Counter(c['states'] for c in classes if c['has_spanning_root']).items())),
         'distinct_archive_payloads':len(archives),'archive_references':len(archive_refs),
         'official_catalogue_classes':len(official),'official_classes_found':sum(c['table_class'] in official_by for c in classes),
         'unmatched_official_classes':[r for r in official if r['table_class'] not in groups],
         'excluded_json_single_state_fragments':excluded_fragments,'errors':errors}
exclusions=[]
for r in summary['unmatched_official_classes']:
    b=subprocess.check_output(['git','-C',str(REPO),'show',REF+':'+r['kept_file']])
    rows,states,start,declared=mc.parse(b)
    halts=sorted({a[2] for a in rows.values()}-states)
    reason='no external terminal' if not halts else 'multiple external terminal labels' if len(halts)>1 else 'OTHER'
    exclusions.append({'official_class':r['class'],'official_reachable_states':int(r['states']),
       'working_labels':len(states),'external_terminal_labels':halts,
       'maximum_reachable_working_states':max(mc.rooted(rows,states,q)[1] for q in states),
       'source':r['kept_file'],'reason':reason})
exclusion_summary={'excluded_official_classes':len(exclusions),'reasons':dict(Counter(r['reason'] for r in exclusions)),
       'official194_classes':sum(r['states']=='194' for r in official),
       'official194_classes_matched':sum(r['states']=='194' and r['table_class'] in groups for r in official),
       'rows':exclusions}
(OUT/'excluded_official.json').write_text(json.dumps(exclusion_summary,indent=2)+'\n')
spanning_summary={'examined_component_classes':len(classes),'spanning_graph_classes':summary['spanning_graph_classes'],
       'spanning_by_state_count':summary['spanning_by_state_count'],
       'nonspanning_component_classes':[{'states':c['states'],'table_class':c['table_class'],'path':c['representative']['first_path']} for c in classes if not c['has_spanning_root']]}
(OUT/'spanning_summary.json').write_text(json.dumps(spanning_summary,indent=2)+'\n')
result={'summary':summary,'scope':__doc__,'archives':archives,'archive_references':archive_refs,
        'files':files,'identities':identities,'classes':classes}
(OUT/'census.json').write_text(json.dumps(result,indent=2)+'\n')
(OUT/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
for n in (193,194):
    selected=[c for c in classes if c['states']==n]
    (OUT/f'frontier{n}.json').write_text(json.dumps(selected,indent=2)+'\n')
    with (OUT/f'frontier{n}.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=['table_class','cosmetic_class','states','normalized_sha256','representative_path','occurrences','official_first_packet'])
        writer.writeheader()
        for c in selected:
            writer.writerow({'table_class':c['table_class'],'cosmetic_class':c.get('cosmetic_class',''),
              'states':n,'normalized_sha256':c['representative']['normalized_sha256'],
              'representative_path':c['representative']['first_path'],'occurrences':len(c['occurrences']),
              'official_first_packet':c.get('official_catalogue',{}).get('first_packet','')})
print(json.dumps(summary,indent=2),flush=True)
