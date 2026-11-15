#!/usr/bin/env python3
"""Rebuild a pinned PA-machine census from a Git checkout or materialized snapshot.

Scope: all complete numeric binary one-halt tables in .tm/.txt/.tsv/.csv
and supported explicit JSON encodings under Research/PA and docs/incoming,
recursively inside ZIP payloads. Archives are scanned once per byte identity;
all archive references are logged. Generators and prose-only tables are not
executed/extracted. A table census is not a correctness proof.

State labels and the start state are forgotten only for table classification.
The start and blank symbol must be recovered separately for semantic claims.
"""
from pathlib import Path
from io import BytesIO
from zipfile import ZipFile
import argparse, collections, csv, hashlib, importlib.util, json, re, subprocess

HERE=Path(__file__).resolve().parent
SUFFIXES={'.tm','.txt','.tsv','.csv','.json','.zip'}
SCOPES=('Computability/BusyBeaver/Research/PA/','docs/incoming/')

def module(name,path):
    s=importlib.util.spec_from_file_location(name,path)
    m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
ji=module('json_inventory',HERE/'vendor/json_inventory.py')
mc=module('machine_classes',HERE/'vendor/machine_classes.py')

def normalized_text(data):
    rows,states,halt=data
    return ''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(rows.items()))

def full_tuple(data,root,reflect=False,complement=False,loose=False):
    rows,states,halt=data;ids={root:0};todo=[root];out=[]
    for q in todo:
        for b in (0,1):
            w,d,t=rows[q,b^complement]
            w^=complement
            if reflect:d='R' if d=='L' else 'L'
            if t in states:
                if t not in ids:ids[t]=len(ids);todo.append(t)
                k=ids[t]
            else:
                k=-1
                if loose:w,d=0,'R'
            out.append((w,d,k))
    return tuple(out),len(todo)

def manifest_inputs(repo,path):
    if path is None:
        raw=subprocess.check_output(['git','-C',str(repo),'ls-tree','-rz','--full-tree','HEAD','--',*(s[:-1] for s in SCOPES)])
        records=[]
        for entry in raw.split(b'\0'):
            if not entry:continue
            meta,name=entry.split(b'\t',1);mode,kind,oid=meta.decode().split()
            if kind=='blob':records.append({'path':name.decode(),'sha':oid})
        return records
    records=json.loads(path.read_text())
    if isinstance(records,dict):
        for key in ('tree','files','entries','blobs','source_files'):
            if key in records:records=records[key];break
    if isinstance(records,dict):
        records=[{'path':p,'sha':v if isinstance(v,str) else v.get('sha',v.get('git_blob'))} for p,v in records.items()]
    return records

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source',type=Path,required=True)
    ap.add_argument('--manifest',type=Path)
    ap.add_argument('--pin',required=True)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--prior194',type=Path,default=HERE/'prior_1e1a41f_classes194.json')
    args=ap.parse_args();repo=args.source.resolve();out=args.output.resolve();out.mkdir(parents=True,exist_ok=True)
    entries=manifest_inputs(repo,args.manifest)
    inputs=[r for r in entries if r.get('type',r.get('kind','blob'))=='blob' and str(r['path']).startswith(SCOPES) and Path(r['path']).suffix.lower() in SUFFIXES]
    if args.manifest is None:
        head=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip()
        if head!=args.pin:raise SystemExit(f'pin mismatch {head} != {args.pin}')
    counters=collections.Counter();raw={};occ=[];sources=[];archives=[];archive_refs=[];seen_zip=set();errors=[]
    def add(data,path,pointer='',representation='literal'):
        if data is None:return
        rows,states,halt=data
        text=normalized_text(data);h=hashlib.sha256(text.encode()).hexdigest()
        raw.setdefault(h,{'data':data,'representative':path,'json_pointer':pointer,'representation':representation,'text':text})
        occ.append({'path':path,'json_pointer':pointer,'representation':representation,'states':len(states),'normalized_sha256':h})
        counters['recognized_tables']+=1;counters['recognized_'+representation]+=1
    def inspect(data,path,depth=0):
        ext=Path(path).suffix.lower();counters['payloads'+ext]+=1
        if ext=='.zip':
            bh=hashlib.sha256(data).hexdigest();archive_refs.append({'path':path,'sha256':bh,'depth':depth})
            if bh in seen_zip:return
            seen_zip.add(bh)
            try:
                with ZipFile(BytesIO(data)) as z:
                    archives.append({'path':path,'sha256':bh,'bytes':len(data),'members':len(z.infolist()),'depth':depth})
                    for member in z.infolist():
                        if not member.is_dir() and Path(member.filename).suffix.lower() in SUFFIXES:
                            inspect(z.read(member),path+'!'+member.filename,depth+1)
            except Exception as e:errors.append({'path':path,'error':str(e)})
        elif ext in ('.tm','.txt','.tsv','.csv'):
            add(ji.lib.parse_table(data),path,representation='tm' if ext=='.tm' else 'other_literal')
        elif ext=='.json':
            if not (b'"L"' in data or b'"R"' in data or b' L ' in data or b' R ' in data or b'"table"' in data or b'"transitions"' in data or re.search(rb'\[\s*\d+\s*,\s*[01]\s*,\s*[01]\s*,\s*-?1\s*,',data)):
                return
            counters['json_screened_in']+=1
            try:node=json.loads(data)
            except Exception as e:errors.append({'path':path,'error':str(e)});return
            stack=[('$',node)]
            while stack:
                ptr,node=stack.pop();value=ji.decode(node)
                if value:add(value,path,ptr,'json');continue
                if isinstance(node,dict):stack.extend((ptr+'/'+str(k),v) for k,v in node.items() if isinstance(v,(dict,list,str)))
                elif isinstance(node,list):stack.extend((ptr+'/'+str(i),v) for i,v in enumerate(node) if isinstance(v,(dict,list,str)))
    for i,r in enumerate(inputs):
        path=r['path'];oid=r.get('sha',r.get('git_blob',r.get('oid')))
        if oid is None:raise ValueError('No Git blob identity for '+path)
        data=(repo/path).read_bytes();actual=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        if actual!=oid:raise ValueError('Working bytes differ from pinned Git blob: '+path)
        sources.append({'path':path,'git_blob':oid,'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)})
        inspect(data,path)
        if i%2000==0:print('scanned',i+1,'/',len(inputs),flush=True)
    prior={r['table_class']:r for r in json.loads(args.prior194.read_text())} if args.prior194.exists() else {}
    by_class={};identities=[];tuples194={};representatives=out/'representatives';representatives.mkdir(exist_ok=True)
    for i,(h,r) in enumerate(raw.items()):
        data=r['data'];rows,states,halt=data;n=len(states)
        roots={q:mc.rooted(rows,states,q) for q in states};maximum=max(k for gh,k in roots.values())
        tc=min(gh for gh,k in roots.values() if k==maximum)
        spanning=maximum==n
        # For disconnected diagnostics mc.table describes only maximal reachable
        # components. Keep each literal identity separate; do not claim graph
        # isomorphism for these records.
        key=(n,tc) if spanning else (n,'nonspanning:'+h)
        if key not in by_class:
            c={'states':n,'table_class':tc,'class_key':key[1],'maximum_reachable':maximum,'spanning':spanning,'representative':r['representative'],'json_pointer':r['json_pointer'],'normalized_sha256':h,'self_loops':sum(t==q for (q,b),(w,d,t) in rows.items()),'occurrences':0}
            if n==194 and tc in prior:
                c.update({k:prior[tc][k] for k in ('historical_name','historical_evidence','mechanism')})
            if n==194 and spanning:
                forms=[full_tuple(data,q,reflect,complement,True)[0] for reflect in (False,True) for complement in (False,True) for q,(gh,k) in roots.items() if k==n]
                exact=min(forms)
                c['enlarged_symmetry_sha256']=hashlib.sha256(json.dumps(exact,separators=(',',':')).encode()).hexdigest()
                tuples194[tc]=exact
            if n<=196:
                rel=f'representatives/{n}_{key[1].replace(":","_")}.tm';(out/rel).write_text(r['text']);c['local_representative']=rel
            by_class[key]=c
        identities.append({'normalized_sha256':h,'states':n,'class_key':key[1],'table_class':tc,'spanning':spanning,'representative':r['representative']})
        r['class_key']=key[1];r['table_class']=tc
        if i%100==0:print('classified',i+1,'/',len(raw),flush=True)
    for item in occ:
        r=raw[item['normalized_sha256']];item['class_key']=r['class_key'];item['table_class']=r['table_class'];by_class[item['states'],r['class_key']]['occurrences']+=1
    classes=sorted(by_class.values(),key=lambda r:(r['states'],r.get('historical_evidence',''),r.get('historical_name',''),r['class_key']))
    classes194=[r for r in classes if r['states']==194]
    summary={'source_revision':args.pin,'scope':__doc__,'tracked_source_payloads_verified':len(sources),'tracked_source_bytes':sum(r['bytes'] for r in sources),**dict(counters),'distinct_archive_payloads':len(archives),'archive_references':len(archive_refs),'normalized_table_identities':len(raw),'spanning_action_graph_classes':sum(r['spanning'] for r in classes),'nonspanning_literal_identities':sum(not r['spanning'] for r in classes),'occurrences_by_states':dict(sorted(collections.Counter(r['states'] for r in occ).items())),'spanning_classes_by_states':dict(sorted(collections.Counter(r['states'] for r in classes if r['spanning']).items())),'classes194_spanning':sum(r['spanning'] for r in classes194),'nonspanning194_literal_identities':sum(not r['spanning'] for r in classes194),'new194_relative_to_prior':sorted({r['table_class'] for r in classes194}-set(prior)),'prior194_absent':sorted(set(prior)-{r['table_class'] for r in classes194}),'errors':errors}
    for name,value in [('summary',summary),('source_blobs',sources),('archives',archives),('archive_references',archive_refs),('occurrences',occ),('identities',identities),('classes',classes),('classes194',classes194),('canonical_tuples194',tuples194)]:
        (out/(name+'.json')).write_text(json.dumps(value,indent=2)+'\n')
    for name,items in [('classes194',classes194),('classes193',[r for r in classes if r['states']==193])]:
        keys=list(dict.fromkeys(k for r in items for k in r))
        with (out/(name+'.csv')).open('w',newline='') as f:
            w=csv.DictWriter(f,fieldnames=keys);w.writeheader();w.writerows(items)
    print(json.dumps(summary,indent=2),flush=True)
    if errors:raise SystemExit('Census completed with parser errors: see summary')

if __name__=='__main__':main()
