#!/usr/bin/env python3
"""Optional offline census of the exact pinned PA source checkout.

Recognizes complete binary one-halt .tm/.txt/.tsv/.csv tables and the documented
explicit JSON table encodings, recursively within ZIPs. Does not execute any
generator, infer tables from prose, or certify arithmetic correctness.
"""
from pathlib import Path
from zipfile import ZipFile
from io import BytesIO
import argparse, collections, hashlib, importlib.util, json, re, subprocess, tempfile

HERE=Path(__file__).resolve().parent
PIN='1e1a41f799d4658b829cdd0eabae3775a0c8c4a0'
def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod);return mod
ji=module('json_inventory',HERE/'vendor/json_inventory.py')
mc=module('machine_classes',HERE/'vendor/machine_classes.py')

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source',type=Path,required=True,help='Local Git checkout with all relevant pinned files materialized')
    ap.add_argument('--output',type=Path)
    args=ap.parse_args();repo=args.source.resolve()
    if args.output is None:args.output=Path(tempfile.mkdtemp(prefix='pa194-census-'))
    out=args.output.resolve();out.mkdir(parents=True,exist_ok=True)
    head=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip()
    if head!=PIN:raise SystemExit(f'Expected source revision {PIN}, got {head}')
    listing=subprocess.check_output(['git','-C',str(repo),'ls-tree','-rz','--full-tree','HEAD','--','Computability/BusyBeaver/Research/PA','docs/incoming'])
    inputs=[]
    for item in listing.split(b'\0'):
        if not item:continue
        meta,path=item.split(b'\t',1);mode,kind,oid=meta.decode().split();path=path.decode()
        if kind=='blob' and Path(path).suffix.lower() in ('.tm','.txt','.tsv','.csv','.json','.zip'):
            inputs.append((path,oid))
    missing=[p for p,h in inputs if not (repo/p).is_file()]
    if missing:raise SystemExit(f'Sparse checkout lacks {len(missing)} required files; first missing: {missing[0]}')
    counters=collections.Counter();tables={};occ=[];cache={};sources=[];archives=[];seen_zip=set();errors=[]

    def add(data,path,pointer='',representation='literal'):
        if data is None:return
        rows,states,halt=data;counters['recognized_tables_all_states']+=1
        if len(states)!=194:return
        txt=''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(rows.items()))
        h=hashlib.sha256(txt.encode()).hexdigest()
        if h not in cache:cache[h]=mc.classify(txt.encode())
        info=cache[h];key=info['table']
        if key not in tables:
            tables[key]={'table_class':key,'states':194,'spanning':len(info['roots'])>0 and max(mc.rooted(rows,states,q)[1] for q in states)==194,'representative':path,'json_pointer':pointer,'normalized_sha256':h}
        occ.append({'path':path,'json_pointer':pointer,'representation':representation,'table_class':key,'normalized_sha256':h})
        counters['recognized_tables194']+=1;counters['recognized194_'+representation]+=1

    def inspect(data,path):
        ext=Path(path).suffix.lower();counters['payloads_'+ext]+=1
        if ext=='.zip':
            bh=hashlib.sha256(data).hexdigest()
            if bh in seen_zip:return
            seen_zip.add(bh)
            try:
                with ZipFile(BytesIO(data)) as z:
                    archives.append({'path':path,'sha256':bh,'members':len(z.infolist())})
                    for member in z.infolist():
                        if member.is_dir():continue
                        if Path(member.filename).suffix.lower() in ('.tm','.txt','.tsv','.csv','.json','.zip'):
                            inspect(z.read(member),path+'!'+member.filename)
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

    for path,oid in inputs:
        data=(repo/path).read_bytes()
        actual=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        if actual!=oid:raise SystemExit('Working file differs from pinned Git blob: '+path)
        sources.append({'path':path,'git_blob':oid,'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)})
        inspect(data,path)
    frozen=json.loads((HERE/'comparison194_complete.json').read_text());expected={r['table_class'] for r in frozen}
    summary={'source_revision':PIN,'tracked_source_payloads_verified':len(sources),'scope':__doc__,**counters,'classes194':len(tables),'spanning_classes194':sum(r['spanning'] for r in tables.values()),'nonspanning_classes194':sum(not r['spanning'] for r in tables.values()),'classes_missing_from_replay':sorted(expected-set(tables)),'new_classes_relative_to_frozen':sorted(set(tables)-expected),'errors':errors}
    (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    (out/'source_blobs.json').write_text(json.dumps(sources,indent=2)+'\n')
    (out/'archives.json').write_text(json.dumps(archives,indent=2)+'\n')
    (out/'occurrences194.json').write_text(json.dumps(occ,indent=2)+'\n')
    (out/'classes194.json').write_text(json.dumps(list(tables.values()),indent=2)+'\n')
    print(json.dumps(summary,indent=2));print('Fresh output:',out)
    assert not errors and not summary['classes_missing_from_replay'] and not summary['new_classes_relative_to_frozen']
    assert summary['recognized_tables194']==908 and summary['classes194']==111 and summary['spanning_classes194']==110
if __name__=='__main__':main()
