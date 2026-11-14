#!/usr/bin/env python3
"""Reproduce the literal-table comparison for the pinned PA research corpus.

This audits tables, not their mathematical correctness. A complete numeric
five-column binary table must have exactly one undefined halting label.
The action graph class forgets the designated start; supplied starts are
recorded separately. Non-spanning diagnostic graphs are listed separately.
"""
import argparse
import collections
import csv
import hashlib
import io
import json
from pathlib import Path
import zipfile

from machine_classes import parse, classify, rooted

SUFFIXES = {'.tm', '.txt', '.csv', '.tsv'}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--repo',type=Path,required=True)
    ap.add_argument('--incoming',type=Path,required=True)
    ap.add_argument('--historical-zips',type=Path)
    ap.add_argument('--output',type=Path,required=True)
    a=ap.parse_args()
    a.output.mkdir(parents=True,exist_ok=True)
    occurrences=[]; data_by_sha={}; archives={}; excluded=[]
    def inspect(data,locator):
        try:
            rows,states,start=parse(data)
        except (ValueError,UnicodeDecodeError,IndexError):
            return
        halts=sorted({n for _,_,n in rows.values()}-states)
        if len(halts)!=1:
            excluded.append(dict(locator=locator,states=len(states),reason='not exactly one halt',halts=halts))
            return
        sha=hashlib.sha256(data).hexdigest()
        occurrences.append(dict(locator=locator,sha256=sha,states=len(states),declared_or_dense_start=start))
        data_by_sha.setdefault(sha,data)
    def inspect_json(data,locator):
        if b'"table"' not in data:return
        try:obj=json.loads(data)
        except (ValueError,UnicodeDecodeError):return
        def walk(x,path):
            if isinstance(x,dict):
                for key,value in x.items():
                    if key=='table' and isinstance(value,str):inspect(value.encode(),locator+'#'+path+'/'+key)
                    elif isinstance(value,(list,dict)):walk(value,path+'/'+key)
            elif isinstance(x,list):
                for i,value in enumerate(x):walk(value,path+'/'+str(i))
        walk(obj,'')
    def archive(data,locator):
        sha=hashlib.sha256(data).hexdigest()
        if sha in archives:
            archives[sha]['locators'].append(locator);return
        archives[sha]=dict(bytes=len(data),locators=[locator])
        with zipfile.ZipFile(io.BytesIO(data)) as z:
            for name in z.namelist():
                suffix=Path(name).suffix.lower()
                if suffix=='.zip':archive(z.read(name),locator+'!'+name)
                elif suffix in SUFFIXES:inspect(z.read(name),locator+'!'+name)
                elif suffix=='.json':inspect_json(z.read(name),locator+'!'+name)
    base=a.repo/'Computability/BusyBeaver/Research/PA'
    for p in sorted(base.rglob('*')):
        if not p.is_file():continue
        if p.suffix.lower() in SUFFIXES:inspect(p.read_bytes(),str(p.relative_to(a.repo)))
        elif p.suffix.lower()=='.zip':archive(p.read_bytes(),str(p.relative_to(a.repo)))
        elif p.suffix.lower()=='.json':inspect_json(p.read_bytes(),str(p.relative_to(a.repo)))
    for p in sorted(a.incoming.glob('*.zip')):
        archive(p.read_bytes(),'docs/incoming/'+p.name)
    if a.historical_zips:
        manifest=json.loads((a.historical_zips/'manifest.json').read_text())
        for r in manifest:
            p=a.historical_zips/Path(r['local']).name
            archive(p.read_bytes(),r['path'])
    print('Literal occurrences',len(occurrences),'byte forms',len(data_by_sha),'archive payloads',len(archives),flush=True)
    cache_path=a.output/'classification_cache.json'
    cache=json.loads(cache_path.read_text()) if cache_path.exists() else {}
    infos={}
    for i,(sha,data) in enumerate(data_by_sha.items()):
        if sha not in cache:
            info=classify(data);info['roots']=sorted(info['roots'])
            cache[sha]=info
        infos[sha]=cache[sha]
        if 'max_reachable' not in infos[sha]:
            if infos[sha]['reachable']==infos[sha]['states']:
                infos[sha]['max_reachable']=infos[sha]['states']
            else:
                rows,states,_=parse(data)
                infos[sha]['max_reachable']=max(rooted(rows,states,q)[1] for q in states)
        if (i+1)%50==0:
            cache_path.write_text(json.dumps(cache,sort_keys=True)+'\n')
            print('Classified',i+1,'/',len(data_by_sha),flush=True)
    cache_path.write_text(json.dumps(cache,sort_keys=True)+'\n')
    groups=collections.defaultdict(list)
    for occurrence in occurrences:
        info=infos[occurrence['sha256']]
        occurrence.update({k:info.get(k) for k in ['machine','table','reachable']})
        groups[info['table']].append(occurrence)
    classes=[]
    for key,occs in sorted(groups.items()):
        info=infos[occs[0]['sha256']]
        classes.append(dict(table_class=key,states=info['states'],reachable=info['reachable'],
            has_spanning_root=info['max_reachable']==info['states'],
            byte_forms=len({x['sha256'] for x in occs}),occurrences=len(occs),
            locators=[x['locator'] for x in occs],
            rooted_classes=sorted({x['machine'] for x in occs if x['machine']})))
    counts=collections.Counter(str(x['states']) for x in classes if x['has_spanning_root'])
    summary=dict(snapshot='2a88cb6a3f823e0de5addf19d725bf8373860c71',
        literal_occurrences=len(occurrences),byte_forms=len(infos),
        action_graph_classes_with_spanning_root=sum(x['has_spanning_root'] for x in classes),
        nonspanning_classes=sum(not x['has_spanning_root'] for x in classes),
        classes_by_states=dict(sorted(counts.items(),key=lambda x:int(x[0]))),
        unique_archive_payloads=len(archives),
        scope='Numeric complete five-column tables in .tm/.txt/.csv/.tsv files and explicit string-valued table fields in JSON; recursive ZIP traversal; identical ZIP payloads visited once. Counts include rejected, experimental, and synthetic tables. Graph classes ignore designated start; correctness is not inferred from file or graph presence.')
    for name,obj in [('summary.json',summary),('occurrences.json',occurrences),('classes.json',classes),('archives.json',archives),('excluded.json',excluded)]:
        (a.output/name).write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')
    with (a.output/'frontier194.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['table_class','states','byte_forms','occurrences','first_locator'])
        for x in classes:
            if x['states']==194:w.writerow([x['table_class'],194,x['byte_forms'],x['occurrences'],x['locators'][0]])
    print(json.dumps(summary,indent=2),flush=True)


if __name__=='__main__':main()
