#!/usr/bin/env python3
"""Finish the census by inspecting the explicitly reported large JSON blobs."""
from pathlib import Path
import argparse,collections,csv,hashlib,importlib.util,io,json,subprocess,zipfile

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('repo',type=Path)
parser.add_argument('--census',type=Path,default=Path(__file__).parent)
args=parser.parse_args()
ROOT=args.census
REPO=args.repo
SPEC=importlib.util.spec_from_file_location('scan_current',Path(__file__).with_name('scan_current.py'))
MOD=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(MOD)
summary=json.loads((ROOT/'summary.json').read_text())
warnings=summary['warnings']
if not warnings:
    print('No unresolved large-JSON inputs remain.')
    raise SystemExit(0)
scanner=MOD.Scanner(REPO,summary['revision'],ROOT)
outer_cache={}
seen={}
records=[]

for warning in warnings:
    path=warning['path']
    if not path.endswith('.json'):
        raise RuntimeError('Unexpected unfinished input: '+path)
    pieces=path.split('!')
    if pieces[0] not in outer_cache:
        outer_cache[pieces[0]]=subprocess.check_output(['git','-c','core.packedGitLimit=64m','-C',str(REPO),'show',summary['revision']+':'+pieces[0]])
    data=outer_cache[pieces[0]]
    for member in pieces[1:]:
        data=zipfile.ZipFile(io.BytesIO(data)).read(member)
    digest=hashlib.sha256(data).hexdigest()
    if digest not in seen:
        before=len(scanner.occurrences)
        scanner.json_file(path,data)
        seen[digest]=scanner.occurrences[before:]
        mode='parsed'
    else:
        original=seen[digest]
        for old in original:
            row=dict(old)
            row['path']=path+old['path'][old['path'].index('::json:'):]
            scanner.occurrences.append(row)
        mode='duplicate_bytes_already_parsed'
    records.append({'path':path,'bytes':len(data),'sha256':digest,'inspection':mode,'recognized_table_values':len(seen[digest])})
    print(mode,len(data),len(seen[digest]),path.split('/')[-1],flush=True)

occurrences=json.loads((ROOT/'table_occurrences.json').read_text())+scanner.occurrences
existing_text=subprocess.check_output(['git','-C',str(REPO),'show',summary['revision']+':Computability/BusyBeaver/Research/PA/docs/MACHINES.tsv']).decode()
known={r['table_class']:r for r in csv.DictReader(io.StringIO(existing_text),delimiter='\t')}
groups=collections.defaultdict(list)
for row in occurrences:
    old=known.get(row['table_class'])
    row['existing_class']=old['class'] if old else None
    row['first_packet']=old['first_packet'] if old else None
    row['known_kept_file']=old['kept_file'] if old else None
    groups[row['table_class']].append(row)
classes=[]
for key,group in sorted(groups.items(),key=lambda kv:(kv[1][0]['states'],kv[0])):
    first=group[0]
    classes.append({k:first[k] for k in ['states','table_class','existing_class','first_packet','known_kept_file','max_reachable','has_graph_spanning_root']}|
                   {'occurrences':len(group),'distinct_bytes':len({r['raw_sha256'] for r in group}),
                    'representative':first['known_kept_file'] or first['path'],'paths':[r['path'] for r in group],
                    'path_status_hints':sorted({r['path_status_hint'] for r in group})})
summary.update(literal_table_occurrences=len(occurrences),distinct_table_bytes=len({r['raw_sha256'] for r in occurrences}),
    distinct_labeled_transition_tables=len({r['normalized_sha256'] for r in occurrences}),table_classes=len(classes),
    classes_by_working_states=dict(sorted(collections.Counter(r['states'] for r in classes).items())),
    classes_without_graph_spanning_root=sum(not r['has_graph_spanning_root'] for r in classes),
    new_classes_relative_to_existing_catalogue=sum(r['existing_class'] is None for r in classes),
    large_json_supplement={'paths_inspected':len(records),'distinct_payloads':len(seen),'new_table_occurrences':len(scanner.occurrences),
                           'max_bytes':max(r['bytes'] for r in records)},warnings=[])
summary['notes'].append('The reported first-pass large-JSON exclusions were all inspected in scan_large_json.py; no size or nesting exclusions remain. See large_json_audit.json.')
summary['full_spanning_graph_classes']=sum(r['has_graph_spanning_root'] for r in classes)
summary['full_spanning_graph_classes_by_state_count']=dict(sorted(collections.Counter(r['states'] for r in classes if r['has_graph_spanning_root']).items()))
for name,data in [('summary.json',summary),('table_occurrences.json',occurrences),('table_classes.json',classes),('large_json_audit.json',records)]:
    (ROOT/name).write_text(json.dumps(data,indent=2)+'\n')
for name,data in [('table_occurrences.csv',occurrences),('table_classes.csv',classes)]:
    with (ROOT/name).open('w',newline='') as out:
        w=csv.DictWriter(out,fieldnames=list(data[0]));w.writeheader()
        for row in data:
            w.writerow({k:json.dumps(v,separators=(',',':')) if isinstance(v,(list,dict)) else v for k,v in row.items()})
for key,data in scanner.frontier_bytes.items():
    (ROOT/'frontier_tables'/(key+'.tm')).write_bytes(data)
print(json.dumps({k:summary[k] for k in ['literal_table_occurrences','distinct_table_bytes','table_classes','full_spanning_graph_classes','full_spanning_graph_classes_by_state_count','large_json_supplement','warnings']},indent=2))
