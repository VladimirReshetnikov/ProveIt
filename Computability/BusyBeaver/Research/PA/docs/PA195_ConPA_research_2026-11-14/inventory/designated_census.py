#!/usr/bin/env python3
"""Independently check selected, explicitly started tables against pinned ZIPs."""
from pathlib import Path
import collections,csv,json,sys,zipfile
from inventory import parse_table,canonical_root,digest,PIN

def main():
    repo=Path(sys.argv[1]); spec=Path(sys.argv[2]); output=Path(sys.argv[3]);output.mkdir(parents=True,exist_ok=True)
    records=[]
    for x in json.loads(spec.read_text()):
        with zipfile.ZipFile(repo/'docs/incoming'/x['archive']) as z: raw=z.read(x['member'])
        if digest(raw)!=x['sha256']: raise ValueError('changed machine '+x['name'])
        meta,rows=parse_table(raw)
        if not meta['complete'] or meta['terminal_labels']!=[x['halt']]:raise ValueError('invalid literal machine '+x['name'])
        graph=canonical_root(rows,x['start'])
        if graph['reachable_working_states']!=meta['working_states']:raise ValueError('unreachable control '+x['name'])
        r={**x,**meta,**graph};records.append(r)
        (output/(x['name']+'.tm')).write_bytes(raw)
    classes=collections.defaultdict(list)
    for r in records:classes[r['rooted_graph_sha256']].append(r['name'])
    result={'source_commit':PIN,'table_count':len(records),'rooted_graph_class_count':len(classes),'status_counts':dict(collections.Counter(x['status'] for x in records)),'classes':dict(classes),'tables':records,'scope':'Exact table identity, structure, start/halt convention and graph isomorphism; does not reprove mathematical consistency calibration or full simulation certificates.'}
    (output/'catalogue.json').write_text(json.dumps(result,indent=2)+'\n')
    with (output/'catalogue.csv').open('w',newline='') as f:
        keys=['name','status','working_states','rows','start','halt','sha256','rooted_graph_sha256','archive','member'];w=csv.DictWriter(f,keys,extrasaction='ignore');w.writeheader();w.writerows(records)
    print(json.dumps({k:v for k,v in result.items() if k not in ('tables','classes')},indent=2))

if __name__=='__main__':main()
