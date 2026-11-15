#!/usr/bin/env python3
"""Reproducible .tm census of pinned ProveIt PA paths and nested incoming ZIPs.

This compares transition graphs, not mathematical correctness. Full-graph
root coverage is recorded so that the inherited all-roots canonicalizer is
not mistaken for a general disconnected-graph isomorphism algorithm.
"""
import argparse, collections, csv, hashlib, importlib.util, io, json, pathlib, re, subprocess, zipfile

HERE = pathlib.Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('machine_classes', HERE / 'machine_classes.py')
mc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mc)

def walk_zip(data, prefix, depth=0):
    if depth > 5:
        raise ValueError('nested archive depth exceeds 5: ' + prefix)
    with zipfile.ZipFile(io.BytesIO(data)) as z:
        for name in sorted(z.namelist()):
            if name.endswith('/'):
                continue
            if name.lower().endswith('.tm'):
                yield prefix + '!' + name, z.read(name)
            elif name.lower().endswith('.zip'):
                yield from walk_zip(z.read(name), prefix + '!' + name, depth + 1)

def collect(root, overlay=None):
    # Reproduce the exact tracked scope, independent of unrelated local files.
    binding=json.loads((HERE/'source_blob_binding.json').read_text())
    for entry in binding['files']:
        relative=entry['path'];p=root/relative
        if not p.exists() and overlay is not None:p=overlay/relative
        data=p.read_bytes()
        if hashlib.sha256(data).hexdigest()!=entry['sha256']:
            raise ValueError('Pinned source byte mismatch: '+relative)
        if relative.lower().endswith('.tm'):
            yield relative,data
        elif relative.lower().endswith('.zip'):
            yield from walk_zip(data,relative)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('source', type=pathlib.Path)
    ap.add_argument('--out', type=pathlib.Path, required=True)
    ap.add_argument('--overlay', type=pathlib.Path)
    ap.add_argument('--reuse', type=pathlib.Path)
    args = ap.parse_args()
    pinned='d8d4fb10149d6a76a56e615a35648c8c32847cf4'
    if (args.source/'.git').exists():
        actual=subprocess.check_output(['git','-C',str(args.source),'rev-parse','HEAD'],text=True).strip()
        if actual!=pinned:raise ValueError('Checkout must be pinned to '+pinned+', got '+actual)
    args.out.mkdir(parents=True, exist_ok=True)
    prior = list(csv.DictReader((HERE / 'MACHINES.tsv').open(), delimiter='\t'))
    prior_by_table = {r['table_class']:r for r in prior}
    cache, records, errors = {}, [], []
    if args.reuse:
        fields=['states','start','declared','table','halting','machine','reachable','loose','full_graph_root','max_reachable']
        for r in json.loads(args.reuse.read_text()):
            cache[r['sha256']]={k:r[k] for k in fields if k in r}
    observed=set()
    for path, data in collect(args.source,args.overlay):
        bh = hashlib.sha256(data).hexdigest()
        observed.add(bh)
        if bh not in cache:
            try:
                info = mc.classify(data)
                rows, states, start, declared = mc.parse(data)
                most = info['reachable']
                if most < len(states) and start is not None:
                    most = max(mc.rooted(rows, states, q)[1] for q in states)
                info['full_graph_root'] = (most == len(states))
                info['max_reachable'] = most
                info.pop('roots')
                cache[bh] = info
            except Exception as e:
                cache[bh] = {'error':str(e)}
        info = cache[bh]
        if 'error' in info:
            errors.append({'path':path,'sha256':bh,**info})
        else:
            old = prior_by_table.get(info['table'])
            records.append({'path':path,'sha256':bh,**info,
                            'prior_class':old['class'] if old else None,
                            'prior_kept_file':old['kept_file'] if old else None})
    groups = collections.defaultdict(list)
    for r in records:
        groups[r['table']].append(r)
    classes=[]
    for table, rr in groups.items():
        old=prior_by_table.get(table)
        classes.append({'table_class':table,'states':rr[0]['states'],
                        'prior_class':old['class'] if old else None,
                        'prior_kept_file':old['kept_file'] if old else None,
                        'full_graph_root':all(r['full_graph_root'] for r in rr),
                        'file_count':len(rr),'byte_versions':len({r['sha256'] for r in rr}),
                        'rooted_classes':sorted({r['machine'] for r in rr if r['machine']}),
                        'paths':[r['path'] for r in rr]})
    classes.sort(key=lambda c:(c['states'],c['table_class']))
    incoming=[r for r in records if r['path'].startswith('docs/incoming/')]
    new=[c for c in classes if c['prior_class'] is None]
    summary={'commit':pinned,
      'scope':'Explicit .tm files throughout PA plus recursively nested ZIP members under docs/incoming.',
      'parsed_file_occurrences':len(records),'parse_errors':len(errors),
      'distinct_bytes':len(observed),'graph_classes':len(classes),
      'classes_by_states':dict(sorted(collections.Counter(c['states'] for c in classes).items())),
      'prior_classes':len(prior),'incoming_occurrences':len(incoming),
      'incoming_graph_classes':len({r['table'] for r in incoming}),
      'new_to_prior_census_classes':len(new),
      'new_to_prior_by_states':dict(sorted(collections.Counter(c['states'] for c in new).items())),
      'classes_without_full_graph_root':sum(not c['full_graph_root'] for c in classes),
      'correctness_warning':'A graph class does not certify blank-start correctness, consistency calibration, or an iPRA proof.'}
    (args.out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    (args.out/'classes.json').write_text(json.dumps(classes,indent=2)+'\n')
    (args.out/'files.json').write_text(json.dumps(records,indent=2)+'\n')
    (args.out/'errors.json').write_text(json.dumps(errors,indent=2)+'\n')
    fields=['table_class','states','prior_class','prior_kept_file','full_graph_root','file_count','byte_versions','rooted_classes','paths']
    with (args.out/'classes.tsv').open('w') as f:
        w=csv.DictWriter(f,fields,delimiter='\t'); w.writeheader()
        for c in classes:
            w.writerow({**c,'rooted_classes':' | '.join(c['rooted_classes']),'paths':' | '.join(c['paths'])})
    print(json.dumps(summary,indent=2))

if __name__=='__main__':main()
