#!/usr/bin/env python3
"""Reproduce a read-only literal numeric transition-table census from a pinned Git tree.
Scope: complete binary five-column tables in .tm/.txt/.tsv/.csv, recursively in ZIPs.
A table census does not establish any consistency theorem; search/rejected fixtures are included.
"""
import csv, hashlib, importlib.util, io, json, pathlib, subprocess, zipfile, collections, re, argparse
CODE_DIR=pathlib.Path(__file__).resolve().parent
ap=argparse.ArgumentParser()
ap.add_argument('--repo',type=pathlib.Path,required=True,help='Local ProveIt checkout containing the pinned commit')
ap.add_argument('--revision',default='3cc7fbf75ba111a0da696ef2f6001dd528891bd5')
ap.add_argument('--output',type=pathlib.Path,default=CODE_DIR/'census_replay')
args=ap.parse_args()
BASE=args.output.resolve();BASE.mkdir(parents=True,exist_ok=True)
spec=importlib.util.spec_from_file_location('machine_classes',(CODE_DIR/'machine_classes_source.py'))
mc=importlib.util.module_from_spec(spec);spec.loader.exec_module(mc)
REPO=args.repo.resolve()
REV=args.revision
PREFIXES=['Computability/BusyBeaver/Research/PA','docs/incoming']
records=[]; errors=[];cache={};archives=[];archive_payloads=set(); occurrences=[]

def sha(b):return hashlib.sha256(b).hexdigest()

def table(b,path):
    h=sha(b)
    if h in cache:
        if cache[h] is not None:occurrences.append(dict(path=path,sha256=h))
        return
    try:
        dat=mc.parse(b)
        if len({n for w,d,n in dat[0].values()}-dat[1])!=1:raise ValueError('not exactly one undefined halt label')
        c=mc.classify(b)
        c['roots']=sorted(c['roots'])
    except (ValueError,UnicodeError) as exc:
        cache[h]=None
        if path.lower().endswith('.tm'):errors.append(dict(path=path,error=str(exc)))
        return
    cache[h]=c;occurrences.append(dict(path=path,sha256=h))
    c=dict(c,sha256=h,bytes=len(b),representative=path)
    records.append(c)
    out=BASE/'tables';out.mkdir(exist_ok=True)
    if c['states']<=196:(out/(h+'.tm')).write_bytes(b)

def archive(b,path,depth=0):
    h=sha(b);already=h in archive_payloads
    archives.append(dict(path=path,sha256=h,bytes=len(b),depth=depth,already_scanned=already))
    if already:return
    archive_payloads.add(h)
    try:
        with zipfile.ZipFile(io.BytesIO(b)) as z:
            for n in z.namelist():
                ext=pathlib.Path(n).suffix.lower()
                if n.endswith('/'):continue
                if ext=='.zip':archive(z.read(n),path+'!'+n,depth+1)
                elif ext in ('.tm','.txt','.tsv','.csv'):table(z.read(n),path+'!'+n)
    except Exception as exc:errors.append(dict(path=path,error=str(exc)))

raw=subprocess.check_output(['git','-C',str(REPO),'ls-tree','-r','-z',REV,*PREFIXES])
entries=[]
for entry in raw.split(b'\0'):
    if not entry:continue
    meta,p=entry.split(b'\t',1);mode,kind,obj=meta.decode().split();p=p.decode()
    if kind=='blob':entries.append((p,obj))
# Serial read/write avoids filling either pipe. No checkout or object modifications.
git=subprocess.Popen(['git','-C',str(REPO),'cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
readmes=[]
for p,obj in entries:
    ext=pathlib.Path(p).suffix.lower()
    is_readme=pathlib.Path(p).name in ('README.md','README.txt') and p.count('/') == 6
    if ext not in ('.tm','.txt','.tsv','.csv','.zip') and not is_readme:continue
    git.stdin.write((obj+'\n').encode());git.stdin.flush()
    header=git.stdout.readline().decode().split();n=int(header[2]);b=git.stdout.read(n);assert git.stdout.read(1)==b'\n'
    if ext=='.zip':archive(b,p)
    elif ext in ('.tm','.txt','.tsv','.csv'):table(b,p)
    if is_readme:readmes.append(dict(path=p,text=b.decode()))
git.stdin.close();git.wait()
by_machine=collections.defaultdict(list);by_table=collections.defaultdict(list)
for r in records:
    by_table[r['table']].append(r)
    if r['machine']:by_machine[r['machine']].append(r)
summary=dict(snapshot=REV,git_blob_paths=len(entries),recognized_occurrences=len(occurrences),unique_byte_forms=len(records),
  rooted_machine_classes=len(by_machine),unrooted_table_classes=len(by_table),
  spanning_root_graph_classes=len({r['table'] for r in records if r['states']==r['reachable']}),
  disconnected_fixture_byte_forms=sum(r['states']!=r['reachable'] for r in records),archives=len(archives),unique_archive_payloads=len(archive_payloads),
  byte_forms_by_states=dict(sorted(collections.Counter(r['states'] for r in records).items())),
  rooted_classes_by_reachable_states=dict(sorted(collections.Counter(rs[0]['reachable'] for rs in by_machine.values()).items())),
  rootfree_classes_by_states=dict(sorted(collections.Counter(rs[0]['states'] for rs in by_table.values()).items())),
  errors=errors)
report=dict(summary=summary,identities=records,occurrences=occurrences,archives=archives)
(BASE/'current_census.json').write_text(json.dumps(report,indent=2)+'\n')
(BASE/'packet_readmes.json').write_text(json.dumps(readmes,indent=2)+'\n')
with (BASE/'machine_identities.csv').open('w') as f:
    cols=['states','reachable','start','sha256','machine','table','bytes','representative']
    w=csv.DictWriter(f,fieldnames=cols,extrasaction='ignore');w.writeheader();w.writerows(sorted(records,key=lambda x:(x['states'],x['representative'])))
with (BASE/'table_occurrences.csv').open('w') as f:
    w=csv.DictWriter(f,fieldnames=['path','sha256']);w.writeheader();w.writerows(occurrences)
print(json.dumps(summary,indent=2))
print('Incoming recognized tables:')
for r in records:
    if r['representative'].startswith('docs/incoming/') and r['states']<=194:print(r['states'],r['sha256'],r['machine'],r['representative'])
