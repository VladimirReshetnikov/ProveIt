#!/usr/bin/env python3
"""Recompute the literal binary-machine inventory for the pinned ProveIt corpus.

Recognizes complete numeric five-column tables, textual, action-array, row-record, and transition-dictionary
tables embedded in JSON, and recursively distinct ZIP payloads. This is a
structural census, not a checker of consistency equivalences. Table identity
for spanning graphs uses the complete canonical transition tuple; a second
digest reproduces ProveIt's machine_classes.py convention for cross-reference.
Unknown starts remain unknown; dense zero is separately marked as a convention.
"""
from pathlib import Path
from collections import Counter
import argparse, csv, hashlib, io, json, re, zipfile, subprocess
import json_inventory as json_recognizer

SNAPSHOT = '1c9524d8bf2e0a27b9a16ff622359927f536e663'
SUFFIXES = {'.tm', '.txt', '.csv', '.tsv', '.json', '.zip'}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def parse(data):
    try:
        text = data.decode('utf-8')
    except UnicodeDecodeError:
        return None
    rows = {}; declared = None
    for line in text.splitlines():
        line = line.strip()
        if not line: continue
        if line.startswith('#'):
            m = re.search(r'\bstart\s*(\d+)', line)
            if m and declared is None: declared = int(m[1])
            continue
        t = line.split()
        if len(t) != 5 or t[1] not in ('0','1') or t[2] not in ('0','1') or t[3] not in ('L','R'):
            return None
        try: q, b, w, n = int(t[0]), int(t[1]), int(t[2]), int(t[4])
        except ValueError: return None
        if q < 0 or (q,b) in rows: return None
        rows[q,b] = (w,t[3],n)
    states = {q for q,b in rows}
    if not states or len(rows) != 2 * len(states): return None
    if declared is not None and declared not in states: return None
    start = declared if declared is not None else (0 if states == set(range(len(states))) else None)
    return rows, states, start, declared

def traversal(rows, states, start, mirror=False, bits=False, loose=False):
    indexes = {start:0}; order = [start]; actions = []
    for q in order:
        for bit in (0,1):
            w, d, target = rows[q, bit ^ bits]
            w ^= bits
            if mirror: d = 'L' if d == 'R' else 'R'
            if target in states:
                if target not in indexes:
                    indexes[target] = len(order); order.append(target)
                actions.append((w,d,indexes[target]))
            else:
                actions.append((0,'R',-1) if loose else (w,d,-1))
    return tuple(actions), len(order)

def encoded(actions):
    return json.dumps(actions, separators=(',',':')).encode()

def classify(data, parsed, extended=False):
    rows, states, start, declared = parsed
    traversals = {q:traversal(rows,states,q) for q in sorted(states)}
    most = max(n for a,n in traversals.values())
    maximal = [a for a,n in traversals.values() if n == most]
    canonical = min(maximal)
    compat = min(sha(encoded(a)) for a in maximal)
    result = dict(byte_sha256=sha(data), states=len(states), transitions=len(rows),
                  start=start, declared_start=declared,
                  start_basis='explicit comment' if declared is not None else ('dense-zero convention' if start is not None else 'unknown'),
                  halt_labels=sorted({n for w,d,n in rows.values()} - states),
                  max_reachable=most, spanning=(most==len(states)),
                  canonical_sha256=sha(encoded(canonical)), table_class=compat,
                  rooted_sha256=None if start is None else sha(encoded(traversals[start][0])),
                  start_reachable=None if start is None else traversals[start][1])
    if most != len(states):
        # A maximal reachable component does not identify the rest of a disconnected
        # table. Keep its bytes distinct, and do not claim graph equivalence.
        result['group_key'] = 'nonspanning-bytes:' + sha(data)
    else:
        result['group_key'] = sha(encoded(canonical))
    if extended and most == len(states):
        forms=[]
        for mirror in (False,True):
            for bits in (False,True):
                forms += [traversal(rows,states,q,mirror,bits,True)[0]
                          for q,(a,n) in traversals.items() if n==most]
        result['extended_sha256'] = sha(encoded(min(forms)))
    return result

def json_tables(value, pointer='$'):
    decoded = json_recognizer.decode(value)
    if decoded:
        rows, states, halt = decoded
        if len(states) < 2:
            return
        data = ''.join(f'{q} {b} {w} {d} {n}\n' for (q,b),(w,d,n) in sorted(rows.items())).encode()
        parsed = parse(data)
        if parsed:
            yield pointer, data, parsed
        return
    if isinstance(value,list):
        for i,v in enumerate(value): yield from json_tables(v,pointer+'/'+str(i))
    elif isinstance(value,dict):
        for k,v in value.items(): yield from json_tables(v,pointer+'/'+str(k))

class Audit:
    def __init__(self, out):
        self.out=out; self.cache={}; self.occurrences=[]; self.failures=[]
        self.json_errors=[]; self.archives={}; self.file_count=0; self.class_bytes={}
    def table(self, locator, data, parsed, encoding):
        digest=sha(data)
        if digest not in self.cache:
            self.cache[digest]=classify(data,parsed,extended=len(parsed[1])==194)
        item=dict(locator=locator,encoding=encoding,**self.cache[digest])
        self.occurrences.append(item)
        self.class_bytes.setdefault(item['group_key'], data)
    def inspect(self, locator, data):
        suffix=Path(locator).suffix.lower();self.file_count+=1
        if suffix in ('.tm','.txt','.csv','.tsv'):
            parsed=parse(data)
            if parsed: self.table(locator,data,parsed,'literal')
            elif suffix=='.tm': self.failures.append(locator)
        elif suffix=='.json':
            try: value=json.loads(data)
            except (ValueError,UnicodeDecodeError) as exc:
                self.json_errors.append({'locator':locator,'error':str(exc)});return
            for pointer,b,p in json_tables(value):self.table(locator+'::JSON'+pointer,b,p,'json')
        elif suffix=='.zip':
            digest=sha(data)
            if digest in self.archives:
                self.archives[digest]['aliases'].append(locator);return
            item={'locator':locator,'sha256':digest,'aliases':[]};self.archives[digest]=item
            with zipfile.ZipFile(io.BytesIO(data)) as z:
                item['members']=len(z.infolist())
                for entry in z.infolist():
                    if not entry.is_dir() and Path(entry.filename).suffix.lower() in SUFFIXES:
                        self.inspect(locator+'::'+entry.filename,z.read(entry))
    def finish(self):
        self.out.mkdir(parents=True,exist_ok=True)
        groups={}
        for x in self.occurrences:
            k=x['group_key']
            if k not in groups:
                groups[k]={key:value for key,value in x.items() if key not in ('locator','encoding','byte_sha256','start','declared_start','start_basis','rooted_sha256','start_reachable')}
                groups[k].update(locators=[],byte_forms=[],start_conventions=[])
            g=groups[k];g['locators'].append(x['locator'])
            if x['byte_sha256'] not in g['byte_forms']:g['byte_forms'].append(x['byte_sha256'])
            start=(x['start'],x['start_basis'],x['rooted_sha256'])
            if start not in g['start_conventions']:g['start_conventions'].append(start)
        ordered=sorted(groups.values(),key=lambda g:(g['states'],g['group_key']))
        summary=dict(snapshot=SNAPSHOT,recognized_occurrences=len(self.occurrences),unique_bytes=len(self.cache),
                     input_files_and_archive_members_examined=self.file_count,spanning_graph_classes=sum(g['spanning'] for g in ordered),
                     spanning_one_halt_classes=sum(g['spanning'] and len(g['halt_labels'])==1 for g in ordered),
                     nonspanning_byte_forms=sum(not g['spanning'] for g in ordered),
                     spanning_counts_by_states=dict(sorted(Counter(g['states'] for g in ordered if g['spanning']).items())),
                     unparsed_tm_files=self.failures,json_parse_failures=self.json_errors,
                     recognized_194_classes=sum(g['states']==194 and g['spanning'] for g in ordered),
                     recognized_193_classes=sum(g['states']==193 and g['spanning'] for g in ordered),
                     scope=__doc__)
        for name,obj in [('summary',summary),('occurrences',self.occurrences),('table_classes',ordered),('archives',list(self.archives.values()))]:
            (self.out/(name+'.json')).write_text(json.dumps(obj,indent=2)+'\n')
        with (self.out/'occurrences.csv').open('w',newline='') as f:
            keys=list(self.occurrences[0]);keys+=['extended_sha256'] if 'extended_sha256' not in keys else []
            wr=csv.DictWriter(f,fieldnames=keys);wr.writeheader();wr.writerows(self.occurrences)
        frontier=self.out/'frontier_tables';frontier.mkdir(exist_ok=True)
        for g in ordered:
            if g['states'] in (193,194) and g['spanning']:
                (frontier/(g['group_key']+'.tm')).write_bytes(self.class_bytes[g['group_key']])
        print(json.dumps({k:v for k,v in summary.items() if k!='scope'},indent=2))

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path)
    ap.add_argument('--git-repo',type=Path,help='Read exact pinned blobs without requiring checkout')
    ap.add_argument('--catalogue-bundle',type=Path)
    ap.add_argument('--incoming',type=Path)
    ap.add_argument('--out',type=Path,required=True)
    args=ap.parse_args();a=Audit(args.out)
    if args.git_repo:
        repo=str(args.git_repo)
        paths=subprocess.check_output(['git','-C',repo,'ls-tree','-r','-z',SNAPSHOT,'--',
                                      'Computability/BusyBeaver/Research/PA','docs/incoming']).split(b'\0')
        tracked=[]
        for entry in paths:
            if not entry:continue
            meta,name=entry.split(b'\t',1);mode,kind,blob=meta.decode().split()
            locator=name.decode()
            if kind=='blob':tracked.append((locator,blob))
        args.out.mkdir(parents=True,exist_ok=True)
        novelty=[]; selected=[]
        relevant=SUFFIXES|{'.tex','.md','.py','.lean','.v'}
        for locator,blob in tracked:
            if Path(locator).suffix.lower() in relevant:selected.append((locator,blob))
        pattern=re.compile(r'\b(?:even|odd|parity|stride|sparse)\b.{0,100}(?:candidate|enumerat|scheduler|search)|(?:candidate|enumerat|scheduler|search).{0,100}\b(?:even|odd|parity|stride|sparse)\b|2.adic|stride2|stride.?two',re.I)
        with (args.out/'git_read.log').open('w') as log:
            process=subprocess.Popen(['git','-C',repo,'cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=log)
            for i,(locator,blob) in enumerate(selected):
                process.stdin.write((blob+'\n').encode());process.stdin.flush()
                header=process.stdout.readline().decode().strip().split()
                if len(header)!=3 or header[1]!='blob':raise RuntimeError((locator,header))
                n=int(header[2]);data=process.stdout.read(n)
                if len(data)!=n or process.stdout.read(1)!=b'\n':raise RuntimeError('truncated cat-file output')
                if Path(locator).suffix.lower() in SUFFIXES:a.inspect(locator,data)
                if Path(locator).suffix.lower() in {'.tex','.md','.txt','.py','.lean','.v'}:
                    for lineno,line in enumerate(data.decode('utf-8',errors='replace').splitlines(),1):
                        if pattern.search(line):novelty.append({'path':locator,'line':lineno,'excerpt':line[:1500]})
                if i%1000==0:print('read',i,'of',len(selected),flush=True)
            process.stdin.close();process.wait()
            if process.returncode:raise RuntimeError('cat-file failed')
        (args.out/'git_manifest.json').write_text(json.dumps({'snapshot':SNAPSHOT,'tracked_file_count':len(tracked),'selected_file_count':len(selected),'files':tracked},indent=2)+'\n')
        (args.out/'scheduler_novelty_search.json').write_text(json.dumps(novelty,indent=2)+'\n')
    elif args.repo:
        for target in (args.repo/'Computability/BusyBeaver/Research/PA',args.repo/'docs/incoming'):
            for p in sorted(target.rglob('*')):
                if p.is_file() and p.suffix.lower() in SUFFIXES:a.inspect(str(p.relative_to(args.repo)),p.read_bytes())
    elif args.catalogue_bundle:
        b=args.catalogue_bundle
        for item in json.loads((b/'inputs/catalogue_index.json').read_text()):
            p=b/item['local_file'];a.inspect(item['kept_file'],p.read_bytes())
    if args.incoming:
        for p in sorted(args.incoming.glob('*.zip')):a.inspect('docs/incoming/'+p.name,p.read_bytes())
    a.finish()

if __name__=='__main__':main()
