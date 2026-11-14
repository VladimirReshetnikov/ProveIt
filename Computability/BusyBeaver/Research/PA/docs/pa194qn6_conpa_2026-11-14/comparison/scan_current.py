#!/usr/bin/env python3
"""Read-only inventory of literal binary TM tables in a pinned Git tree.

Scans tracked PA files and incoming ZIP members (including nested ZIPs),
without checking out the repository. Recognizes complete numeric five-column
tables in .tm/.txt/.tsv/.csv, plus complete textual tables and five-column
row arrays recursively embedded in JSON. Does not infer machines from arbitrary
programs, other JSON encodings, source syntax, diagrams, or prose. Includes rejected/test tables;
counts must not be interpreted as counts of established Con(PA) machines.
"""
from __future__ import annotations
import argparse, csv, hashlib, io, json, re, subprocess, zipfile
from collections import Counter, defaultdict
from pathlib import Path

SCOPES = ['Computability/BusyBeaver/Research/PA', 'docs/incoming']
TEXT_EXTS = {'.tm', '.txt', '.tsv', '.csv'}
INPUT_EXTS = TEXT_EXTS | {'.json'}
MAX_TEXT = 8 * 1024 * 1024
MAX_ARCHIVE = 128 * 1024 * 1024
MAX_TOTAL_ARCHIVE = 1024 * 1024 * 1024

def sha(data):
    return hashlib.sha256(data).hexdigest()

def parse_table(data):
    try:
        text = data.decode('ascii')
    except UnicodeDecodeError:
        return None
    rows = {}
    declared = None
    for line in text.splitlines():
        line = line.strip()
        if not line:
            continue
        if line.startswith('#'):
            match = re.search(r'\bstart\s*[:=]?\s*(-?\d+)\b', line, re.I)
            if match and declared is None:
                declared = int(match[1])
            continue
        fields = re.split(r'[,\s]+', line)
        if len(fields) != 5:
            return None
        q, b, w, d, n = fields
        if d not in ('L', 'R'):
            return None
        try:
            q, b, w, n = map(int, (q, b, w, n))
        except ValueError:
            return None
        if b not in (0, 1) or w not in (0, 1) or (q, b) in rows:
            return None
        rows[q, b] = (w, d, n)
    states = set(q for q, b in rows)
    if not states or any((q, b) not in rows for q in states for b in (0, 1)):
        return None
    if declared is not None and declared not in states:
        return None
    return rows, states, declared

def rooted(rows, states, start):
    index = {start: 0}
    order = [start]
    out = []
    for q in order:
        for b in (0, 1):
            w, d, nxt = rows[q, b]
            if nxt in states:
                if nxt not in index:
                    index[nxt] = len(index)
                    order.append(nxt)
                out.append((w, d, index[nxt]))
            else:
                out.append((w, d, -1))
    return sha(json.dumps(out, separators=(',', ':')).encode()), len(order)

def classify(rows, states):
    roots = {q: rooted(rows, states, q) for q in states}
    maximum = max(n for h, n in roots.values())
    table_class = min(h for h, n in roots.values() if n == maximum)
    normalized = '\n'.join(f'{q} {b} {w} {d} {n}' for (q, b), (w, d, n) in sorted(rows.items())) + '\n'
    return {
        'states': len(states),
        'transitions': len(rows),
        'halting_labels': sorted({n for w, d, n in rows.values()} - states),
        'max_reachable': maximum,
        'has_graph_spanning_root': maximum == len(states),
        'table_class': table_class,
        'normalized_sha256': sha(normalized.encode()),
        '_roots': roots,
    }

class Scanner:
    def __init__(self, repo, rev, dest):
        self.repo, self.rev, self.dest = repo, rev, dest
        self.occurrences = []
        self.warnings = []
        self.archive_occurrences = []
        self.archive_cache = {}
        self.parse_cache = {}
        self.class_cache = {}
        self.bytes_archive = 0
        self.scanned_candidates = 0
        self.json_files_scanned = 0
        self.frontier_bytes = {}

    def file(self, path, data, depth=0):
        ext = Path(path.split('!')[-1]).suffix.lower()
        if ext == '.zip':
            self.archive(path, data, depth)
            return
        if ext == '.json':
            self.json_file(path, data)
            return
        if ext not in TEXT_EXTS:
            return
        self.scanned_candidates += 1
        digest = sha(data)
        if digest not in self.parse_cache:
            self.parse_cache[digest] = parse_table(data)
        parsed = self.parse_cache[digest]
        if parsed is None:
            return
        rows, states, declared = parsed
        key = tuple(sorted(rows.items()))
        if key not in self.class_cache:
            self.class_cache[key] = classify(rows, states)
        cls = self.class_cache[key]
        start = declared if declared is not None else (0 if sorted(states) == list(range(len(states))) else None)
        record = {k: v for k, v in cls.items() if not k.startswith('_')}
        record.update(path=path, raw_sha256=digest, bytes=len(data),
                      start=start, start_basis='declared' if declared is not None else ('dense_zero_convention' if start == 0 else 'unspecified'),
                      rooted_class=cls['_roots'][start][0] if start is not None else None,
                      reachable_from_start=cls['_roots'][start][1] if start is not None else None,
                      multiple_halting_labels=len(record['halting_labels']) > 1,
                      path_status_hint='rejected_or_diagnostic' if re.search(r'(?i)reject|counterexample|diagnos|negative_control|test_control',path) else 'unreviewed')
        self.occurrences.append(record)
        if 193 <= record['states'] <= 194 and record['table_class'] not in self.frontier_bytes:
            self.frontier_bytes[record['table_class']] = data

    def json_file(self, path, data):
        self.json_files_scanned += 1
        try:
            obj = json.loads(data)
        except (ValueError, UnicodeDecodeError):
            return
        todo = [('$', obj)]
        while todo:
            pointer, value = todo.pop()
            if isinstance(value, str):
                if '\n' in value and 4 < len(value) <= MAX_TEXT:
                    try:
                        candidate = value.encode('ascii')
                    except UnicodeEncodeError:
                        continue
                    if parse_table(candidate) is not None:
                        self.file(path + '::json:' + pointer + '.tm', candidate)
            elif isinstance(value, list):
                if value and all(isinstance(row,list) and len(row)==5 and row[3] in ('L','R') and
                                 all(isinstance(row[i],int) and not isinstance(row[i],bool) for i in (0,1,2,4)) for row in value):
                    candidate = ('\n'.join(' '.join(map(str,row)) for row in value)+'\n').encode()
                    if parse_table(candidate) is not None:
                        self.file(path + '::json:' + pointer + '.tm', candidate)
                else:
                    todo.extend((pointer+'/'+str(i),child) for i,child in enumerate(value) if isinstance(child,(str,list,dict)))
            elif isinstance(value, dict):
                todo.extend((pointer+'/'+str(key).replace('~','~0').replace('/','~1'),child)
                            for key,child in value.items() if isinstance(child,(str,list,dict)))

    def archive(self, path, data, depth):
        digest = sha(data)
        self.archive_occurrences.append({'path':path, 'sha256':digest, 'bytes':len(data), 'depth':depth})
        if depth > 12:
            self.warnings.append({'path':path, 'reason':'archive_depth_limit'})
            return
        try:
            zf = zipfile.ZipFile(io.BytesIO(data))
        except zipfile.BadZipFile:
            self.warnings.append({'path':path, 'reason':'invalid_zip'})
            return
        for member in zf.infolist():
            if member.is_dir():
                continue
            ext = Path(member.filename).suffix.lower()
            if ext not in INPUT_EXTS | {'.zip'}:
                continue
            bound = MAX_ARCHIVE if ext == '.zip' else MAX_TEXT
            member_path = path + '!' + member.filename
            if member.file_size > bound:
                self.warnings.append({'path':member_path, 'reason':'member_size_limit', 'bytes':member.file_size})
                continue
            if self.bytes_archive + member.file_size > MAX_TOTAL_ARCHIVE:
                self.warnings.append({'path':member_path, 'reason':'total_archive_bytes_limit'})
                continue
            self.bytes_archive += member.file_size
            try:
                contents = zf.read(member)
            except (RuntimeError, zipfile.BadZipFile) as error:
                self.warnings.append({'path':member_path,'reason':str(error)})
                continue
            self.file(member_path, contents, depth+1)

    def run(self):
        self.dest.mkdir(parents=True, exist_ok=True)
        cmd = ['git', '-C', str(self.repo), 'ls-tree', '-rzl', self.rev, '--', *SCOPES]
        items = []
        tree = subprocess.check_output(cmd)
        for rec in tree.split(b'\0'):
            if not rec:
                continue
            meta, rawpath = rec.split(b'\t',1)
            mode, kind, oid, size = meta.decode().split()
            path = rawpath.decode()
            if kind != 'blob':
                continue
            items.append((path, oid, int(size)))
        with (self.dest/'tracked_files.tsv').open('w',newline='') as out:
            writer=csv.writer(out,delimiter='\t')
            writer.writerow(['path','git_blob','bytes'])
            writer.writerows(items)
        proc = subprocess.Popen(['git','-c','core.packedGitLimit=64m','-c','core.packedGitWindowSize=8m','-C',str(self.repo),'cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
        assert proc.stdin and proc.stdout
        cache={}
        for path,oid,size in items:
            ext=Path(path).suffix.lower()
            if ext not in INPUT_EXTS|{'.zip'}:
                continue
            if size > (MAX_ARCHIVE if ext == '.zip' else MAX_TEXT):
                self.warnings.append({'path':path,'reason':'git_blob_size_limit','bytes':size})
                continue
            if oid in cache:
                contents = cache[oid]
            elif (self.repo/path).is_file():
                contents = (self.repo/path).read_bytes()
                if len(contents) != size or hashlib.sha1(b'blob '+str(size).encode()+b'\0'+contents).hexdigest() != oid:
                    raise RuntimeError('worktree differs from Git blob: '+path)
            else:
                proc.stdin.write((oid+'\n').encode()); proc.stdin.flush()
                header=proc.stdout.readline().decode().strip()
                if len(header.split()) != 3:
                    raise RuntimeError({'path':path,'object':oid,'header':header,'cat_file_returncode':proc.poll()})
                got_oid,got_type,got_size=header.split()
                if got_type!='blob' or int(got_size)!=size:
                    raise RuntimeError((path,header,size))
                contents=proc.stdout.read(size)
                if proc.stdout.read(1)!=b'\n':
                    raise RuntimeError('bad git frame')
                if ext == '.tm':
                    cache[oid]=contents
            self.file(path,contents)
        proc.stdin.close();proc.wait()
        if proc.returncode:
            raise RuntimeError(f'cat-file exited {proc.returncode}')
        existing_path='Computability/BusyBeaver/Research/PA/docs/MACHINES.tsv'
        existing_text=subprocess.check_output(['git','-C',str(self.repo),'show',f'{self.rev}:{existing_path}']).decode()
        existing_rows=list(csv.DictReader(io.StringIO(existing_text),delimiter='\t'))
        known={r['table_class']:r for r in existing_rows}
        groups=defaultdict(list)
        for row in self.occurrences:
            old=known.get(row['table_class'])
            row['existing_class']=old['class'] if old else None
            row['first_packet']=old['first_packet'] if old else None
            row['known_kept_file']=old['kept_file'] if old else None
            groups[row['table_class']].append(row)
        classes=[]
        for key,group in sorted(groups.items(),key=lambda kv:(kv[1][0]['states'],kv[0])):
            first=group[0]
            classes.append({k:first[k] for k in ['states','table_class','existing_class','first_packet','known_kept_file','max_reachable','has_graph_spanning_root'] }|
                           {'occurrences':len(group),'distinct_bytes':len({r['raw_sha256'] for r in group}),
                            'representative':first['known_kept_file'] or first['path'],
                            'paths':[r['path'] for r in group],
                            'path_status_hints':sorted({r['path_status_hint'] for r in group})})
        by_states=Counter(r['states'] for r in classes)
        summary={
            'repository':'https://github.com/VladimirReshetnikov/ProveIt',
            'revision':self.rev,'scope':SCOPES,'tracked_files':len(items),
            'candidate_text_files_scanned':self.scanned_candidates,
            'json_files_scanned':self.json_files_scanned,
            'literal_table_occurrences':len(self.occurrences),
            'distinct_table_bytes':len({r['raw_sha256'] for r in self.occurrences}),
            'distinct_labeled_transition_tables':len(self.class_cache),
            'table_classes':len(classes),
            'classes_by_working_states':dict(sorted(by_states.items())),
            'existing_catalogue_classes':len(existing_rows),
            'new_classes_relative_to_existing_catalogue':sum(r['existing_class'] is None for r in classes),
            'classes_without_graph_spanning_root':sum(not r['has_graph_spanning_root'] for r in classes),
            'archive_occurrences':len(self.archive_occurrences),
            'distinct_archive_payloads':len({r['sha256'] for r in self.archive_occurrences}),
            'archive_uncompressed_candidate_bytes_read':self.bytes_archive,
            'warnings':self.warnings,
            'limits':{'text_bytes':MAX_TEXT,'archive_bytes':MAX_ARCHIVE,'archive_candidate_total_bytes':MAX_TOTAL_ARCHIVE,'nested_depth':12},
            'notes':[
                'This census includes prototypes, failed candidates, components and test machines.',
                'State counts are literal counts of working-state row labels, excluding rowless halt labels.',
                'No nonhalting/consistency claim follows from parsing or graph comparison.',
                'Rooted hashes retain the inferred or declared start. Dense zero is a packet convention, not a file declaration.',
                'Start-free table classes match the repository convention. When no graph-spanning root exists this is only a maximal reachable component invariant, not a complete all-component isomorphism certificate.',
                'Deleted duplicate files are represented in the repository historical catalogue, not rescanned as current blobs.',
                'JSON supplements recognize full text tables and full five-column row arrays recursively inside JSON. Other dictionary serializations, programs, diagrams and prose are outside the literal-table census.'
            ]}
        for name,value in [('summary.json',summary),('table_occurrences.json',self.occurrences),('table_classes.json',classes),('archives.json',self.archive_occurrences)]:
            (self.dest/name).write_text(json.dumps(value,indent=2)+'\n')
        for name,records in [('table_occurrences.csv',self.occurrences),('table_classes.csv',classes)]:
            with (self.dest/name).open('w',newline='') as out:
                writer=csv.DictWriter(out,fieldnames=list(records[0]))
                writer.writeheader()
                for row in records:
                    writer.writerow({k:json.dumps(v,separators=(',',':')) if isinstance(v,(dict,list)) else v for k,v in row.items()})
        frontier = self.dest/'frontier_tables'
        frontier.mkdir(exist_ok=True)
        for key,data in self.frontier_bytes.items():
            (frontier/(key+'.tm')).write_bytes(data)
        print(json.dumps(summary,indent=2))

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('repo',type=Path)
    parser.add_argument('--revision',default='2337ce611a26e308697ccbddb2a1636f989f01c3')
    parser.add_argument('--output',type=Path,default=Path(__file__).parent/'census')
    args=parser.parse_args()
    Scanner(args.repo,args.revision,args.output).run()
