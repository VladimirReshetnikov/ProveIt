#!/usr/bin/env python3
"""Read-only PA machine corpus audit, including recursively nested ZIPs.

Identity classes preserve each edge's read bit, write bit and direction.
The root-free class is exact for full tables with a graph-spanning root.
Unspanned tables are explicitly excluded, never merged with one another.
This recognizer makes no correctness claim about any parsed machine.
"""
from __future__ import annotations
import argparse, collections, hashlib, io, json, re, subprocess, zipfile
from pathlib import Path

SUFFIXES = ('.tm', '.txt', '.csv', '.tsv')

def sha(data):
    return hashlib.sha256(data).hexdigest()

def parse(data):
    try:
        lines = data.decode('utf8').splitlines()
    except UnicodeError:
        return None
    rows, start = {}, None
    for line in lines:
        line = line.strip()
        if not line: continue
        if line.startswith(('#', '//', ';')):
            match = re.search(r'\bstart\s*(\d+)', line)
            if match and start is None: start = int(match[1])
            continue
        parts = line.split()
        if (len(parts) != 5 or not parts[0].isdigit() or
            parts[1] not in ('0', '1') or parts[2] not in ('0', '1') or
            parts[3] not in ('L', 'R') or not parts[4].isdigit()): return None
        q, b, w, d, t = parts
        key = int(q), int(b)
        if key in rows: return None
        rows[key] = int(w), d, int(t)
    states = {q for q, _ in rows}
    if not states or len(rows) != 2 * len(states): return None
    halts = {t for _, _, t in rows.values()} - states
    if len(halts) != 1: return None
    if start is None and states == set(range(len(states))): start = 0
    if start is not None and start not in states: return None
    return rows, states, next(iter(halts)), start

def canon(table, root, mirror=False, complement=False):
    rows, states, halt, _ = table
    labels, queue, ans = {root: 0}, [root], []
    for q in queue:
        for read in (0, 1):
            w, d, t = rows[q, read ^ int(complement)]
            if complement: w ^= 1
            if mirror: d = 'R' if d == 'L' else 'L'
            if t == halt: target = -1
            else:
                if t not in labels:
                    labels[t] = len(queue)
                    queue.append(t)
                target = labels[t]
            ans.append((w, d, target))
    return json.dumps(ans, separators=(',', ':')).encode(), len(queue)

def rootfree(table, mirror=False, complement=False):
    vals = [s for q in sorted(table[1])
            for s, n in [canon(table, q, mirror, complement)] if n == len(table[1])]
    return (min(vals), len(vals)) if vals else (None, 0)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--repo', required=True, type=Path)
    ap.add_argument('--out', required=True, type=Path)
    ap.add_argument('--cache', type=Path, help='Earlier census JSON; canonicalization is content addressed.')
    a = ap.parse_args()
    repo, out = a.repo.resolve(), a.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    (out / 'tables').mkdir(exist_ok=True)
    head = subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD']).decode().strip()
    cache = {r['sha256']: r for r in json.loads(a.cache.read_text())['raw_tables']} if a.cache else {}
    prefix = 'Computability/BusyBeaver/Research/PA/'
    paths = subprocess.check_output(['git', '-C', str(repo), 'ls-tree', '-r', '--name-only', head, prefix, 'docs/incoming']).decode().splitlines()
    occurrences, archives, archive_refs, failures = [], [], [], []
    raws, seen_zips = {}, set()
    scanned = 0
    def add(data, name):
        nonlocal scanned
        scanned += 1
        table = parse(data)
        if table is None:
            if name.lower().endswith('.tm'): failures.append(name)
            return
        h = sha(data)
        occurrences.append({'path': name, 'sha256': h, 'states': len(table[1]), 'start': table[3], 'halt': table[2]})
        if h not in raws:
            raws[h] = {'table': table, 'first_path': name}
            (out / 'tables' / (h + '.tm')).write_bytes(data)
    def scan_zip(data, name, depth=0):
        h = sha(data)
        archive_refs.append({'path': name, 'sha256': h, 'depth': depth})
        if h in seen_zips: return
        seen_zips.add(h)
        with zipfile.ZipFile(io.BytesIO(data)) as z:
            archives.append({'path': name, 'sha256': h, 'depth': depth, 'bytes': len(data), 'members': len(z.infolist())})
            for entry in z.infolist():
                if entry.is_dir(): continue
                loc = name + '!' + entry.filename
                if entry.filename.lower().endswith('.zip'): scan_zip(z.read(entry), loc, depth+1)
                elif entry.filename.lower().endswith(SUFFIXES): add(z.read(entry), loc)
    for name in paths:
        if not name.lower().endswith(SUFFIXES + ('.zip',)): continue
        path = repo / name
        data = path.read_bytes() if path.exists() else subprocess.check_output(['git', '-C', str(repo), 'show', head + ':' + name])
        if name.lower().endswith('.zip'): scan_zip(data, name)
        else: add(data, name)
    print(f'Scanned {scanned} numeric-suffix text files; {len(occurrences)} tables; {len(raws)} byte identities', flush=True)
    records, classes = [], collections.defaultdict(list)
    for j, (h, row) in enumerate(sorted(raws.items())):
        table = row['table']
        if h in cache:
            rec = dict(cache[h], first_path=row['first_path'])
            classes[(len(table[1]), rec['rootfree_sha256'])].append(h)
            records.append(rec)
            continue
        c, roots = rootfree(table)
        rec = {'sha256': h, 'states': len(table[1]), 'start': table[3], 'halt': table[2],
               'spanning_roots': roots, 'rootfree_sha256': sha(c) if c else None, 'first_path': row['first_path']}
        if table[3] is not None:
            rooted, count = canon(table, table[3])
            rec.update(rooted_sha256=sha(rooted), reachable=count)
        if len(table[1]) == 194 and c:
            reflected, _ = rootfree(table, True, False)
            rec['reflection_class_sha256'] = sha(min(c, reflected))
            sym = [rootfree(table, m, b)[0] for m in (False, True) for b in (False, True)]
            rec['cosmetic_class_sha256'] = sha(min(sym))
        classes[(len(table[1]), rec['rootfree_sha256'])].append(h)
        records.append(rec)
        if (j+1) % 100 == 0: print(f'Canonicalized {j+1}/{len(raws)}', flush=True)
    groups = []
    for (n, h), members in sorted(classes.items(), key=lambda p: (p[0][0], p[0][1] or '')):
        if h is None: continue
        groups.append({'states': n, 'rootfree_sha256': h, 'raw_sha256s': members,
                       'paths': [p['path'] for p in occurrences if p['sha256'] in members]})
    summary = {
        'commit': head,
        'scope': 'All tracked PA files and docs/incoming recursively through nested ZIPs; complete numeric five-column binary L/R tables in .tm, .txt, .csv and .tsv. Identical ZIP payloads visited once. Tables given only in JSON, arbitrary source or prose are outside the literal recognizer and addressed in the narrative review.',
        'parsed_file_occurrences': scanned, 'table_occurrences': len(occurrences), 'unique_table_bytes': len(raws),
        'spanning_action_graph_classes': len(groups), 'unspanned_table_bytes': sum(r['rootfree_sha256'] is None for r in records),
        'recursive_zip_bodies': len(archives), 'zip_references': len(archive_refs),
        'states_occurrence_histogram': dict(sorted(collections.Counter(x['states'] for x in occurrences).items())),
        'states_byte_histogram': dict(sorted(collections.Counter(x['states'] for x in records).items())),
        'states_graph_histogram': dict(sorted(collections.Counter(x['states'] for x in groups).items())),
        '194_reflection_classes': len({r['reflection_class_sha256'] for r in records if 'reflection_class_sha256' in r}),
        '194_full_cosmetic_classes': len({r['cosmetic_class_sha256'] for r in records if 'cosmetic_class_sha256' in r}),
        'top_level_incoming_zips': [p for p in paths if p.startswith('docs/incoming/') and p.lower().endswith('.zip')],
        'filed_packets': sorted(p.name for p in (repo / prefix / 'docs').iterdir() if p.is_dir()),
    }
    result = {'summary': summary, 'archives': archives, 'archive_references': archive_refs,
              'raw_tables': records, 'classes': groups, 'occurrences': occurrences, 'tm_files_outside_recognizer': failures}
    (out / 'census.json').write_text(json.dumps(result, indent=2) + '\n')
    (out / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))

if __name__ == '__main__': main()
