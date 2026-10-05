"""New independent byte/locator audit; never execute a reviewed program."""
from pathlib import Path
import hashlib, io, json, re, subprocess, zipfile

ROOT = Path('/home/codex/.codex/worktrees/2a71/Proofs')
TMP = Path('/tmp')
counts = {}
def need(ok, what):
    if not ok: raise ValueError(what)
def sha(b): return hashlib.sha256(b).hexdigest()
def tick(k): counts[k] = counts.get(k, 0) + 1
def git(*a): return subprocess.check_output(['git', *a], cwd=ROOT)
def authenticate(b, obj):
    need(sha(b) == obj['sha256'], 'SHA ' + str(obj.get('path', 'span')))
    size = obj.get('bytes', obj.get('normalized_utf8_bytes'))
    if size is not None: need(len(b) == size, 'size')
def spans(b, items):
    if not items: return
    lines = b.decode().splitlines()
    for s in items:
        lo, hi = s.get('first_line', s.get('first')), s.get('last_line', s.get('last'))
        need(1 <= lo <= hi <= len(lines), 'span bounds')
        part = ('\n'.join(lines[lo-1:hi])+'\n').encode()
        authenticate(part, s)
        if 'lines' in s: need(hi-lo+1 == s['lines'], 'span lines')
        tick('normalized_spans')
def blob(obj):
    spec = obj['commit']+':'+obj['path']
    b = git('show',spec)
    authenticate(b,obj)
    need(git('rev-parse',spec).decode().strip()==obj['blob'],'blob ID')
    for key in ['read_spans','read_spans_reauthenticated']:
        spans(b,obj.get(key,[]))
    tick('git_blob_records')
    return b

pins = {
 'review_beyond_ord_write_62b16914e.md':'0c584cb04115c93ca476b1dc8f93a6f5551b23412597960105e34cdb6d21861c',
 'review_beyond_ord_write_62b16914e.py':'b77050534c72b03af9615d6c2f6df254221969e894f8aed46c75ae07a048cfaa',
 'review_beyond_ord_write_62b16914e.json':'73df09930370852a63ba4ac2f7038e7cfa24498e5614b8f95051fa667a12f81f',
 'review_beyond_ord_gb_62b16914e.md':'f79d9caf8a3d51c9b7850d8833b04650ea7f6d60dca26bf847bfa3f019c027e6',
 'review_beyond_ord_gb_62b16914e.json':'aa2759996a6fd225ece66ea39edee693b71c07cf0839d486c44b8e06b0df604a',
}
for name,pin in pins.items(): need(sha((TMP/name).read_bytes())==pin,name)
r=json.loads((TMP/'review_beyond_ord_write_62b16914e.json').read_text())
peer=json.loads((TMP/'review_beyond_ord_gb_62b16914e.json').read_text())
need(r['reviewer_helper_sha256']==pins['review_beyond_ord_write_62b16914e.py'],'helper pin')
for f in r['changed_files']:
    blob(f['before']); blob(f['after'])
    d=git('diff','--no-ext-diff','--unified=3',r['parent'],r['commit'],'--',f['path'])
    need(sha(d)==f['diff_sha256'] and len(d)==f['diff_bytes'],'diff')
    need(len(d.decode().splitlines())==f['diff_line_count'],'diff line count')
    spans(d,f['diff_read_spans']); tick('diffs')
for k in ['contexts','prior_contexts_reauthenticated','prior_receipts']:
    for f in r[k]: blob(f)
for f in peer['files']: blob(f)
members={}
for arc in r['archives']:
    raw=blob(arc)
    z=zipfile.ZipFile(io.BytesIO(raw))
    actual={i.filename:i for i in z.infolist() if not i.is_dir()}
    need(set(actual)=={m['path'] for m in arc['members']},'complete archive census')
    for m in arc['members']:
        b=z.read(m['path']); authenticate(b,m)
        i=actual[m['path']]
        need(i.compress_size==m['compressed_bytes'] and f'{i.CRC:08x}'==m['crc32'],'ZIP metadata')
        spans(b,m['prior_read_spans_reauthenticated'])
        members[arc['path'],m['path']]=b;tick('members')
    for row in arc['checksum_matches']:
        need(sha(z.read(row['target']))==row['sha256'] and row['matches'],'manifest target')
        manifest=z.read(row['manifest']).decode()
        need(row['sha256'] in manifest,'manifest digest literal')
        tick('checksum_entries')
for p in r['placements']:
    source=members[p['archive'],p['member']]
    need(sha(source)==p['source_sha256'],'placement source')
    need(blob(p['first_placement'])==source==blob(p['at_publication']),'exact placement')
    tick('placements')
host=next(x['path'] for x in r['changed_files'] if x['path'].endswith('article.tex'))
need(host.endswith('article.tex'),'article record')
article=git('show',r['commit']+':'+host).decode()
pat=re.compile(r'\\label(?:\[[^\]]*\])?\{([^}]+)\}')
def labels(text):
    return [{'label':m.group(1),'line':n} for n,line in enumerate(text.splitlines(),1) for m in pat.finditer(line)]
after=labels(article);before=labels(git('show',r['parent']+':'+host).decode())
need(before==r['labels']['before'] and after==r['labels']['after'],'label census')
need(len({x['label'] for x in after})==len(after),'unique labels')
index={x['label']:x['line'] for x in after}
for group in r['source_label_routes']:
    b=members[group['archive'],group['member']]
    need(sha(b)==group['sha256'],'route source')
    old=labels(b.decode())
    need(len(old)==len(group['routes']),'route complete')
    for x,route in zip(old,group['routes']):
        need((x['label'],x['line'])==(route['source_label'],route['source_line']),'source label')
        need(route['target_label']==group['prefix']+x['label'],'label prefix')
        need(index[route['target_label']]==route['target_line'],'target line')
        tick('label_routes')
for ref in r['selected_literal_references']:
    need(ref['resolves'] and ref['target_lines']==[index[ref['target']]],'reference target')
    need(ref['target'] in article.splitlines()[ref['line']-1],'reference source')
    tick('selected_reference_occurrences')
for item in r['independent_proof_review']:
    authenticate((TMP/Path(item['path']).name).read_bytes(),item)
current=(ROOT/host).read_text()
need([x['label'] for x in labels(current)]==[x['label'] for x in after],'correction retains all labels in order')
for f in ['lake-manifest.json','Algebra/SurrealNumbers/lake-manifest.json']:
    j=json.loads(git('show',r['commit']+':'+f))
    package=next(p for p in j['packages'] if p['name']=='mathlib')
    need(package==r['actual_mathlib_package'],'actual manifest pin')
need(r['prior_archive_read_census']=={'other':803,'tex':1665,'total':2468},'read census')
out={'schema':'beyond-ord-publication-root-reauth-v1','artifact_pins':pins,'counts':counts,
     'retained_labels':len(after),'scope':'Independent immutable metadata, spans and locators; no reviewed helper execution, no added proof coverage. Corrected host label sequence retained.'}
dest=TMP/'reauth_beyond_ord_write_root.json'
dest.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
print('PASS',counts,'retained labels',len(after))
