"""Copy exact core and owner/independent records, without another replay."""
from pathlib import Path
import hashlib,json
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');O=Path('/tmp/k215-phase15-root')
P='Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase15/'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
mp=Path('/tmp/k215-phase15-publication-execution/copy-map.json')
assert sha(mp)=='4d64819e7eb384c76000fe056b7e0f987f30845b4a74940b8d06256180491056'
rows=read(mp)['files'];assert len(rows)==33
peer=Path('/tmp/k215-phase15-publication-peer/saved-handoff.json')
assert sha(peer)=='ff1d03de4077f1dab1cd09956ae817587944d8a1518b06fbce684873b2ed50a2'
for name,row in read(peer)['files'].items():
    suffix=name[:-4]+'.txt' if name.endswith('.log') else name
    rows.append({'source':row['path'],'target':P+'lean/independent/'+suffix,'sha256':row['sha256'],'bytes':row['bytes']})
rows.append({'source':str(peer),'target':P+'lean/independent/handoff.json','sha256':sha(peer),'bytes':peer.stat().st_size})
assert len({r['target'] for r in rows})==len(rows)==43
core=read('/tmp/k215-phase15-publication-execution/core-hashes.json')
for name,pin in core['files'].items():assert sha(Path(core['directory'])/name)==pin['sha256']
owner=read('/tmp/k215-phase15-publication-execution/run2/saved-review.json')
independent=read('/tmp/k215-phase15-publication-peer/saved-review.json')
assert owner==independent and owner['status']=='PASS_SAVED_PHASE15' and owner['current_sources_checked']
for p in ['/tmp/k215-phase15-publication-execution/run2/saved-actual.json','/tmp/k215-phase15-publication-peer/saved-reader-actual.json']:
    r=read(p);assert r['exit_code']==0 and not r['timed_out']
for row in rows:
    assert sha(row['source'])==row['sha256'] and Path(row['source']).stat().st_size==row['bytes']
    out=R/row['target'];assert not out.exists() and not out.is_symlink()
for row in rows:
    out=R/row['target'];out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(Path(row['source']).read_bytes());assert sha(out)==row['sha256']
for name,pin in core['files'].items():assert sha(R/P/'lean'/name)==pin['sha256']
for m,row in read(O/'current-review.json')['sources'].items():assert sha(row['current'])==row['sha256']
record={'status':'PASS_EXACT_PUBLICATION_COPY_NO_THIRD_REPLAY','files':rows,'core':core,
        'owner_and_independent_receipts_identical':True,'receipt_sha256':'d285ac2ca987aca146e7b4dff4305ab44f83ba3fbcdc716aba8c4007e2b91ede',
        'current_sources_rehashed':199}
(O/'publication-copy-review.json').write_text(json.dumps(record,indent=2)+'\n')
print('Copied43 exact publication files;8core unchanged;199current sources exact;no third replay')
