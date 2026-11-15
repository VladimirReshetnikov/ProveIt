#!/usr/bin/env python3
"""Replay the bounded adaptive bootstrap experiment.

Default: at most three distinct modified rows. Larger budgets run only when
explicitly requested with --max-edits. Compile with C++17 into --output,
which must be outside this source directory. No network access is required.
"""
from pathlib import Path
import argparse,hashlib,json,re,subprocess,time

ROOT=Path(__file__).resolve().parent
BOUND=200000
COUNTERS=('edits','bound','branches','leaves','ticks','halts','rays','cycles','limits','hits')

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def done_counts(path):
    if not path.exists():return None
    done=[line for line in path.read_text().splitlines() if line.startswith('DONE ')]
    if not done:return None
    assert len(done)==1,('ambiguous completion record',str(path))
    parts=done[0].split()[1:]
    assert len(parts)%2==0
    fields=dict(zip(parts[::2],parts[1::2]))
    assert set(fields)==set(COUNTERS)|{'seconds'},fields
    # Elapsed time is intentionally not a reproducibility assertion.
    return {key:int(fields[key]) for key in COUNTERS}

def check_counts(counts,k):
    assert counts['edits']==k and counts['bound']==BOUND,counts
    assert all(counts[key]>=0 for key in COUNTERS),counts
    assert counts['branches']==counts['leaves'],counts
    assert sum(counts[key] for key in ('halts','rays','cycles','limits','hits'))==counts['leaves'],counts

def read_hits(path,edits,k):
    if not path.exists():return None
    hits=[json.loads(line) for line in path.read_text().splitlines() if line.strip()]
    for hit in hits:
        ids=hit['edits']
        assert len(ids)<=k and len(ids)==len(set(ids)),hit
        assert all(0<=i<len(edits) for i in ids),hit
        assert len({(edits[i][1],edits[i][2]) for i in ids})==len(ids),hit
        assert 0<=hit['steps']<=BOUND and 25<=hit['pc']<=44,hit
        assert len(hit['values'])>=10 and all(v>=0 for v in hit['values']),hit
        assert hit['ones']==sorted(set(hit['ones'])),hit
    return hits

def validate_inputs():
    provenance=json.loads((ROOT/'PROVENANCE.json').read_text())
    assert provenance['commit']=='e6a84f8dd2702f5f8c7db3ca53a8cbacb1d89f4f'
    for name,item in provenance['inputs'].items():assert sha(ROOT/name)==item['sha256'],name
    assert sha(ROOT/'edits.tsv')==provenance['derived_input']['edits.tsv']['sha256']
    assert sha(ROOT/'adaptive_startup.cpp')==provenance['program']['sha256']
    table={}
    for line in (ROOT/'runtime193.native.tm').read_text().splitlines():
        q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
        assert 0<=q<3000 and b in(0,1) and w in(0,1) and d in('L','R') and 0<=n<3000
        assert(q,b)not in table
        table[q,b]=(w,1 if d=='R' else -1,n)
    states={q for q,b in table}
    assert len(states)==193 and set(table)=={(q,b)for q in states for b in(0,1)}
    assert {n for w,d,n in table.values()}-states=={254}
    assert 74 in states and 84 in states
    candidates=[json.loads(line)for line in(ROOT/'candidate_rewrites.jsonl').read_text().splitlines()if line.strip()]
    edits=[tuple(map(int,line.split()))for line in(ROOT/'edits.tsv').read_text().splitlines()if line.strip()]
    assert len(candidates)==len(edits)==346
    assert len({(record['state'],record['read'])for record in candidates})==92
    for i,(record,edit)in enumerate(zip(candidates,edits)):
        q,b=record['state'],record['read']
        assert tuple(record['old'])==table[q,b],(i,'old row mismatch')
        assert record['new']!=record['old'],(i,'replacement leaves the row unchanged')
        w,d,n=record['new'];assert w in(0,1)and d in(-1,1)and n in states|{254}
        assert edit==(i,q,b,w,d,n),(i,'edit conversion mismatch')
    seeds=[line.split()for line in(ROOT/'startup_any_frame_templates.tsv').read_text().splitlines()if line.strip()]
    assert [int(pc)for pc,path,mask in seeds]==list(range(25,45))
    assert all(path.startswith('1')and set(path)<=set('01')and int(mask)==511 for pc,path,mask in seeds)
    return provenance,edits

def main():
    if not __debug__:
        raise SystemExit('Verification requires assertions; run without -O.')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--max-edits',type=int,default=3,help='maximum distinct modified rows (default: 3); larger budgets require this explicit option')
    ap.add_argument('--output',type=Path,required=True,help='directory outside this source folder for the executable and replay results')
    a=ap.parse_args()
    if not 0<=a.max_edits<=92:ap.error('--max-edits must be between 0 and 92')
    out=a.output.resolve()
    if out==ROOT or ROOT in out.parents:ap.error('--output must be outside this source directory')
    provenance,edits=validate_inputs()
    recorded={}
    for logfile in sorted(ROOT.glob('run_k*.log')):
        match=re.fullmatch(r'run_k(\d+)\.log',logfile.name)
        if not match:continue
        k=int(match[1]);counts=done_counts(logfile)
        if counts is None:continue # An unfinished optional budget is not a result.
        check_counts(counts,k)
        hits=read_hits(ROOT/f'hits_k{k}.jsonl',edits,k)
        if hits is not None:assert len(hits)==counts['hits'],k
        recorded[k]=counts
    summary_path=ROOT/'summary.json'
    if summary_path.exists():
        summaries=json.loads(summary_path.read_text())
        if isinstance(summaries,list):
            for item in summaries:
                if isinstance(item,dict)and item.get('edits')in recorded:
                    assert {key:item[key]for key in COUNTERS}==recorded[item['edits']],item
    out.mkdir(parents=True,exist_ok=True)
    executable=out/'adaptive_startup'
    with(out/'compile.log').open('w')as log:
        subprocess.run(['g++','-O3','-std=c++17',str(ROOT/'adaptive_startup.cpp'),'-o',str(executable)],stdout=log,stderr=subprocess.STDOUT,check=True)
    k=a.max_edits;logfile=out/f'run_k{k}.log';hitfile=out/f'hits_k{k}.jsonl'
    started=time.monotonic()
    with hitfile.open('w')as hits,logfile.open('w')as log:
        subprocess.run([str(executable),str(ROOT/'runtime193.native.tm'),str(ROOT/'edits.tsv'),str(ROOT/'startup_any_frame_templates.tsv'),str(k),str(BOUND)],stdout=hits,stderr=log,check=True)
    counts=done_counts(logfile);assert counts is not None
    check_counts(counts,k)
    hits=read_hits(hitfile,edits,k);assert len(hits)==counts['hits']
    matched=k in recorded
    if matched:
        assert counts==recorded[k],{'actual':counts,'expected':recorded[k]}
        expected_hits=read_hits(ROOT/f'hits_k{k}.jsonl',edits,k)
        if expected_hits is not None:assert hits==expected_hits
    receipt={'status':'PASS','input_hashes_verified':True,'max_edits':k,'counts':counts,
             'matched_saved_counts':matched,'completed_saved_budgets_checked':sorted(recorded),
             'adaptive_source_sha256':provenance['program']['sha256'],
             'elapsed_seconds':time.monotonic()-started,
             'scope':'Fixed start 74; 346 allowed edits on 92 rows; bounded adaptive bootstrap search. No runtime-neutrality assumption or global nonexistence claim.'}
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
