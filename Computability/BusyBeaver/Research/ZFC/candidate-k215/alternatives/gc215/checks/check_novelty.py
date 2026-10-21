#!/usr/bin/env python3
"""Portable exact rooted-graph comparison with relabeling and reflection.

  python check_novelty.py --table GC215 --corpus CORPUS_DIR \
      --provenance corpus.json --output novelty.json

CORPUS_DIR contains one raw table named SHA256.tm per unique byte string.
The provenance JSON is the399-path census supplied with this package.  The
proof of nonisomorphism uses forced state bijections and literal row mismatch,
not only canonical hashes.  No semantic or worldwide novelty is asserted.
"""
import argparse,hashlib,json
from pathlib import Path
def need(test,message):
    if not test:raise ValueError(message)
def sha(raw):return hashlib.sha256(raw).hexdigest()
def parse(raw):
    T={};start=None
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! start '):need(start is None,'Duplicate start');start=int(line[9:]);continue
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        need((q,b)not in T and b in(0,1)and w in(0,1)and d in('L','R'),'Invalid row')
        T[q,b]=(w,1 if d=='R'else-1,z)
    states={q for q,b in T};halts={z for w,d,z in T.values()}-states
    need(len(states)==215 and len(T)==430 and start in states and len(halts)==1,'Expected complete215-state table')
    need(set(T)=={(q,b)for q in states for b in(0,1)},'Partial table')
    halt=halts.pop();seen={start};queue=[start]
    for q in queue:
        for b in(0,1):
            z=T[q,b][2]
            if z!=halt and z not in seen:seen.add(z);queue.append(z)
    need(seen==states,'Graph-unreachable working state')
    return T,start,halt
def compare(A,B,reflect):
    AT,astart,ahalt=A;BT,bstart,bhalt=B
    mapping={astart:bstart,ahalt:bhalt};inverse={bstart:astart,bhalt:ahalt};queue=[astart]
    paths={astart:''}
    for q in queue:
        nq=mapping[q]
        for read in(0,1):
            aw,ad,az=AT[q,read];bw,bd,bz=BT[nq,read]
            path=paths[q]+str(read)
            if (aw,ad)!=(bw,-bd if reflect else bd):
                return dict(isomorphic=False,reason='write_or_direction_mismatch',access_word=path,
                            candidate_state=q,reference_state=nq,candidate_row=[aw,ad,az],reference_row=[bw,bd,bz])
            if az in mapping:
                if mapping[az]!=bz:return dict(isomorphic=False,reason='forced_map_conflict',access_word=path,
                                               candidate_target=az,forced_reference=mapping[az],actual_reference=bz)
            else:
                if bz in inverse:return dict(isomorphic=False,reason='forced_inverse_conflict',access_word=path,
                                              reference_target=bz,previous_candidate=inverse[bz],new_candidate=az)
                mapping[az]=bz;inverse[bz]=az;paths[az]=path;queue.append(az)
    need(len(mapping)==216 and len(inverse)==216,'Incomplete forced bijection')
    return dict(isomorphic=True,bijection=mapping)
def canonical(A,reflection=False):
    T,start,halt=A;labels={start:0};queue=[start];rows=[]
    for q in queue:
        for b in(0,1):
            w,d,z=T[q,b]
            if z==halt:n=215
            else:
                if z not in labels:labels[z]=len(labels);queue.append(z)
                n=labels[z]
            rows.append([labels[q],b,w,-d if reflection else d,n])
    return sha((json.dumps(rows,separators=(',',':'))+'\n').encode())
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--table',type=Path,required=True);ap.add_argument('--corpus',type=Path,required=True)
    ap.add_argument('--provenance',type=Path,required=True);ap.add_argument('--output',type=Path,required=True)
    a=ap.parse_args();raw=a.table.read_bytes();candidate=parse(raw)
    provenance=json.loads(a.provenance.read_text());paths=provenance['rows']
    expected={r['sha256']for r in paths};files={p.stem:p for p in a.corpus.glob('*.tm')}
    need(set(files)==expected,'Raw representative set differs from provenance')
    need(len(paths)==399 and len(expected)==128,'Pinned corpus census differs')
    checks=[];families=set();computed={}
    for digest,p in sorted(files.items()):
        other_raw=p.read_bytes();need(sha(other_raw)==digest,'Representative filename/hash mismatch')
        other=parse(other_raw);normal=canonical(other);reflected=canonical(other,True)
        computed[digest]=(min(normal,reflected),normal,reflected);families.add(min(normal,reflected))
        direct=compare(candidate,other,False);mirror=compare(candidate,other,True)
        checks.append(dict(reference_sha256=digest,direct=direct,reflected=mirror))
    for r in paths:
        family,normal,reflected=computed[r['sha256']]
        need((family,normal,reflected)==(r['family_key'],r['canonical'],r['reflected']),'Provenance graph hash mismatch')
    need(len(families)==86,'Pinned corpus family census differs')
    matches=[r['reference_sha256']for r in checks if r['direct']['isomorphic']or r['reflected']['isomorphic']]
    receipt=dict(status='NO_ROOTED_GRAPH_OR_REFLECTION_MATCH'if not matches else'EXISTING_GRAPH_FAMILY',
        candidate_sha256=sha(raw),known_paths=len(paths),literal_representatives=len(files),graph_families=len(families),
        provenance_sha256=sha(a.provenance.read_bytes()),matches=matches,comparisons=checks,
        candidate_canonical_sha256=canonical(candidate),candidate_reflected_sha256=canonical(candidate,True),
        checker_sha256=sha(Path(__file__).read_bytes()),
        scope='Pinned repository plus six pending ZIPs. Exact forced-bijection tests preserve start, read symbols, writes, and moves; the second test reverses every move. This is graph novelty, not semantic inequivalence or a literature search.')
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items()if k!='comparisons'},indent=2))
    need(not matches,'Candidate already appears up to state relabeling/reflection')
if __name__=='__main__':main()
