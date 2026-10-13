"""Scratch-only deterministic strict Pachner 3-2 scan; no LP or ray search."""
import gzip
from hashlib import sha256
import json
from pathlib import Path

from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_chain import verify_crushing_chain
from fastunknot.normal_surface_geometry import _prepare, _EDGES, NormalOrbitError
from fastunknot.pachner32 import pachner_32
from fastunknot.pachner32_verify import verify_pachner_32

ROOT=Path('/home/codex/.codex/worktrees/cc5b/Proofs/Topology/UnknotRecognition')
HERE=Path(__file__).resolve().parent


def digest(x):
    return sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()


def pins():
    return {str(p.relative_to(ROOT)):sha256(p.read_bytes()).hexdigest()
            for p in sorted((ROOT/'fast/fastunknot').rglob('*.py'))}


def fixtures():
    path=ROOT/'synthesis/data/boundary-unlayer-audit.json';raw=path.read_bytes();old=json.loads(raw)
    result=[]
    for name in ('trefoil','figure_eight'):
        row=next(r for r in old['diagrams'] if r['id']==name)
        chain=row['arms']['baseline']['result']['certificate']['chain']
        result.append(dict(id=name,input_pd=row['input_pd'],chain=chain,
            historical_input=dict(path=str(path),file_sha256=sha256(raw).hexdigest(),
                selector='diagrams[id='+name+'].arms.baseline.result.certificate.chain',
                source_sha256=old['source_sha256'])))
    path=ROOT/'fast/conflict_composition_research/data/generation/tt-state.json.gz'
    raw=path.read_bytes();old=json.loads(gzip.decompress(raw))
    result.append(dict(id='TT',input_pd=old['input_pd'],chain=old['chain'],
        historical_input=dict(path=str(path),file_sha256=sha256(raw).hexdigest(),
            selector='chain',source_sha256=old['native_sha256'])))
    return result


def candidates(source):
    p=_prepare(source,lambda:None)
    boundary={p['edge_roots'][6*t+i] for t,f in p['boundary_faces']
              for i,(a,b) in enumerate(_EDGES) if a!=f and b!=f}
    occurrences={}
    for i,r in enumerate(p['edge_roots']):occurrences.setdefault(r,[]).append((i//6,*_EDGES[i%6]))
    eligible=sorted((min(v),k,v) for k,v in occurrences.items()
                    if k not in boundary and len(v)==3 and len({t for t,a,b in v})==3)
    return p,[dict(tetrahedron=key[0],vertices=list(key[1:]),edge_root=root,
                   incidences=[list(x) for x in inc]) for key,root,inc in eligible]


def scan(record):
    source=record['chain']['triangulation']
    assert verify_crushing_chain(Diagram.from_pd(record['input_pd']),record['chain'])
    assert _prepare(source,lambda:None)['vertices']==1
    result=dict(record,initial_source=source,initial_source_sha256=digest(source),
                initial_tetrahedra=len(source['tetrahedra']),source_chain_verified=True,
                rounds=[],steps=[])
    while True:
        p,eligible=candidates(source)
        round_record=dict(source_sha256=digest(source),tetrahedra=len(source['tetrahedra']),
                          vertices=p['vertices'],boundary_faces=p['boundary_faces'],
                          eligible_candidates=eligible,attempts=[])
        result['rounds'].append(round_record)
        accepted=None
        for candidate in eligible:
            try:
                move=pachner_32(source,candidate['tetrahedron'],candidate['vertices'])
            except NormalOrbitError as error:
                round_record['attempts'].append(dict(candidate=candidate,status='REJECTED',reason=str(error)))
                continue
            after=move['triangulation']
            verified=verify_pachner_32(source,after,move['certificate'])
            round_record['attempts'].append(dict(candidate=candidate,status='ACCEPTED' if verified else 'VERIFIER_REJECTED'))
            if not verified:continue
            after_prepared=_prepare(after,lambda:None)
            assert after_prepared['vertices']==1
            assert len(after['tetrahedra'])==len(source['tetrahedra'])-1
            step=dict(candidate=candidate,source_sha256=digest(source),
                      successor_sha256=digest(after),successor=after,
                      certificate=move['certificate'],stats=move['stats'],independent_replay=True)
            result['steps'].append(step)
            accepted=after
            break
        if accepted is None:break
        source=accepted
    result.update(final_source=source,final_source_sha256=digest(source),
        final_tetrahedra=len(source['tetrahedra']),terminal_scan_complete=True,
        tetrahedron_trace=[result['initial_tetrahedra']]+[len(s['successor']['tetrahedra']) for s in result['steps']],
        scope='Authenticated initial source plus independently checked relative-boundary Pachner packets; not yet a maintained mixed chain. No Euler-cone, h, or complexity conclusion.')
    return result


def main():
    before=pins();out=dict(schema='scratch-crushing-pachner32-v1',native_sha256=before,
                          records=[],lp_used=False,regina_used=False,passed=False)
    for fixture in fixtures():
        result=scan(fixture);out['records'].append(result)
        print(result['id'],result['tetrahedron_trace'],
              'candidateattempts',sum(len(r['attempts']) for r in result['rounds']),
              'terminaleligible',len(result['rounds'][-1]['eligible_candidates']),flush=True)
        (HERE/'scan.json').write_text(json.dumps(out,sort_keys=True,separators=(',',':'))+'\n')
    assert pins()==before;out['passed']=True;out['native_pins_unchanged']=True
    (HERE/'scan.json').write_text(json.dumps(out,sort_keys=True,separators=(',',':'))+'\n')

if __name__=='__main__':main()
