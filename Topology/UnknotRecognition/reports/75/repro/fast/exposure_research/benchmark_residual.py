"""Paired native Gordian audit: existing search versus exposure-residual handoff."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import platform
import random
import statistics
from time import monotonic,perf_counter

from residual_bridge import FAST,REPO,load_delivery,residual_probe
from fastunknot import Diagram
from fastunknot.group_certificate import group_certificate,verify_group_certificate,GroupLimit
from fastunknot.compressed_search import compressed_certificate


def incumbent(pd,mode):
    start=monotonic();stats={}
    def tick():
        if monotonic()-start>=15:raise GroupLimit('incumbent wall allowance exhausted')
    try:
        tick();d=Diagram.from_pd(pd);tick()
        kw=dict(check=tick,max_work=20000000,max_letters=200000,max_nodes=100000,
                relator_moves=True,stats=stats)
        if mode=='compressed':cert=compressed_certificate(d,**kw)
        else:cert=group_certificate(d,adaptive=mode=='adaptive',
                switch_letters=20000 if mode=='adaptive' else None,**kw)
        if cert is None:return dict(status='INCONCLUSIVE',reason='stalled',stats=stats)
        for compressed in (False,True):
            assert verify_group_certificate(d,cert,check=tick,max_work=20000000,
                max_letters=600000,max_nodes=100000,compressed=compressed)
        tick()
        return dict(status='UNKNOT',certificate=cert,stats=stats)
    except GroupLimit as e:return dict(status='INCONCLUSIVE',reason=str(e),stats=stats)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--certificate',type=Path,required=True)
    args=ap.parse_args()
    source=FAST/'normal_research/gordian.json';pd=json.loads(source.read_text())['pd']
    paths=[Path(__file__),FAST/'exposure_research/residual_bridge.py',source,*sorted((FAST/'fastunknot').glob('*.py'))]
    hashes={str(p.relative_to(REPO)):sha256(p.read_bytes()).hexdigest() for p in paths}
    rng=random.Random(261008113);samples=[];cert_hashes={};last=None
    with load_delivery():
        for round_number in range(6):
            order=['explicit','control','compressed','adaptive','exposure_overlap'];rng.shuffle(order)
            for arm in order:
                start=perf_counter()
                result=residual_probe(pd) if arm=='exposure_overlap' else incumbent(pd,'explicit' if arm=='control' else arm)
                elapsed=perf_counter()-start
                cert=result.pop('certificate',None)
                if cert is not None:
                    digest=sha256(json.dumps(cert,sort_keys=True,separators=(',',':')).encode()).hexdigest()
                    if arm in cert_hashes:assert cert_hashes[arm]==digest
                    cert_hashes[arm]=digest
                    if arm=='exposure_overlap':last=cert
                else:digest=None
                samples.append(dict(round=round_number,warmup=round_number==0,arm=arm,order=order,
                    seconds=elapsed,certificate_sha256=digest,result=result))
            print('completed round',round_number,flush=True)
    for p in paths:assert sha256(p.read_bytes()).hexdigest()==hashes[str(p.relative_to(REPO))]
    summary={}
    for arm in order:
        rows=[r for r in samples if r['arm']==arm and not r['warmup']]
        summary[arm]=dict(statuses=sorted({r['result']['status'] for r in rows}),
            median_seconds=statistics.median(r['seconds'] for r in rows),
            paired_explicit_ratio=statistics.median(next(s['seconds'] for s in samples if s['arm']=='explicit' and s['round']==r['round'])/r['seconds'] for r in rows)
                if all(r['result']['status']=='UNKNOT' for r in samples) else None)
    result=dict(seed=261008113,python=platform.python_version(),source_sha256=hashes,input_crossings=len(pd),
        scope='Fresh native PD validation, complete search and two independent replay modes. Search allowance is 20 million work units, each verifier has its own 20 million, with one shared 15-second wall cap. All arms allow 600000 replay letters. Exposure allows 3M temporary Whitehead workspace; explicit search retains its existing M workspace limit. Archive imports and JSON serialization excluded.',
        measured=25,warmups=5,summary=summary,samples=samples,certificate_hashes=cert_hashes)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    if last is not None:args.certificate.write_text(json.dumps(last,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':main()
