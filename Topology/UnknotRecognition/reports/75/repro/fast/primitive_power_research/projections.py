"""Source-bound disjoint projection audit and complete recognition measurements."""
import argparse
from hashlib import sha256
import importlib.util
import io
import json
from pathlib import Path
import platform
import random
from statistics import median
import subprocess
import sys
import tarfile
import tempfile
import time
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from fastunknot import Diagram, DiagramError, recognize
from fastunknot.compressed_search import compressed_certificate, _search
from fastunknot.group_certificate import verify_group_certificate
from fastunknot.primitive_projection_verify import replay_compressed_projection, verify_compressed_rank_one
from fastunknot.integer_codec import json_safe
from cyclic_overlap_research.native import stage_records
sys.path.insert(0,str(ROOT/'tests'))
from test_primitive_projection import balanced, inflated_source

BASELINE='e2cf6faa562b857dfe50f29748553c7e198d8add'
CORPUS=ROOT.parent/'reports/46/repo_overlay/Topology/UnknotRecognition/fast/cyclic_overlap_research/results.json'
SEED=261008504


def sources():
    paths=list((ROOT/'fastunknot').rglob('*.py'))+[
        Path(__file__).resolve(),ROOT/'tests/test_primitive_projection.py',
        ROOT/'cyclic_overlap_research/native.py',CORPUS]
    return {str(p.relative_to(ROOT.parent)):sha256(p.read_bytes()).hexdigest() for p in paths}


def baseline(directory):
    prefix='Topology/UnknotRecognition/fast/fastunknot/'
    raw=subprocess.check_output(['git','archive',BASELINE,prefix],cwd=ROOT.parents[2])
    hashes={};directory=Path(directory)
    with tarfile.open(fileobj=io.BytesIO(raw)) as archive:
        for entry in archive:
            if not entry.isfile() or not entry.name.endswith('.py'):continue
            assert entry.name.startswith(prefix)
            relative=entry.name[len(prefix):]
            assert '..' not in Path(relative).parts
            data=archive.extractfile(entry).read()
            target=directory/relative;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
            hashes[relative]=sha256(data).hexdigest()
    spec=importlib.util.spec_from_file_location('_projection_pinned',directory/'__init__.py',submodule_search_locations=[str(directory)])
    package=importlib.util.module_from_spec(spec);sys.modules[spec.name]=package;spec.loader.exec_module(package)
    old_search=__import__(spec.name+'.compressed_search',fromlist=['compressed_certificate'])
    return package,old_search,hashes


def corpus():return json.loads(CORPUS.read_text())['rows']


def capacity():
    rows=[]
    for depth,bits in ((1,128),(3,512),(6,64),(8,32)):
        arena,roots,alive=balanced(depth,bits);moves=[];terminal={}
        initial=dict(nodes=len(arena.rules),rank=len(alive),slots=len(roots),length_bits=max(arena.lengths[r].bit_length() for r in roots))
        with patch.object(arena,'reduce',side_effect=AssertionError),patch.object(arena,'cyclic_reduce',side_effect=AssertionError),patch.object(arena,'expand',side_effect=AssertionError),patch.object(arena,'equal',side_effect=AssertionError):
            assert _search(arena,roots,alive,moves,primitive_terminal=terminal,primitive_projection=True,rank_two_terminal=False)
        other,rr,ll=balanced(depth,bits)
        with patch.object(other,'reduce',side_effect=AssertionError),patch.object(other,'cyclic_reduce',side_effect=AssertionError),patch.object(other,'expand',side_effect=AssertionError),patch.object(other,'equal',side_effect=AssertionError):
            for move in moves:assert replay_compressed_projection(other,rr,ll,move)
            assert verify_compressed_rank_one(other,rr,ll,terminal)
        rows.append(dict(depth=depth,bits=bits,initial=initial,rounds=len(moves),
            final_nodes=len(arena.rules),final_length_bits=max(arena.lengths[r].bit_length() for r in roots),
            retained_slots=len(roots),nonempty_raw_roots=sum(bool(r) for r in roots),stats=arena.stats,
            replay_nodes=len(other.rules),replay_stats=other.stats))
    return dict(cases=rows,scope='Abstract balanced Z presentations with coprime square/cube donor relations. These are algebraic capacity checks with normalization/expansion/equality disabled, not diagram inputs or knot verdicts.')


def audit(old,old_search,hashes):
    inputs=list(corpus());rng=random.Random(SEED)
    for index in range(240):
        strands=rng.randrange(2,6)
        word=[rng.choice((-1,1))*rng.randrange(1,strands) for _ in range(rng.randrange(1,15))]
        try:d=Diagram.from_braid(strands,word)
        except DiagramError:continue
        inputs.append(dict(name=f'random-{index}',pd=d.pd,braid=dict(strands=strands,word=word)))
    for strands in (4,5,9,17,33):
        d=Diagram.from_braid(strands,list(range(1,strands)))
        inputs.append(dict(name=f'stabilized-circle-{strands}',pd=d.pd))
    rows=[]
    for source in inputs:
        options=dict(relator_moves=True,max_work=20_000_000)
        before=old_search.compressed_certificate(old.Diagram.from_pd(source['pd']),**options)
        d=Diagram.from_pd(source['pd']);disabled=compressed_certificate(d,**options)
        assert before==disabled
        stats={};after=compressed_certificate(d,stats=stats,primitive_projection=True,**options)
        if after:
            for compressed in (False,True):assert verify_group_certificate(d,after,compressed=compressed,max_work=20_000_000)
        if after and not before:assert recognize(Diagram.from_pd(source['pd']),use_group=False,seconds=30).status=='UNKNOT'
        rows.append(dict(source=source,old_certificate=before,new_certificate=after,stats=stats))
    inflated=[]
    for bits in (4,128,1024):
        d,c=inflated_source(bits)
        assert verify_group_certificate(d,c,compressed=True,max_work=20_000_000)
        if bits==4:assert verify_group_certificate(d,c,max_work=20_000_000)
        inflated.append(dict(bits=bits,pd=d.pd,certificate=c))
    pairs=[p for r in rows if r['new_certificate'] for m in r['new_certificate']['moves'] if m['kind']=='primitive_projection' for p in m['pairs']]
    return dict(cases=rows,diagrams=len(rows),baseline_source_sha256=hashes,
        projected_certificates=sum(bool(r['new_certificate'] and r['new_certificate']['version']==6) for r in rows),
        projection_pairs=len(pairs),proper_power_pairs=sum(p['exponent']>1 for p in pairs),
        newly_closed=sum(bool(r['new_certificate'] and not r['old_certificate']) for r in rows),
        lost_positives=sum(bool(r['old_certificate'] and not r['new_certificate']) for r in rows),
        inflated_source_cases=inflated,capacity=capacity(),
        scope='Actual validated PDs; current default equals pinned previous producer exactly. Every enabled positive has independent literal and compressed full source replay. Huge-prefix and raw abstract capacity checks are separate; no failed group search is a knotted verdict.')


def benchmark(old,old_search,hashes):
    functions=dict(old=(old.Diagram,old.recognize,False),old_AA=(old.Diagram,old.recognize,False),
        current=(Diagram,recognize,False),current_AA=(Diagram,recognize,False),
        projection=(Diagram,recognize,True),projection_AA=(Diagram,recognize,True))
    rng=random.Random(SEED+1);rows=[];proofs={}
    common=dict(use_group=True,group_relators=True,group_compressed_search=True,
        group_seconds=10,group_max_work=20_000_000,seconds=12,max_objects=50_000)
    for source in corpus():
        samples,warmups=[],[]
        for iteration in range(-1,5):
            order=list(functions);rng.shuffle(order);measurements={}
            for arm in order:
                diagram,recognizer,project=functions[arm];options=dict(common)
                if project:options['group_primitive_projection']=True
                start=time.perf_counter();result=recognizer(diagram.from_pd(source['pd']),**options);elapsed=time.perf_counter()-start
                complete=result.status in ('UNKNOT','KNOTTED')
                if complete:assert result.status==source['expected']
                groups=[]
                for group in stage_records(result.evidence):
                    record={k:v for k,v in group.items() if k!='certificate'}
                    if 'certificate' in group:
                        c=group['certificate'];encoded=json.dumps(json_safe(c),sort_keys=True,separators=(',',':')).encode()
                        key=sha256(encoded).hexdigest();proofs[key]=c
                        record.update(certificate_sha256=key,certificate_bytes=len(encoded),certificate_version=c['version'])
                    groups.append(record)
                measurements[arm]=dict(seconds=elapsed,completed=complete,status=result.status,
                    method=result.method,groups=groups,reason=result.evidence.get('reason'))
            (warmups if iteration<0 else samples).append(dict(order=order,measurements=measurements))
        medians={arm:median([s['measurements'][arm]['seconds'] for s in samples if s['measurements'][arm]['completed']])
                 if any(s['measurements'][arm]['completed'] for s in samples) else None for arm in functions}
        ratios={}
        for label,a,b in [('projection','old','projection'),('default','old','current'),('old_AA','old','old_AA'),('current_AA','current','current_AA'),('projection_AA','projection','projection_AA')]:
            pairs=[s['measurements'][a]['seconds']/s['measurements'][b]['seconds'] for s in samples
                   if s['measurements'][a]['completed'] and s['measurements'][b]['completed']]
            ratios[label]=dict(count=len(pairs),median=median(pairs) if pairs else None)
        rows.append(dict(source=source,samples=samples,warmups=warmups,medians=medians,paired_ratios=ratios))
        print(source['name'],json.dumps(dict(medians=medians,ratios=ratios)),flush=True)
    return dict(cases=rows,certificates=proofs,baseline_source_sha256=hashes,rounds=5,
        measured_calls=len(rows)*30,warmup_calls=len(rows)*6,
        completed_calls=sum(m['completed'] for r in rows for s in r['samples'] for m in s['measurements'].values()),
        scope='Complete fresh PD recognition, including independent source reconstruction and proof replay. Entire previous fastunknot Python package pinned, six shuffled arms with old/current-default/projection A/A controls. Timed-out/stalled calls retained and excluded from complete medians/ratios. No kernel-only ratio is advertised as pipeline speedup.')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=('audit','benchmark'));parser.add_argument('--output',required=True,type=Path)
    args=parser.parse_args();before=sources();start=time.perf_counter()
    with tempfile.TemporaryDirectory(prefix='unknot-projection-baseline-') as directory:
        old,old_search,hashes=baseline(directory)
        result=(audit if args.mode=='audit' else benchmark)(old,old_search,hashes)
    assert before==sources()
    result.update(mode=args.mode,baseline_commit=BASELINE,seed=SEED if args.mode=='audit' else SEED+1,
        seconds=time.perf_counter()-start,python=platform.python_version(),platform=platform.platform(),
        source_sha256=before,source_hashes_unchanged=True)
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(json_safe(result),indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('cases','certificates','source_sha256','baseline_source_sha256','inflated_source_cases','capacity')},indent=2))


if __name__=='__main__':main()
