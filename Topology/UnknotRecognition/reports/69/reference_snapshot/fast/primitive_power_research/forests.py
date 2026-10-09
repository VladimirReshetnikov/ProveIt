"""Unit-coordinate forest audits and complete recognition/group-stage timings."""
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
from fastunknot.group_certificate import verify_group_certificate, group_decide, _presentation, _Budget
from fastunknot.compressed_words import WordArena
from fastunknot.whitehead_power import powered_images
from fastunknot.primitive_forest_verify import replay_compressed_forest
from fastunknot.primitive_projection_verify import replay_compressed_projection, verify_compressed_rank_one
from fastunknot.integer_codec import json_safe
from cyclic_overlap_research.native import stage_records
sys.path.insert(0,str(ROOT/'tests'))
from test_primitive_forest import family
from test_primitive_projection import balanced

BASELINE='7bf6f01026a1fc2f164143d0cb6076132d5a4115'
CORPUS=ROOT.parent/'reports/46/repo_overlay/Topology/UnknotRecognition/fast/cyclic_overlap_research/results.json'
SEED=261008506


def sources():
    paths=list((ROOT/'fastunknot').rglob('*.py'))+[
        Path(__file__).resolve(),ROOT/'tests/test_primitive_projection.py',ROOT/'tests/test_primitive_forest.py',
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
            relative=entry.name[len(prefix):];assert '..' not in Path(relative).parts
            data=archive.extractfile(entry).read();target=directory/relative
            target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
            hashes[relative]=sha256(data).hexdigest()
    spec=importlib.util.spec_from_file_location('_forest_pinned',directory/'__init__.py',submodule_search_locations=[str(directory)])
    package=importlib.util.module_from_spec(spec);sys.modules[spec.name]=package;spec.loader.exec_module(package)
    old_search=__import__(spec.name+'.compressed_search',fromlist=['compressed_certificate'])
    old_group=__import__(spec.name+'.group_certificate',fromlist=['group_decide'])
    assert hashes['compressed_words.py']==sha256((ROOT/'fastunknot/compressed_words.py').read_bytes()).hexdigest()
    return package,old_search,old_group,hashes


def corpus():return json.loads(CORPUS.read_text())['rows']


def capacity(old_search):
    rows=[]
    cases=[('star',64,128),('chain',64,128),('balanced',64,64),('star',256,32)]
    for shape,rank,bits in cases:
        build=lambda:balanced(rank.bit_length()-1,bits) if shape=='balanced' else family(rank,bits,shape)
        result={}
        for mode in ('old_projection','forest'):
            arena,roots,alive=build();initial=dict(rank=rank,slots=len(roots),nodes=len(arena.rules),length_bits=max(arena.lengths[r].bit_length() for r in roots))
            moves=[];terminal={};query=old_search._search if mode=='old_projection' else _search
            opts=dict(primitive_projection=True,rank_two_terminal=False,primitive_terminal=terminal)
            if mode=='forest':opts['primitive_forest']=True
            with patch.object(arena,'reduce',side_effect=AssertionError),patch.object(arena,'cyclic_reduce',side_effect=AssertionError),patch.object(arena,'expand',side_effect=AssertionError),patch.object(arena,'equal',side_effect=AssertionError):
                assert query(arena,roots,alive,moves,**opts)
            other,rr,ll=build()
            with patch.object(other,'reduce',side_effect=AssertionError),patch.object(other,'cyclic_reduce',side_effect=AssertionError),patch.object(other,'expand',side_effect=AssertionError),patch.object(other,'equal',side_effect=AssertionError):
                for move in moves:
                    replay=replay_compressed_forest if move['kind']=='primitive_forest' else replay_compressed_projection
                    assert replay(other,rr,ll,move)
                assert verify_compressed_rank_one(other,rr,ll,terminal)
            result[mode]=dict(initial=initial,rounds=len(moves),final_nodes=len(arena.rules),
                final_length_bits=max(arena.lengths[r].bit_length() for r in roots),retained_slots=len(roots),
                nonempty_raw_roots=sum(bool(r) for r in roots),stats=arena.stats,replay_stats=other.stats,
                certificate_bytes=len(json.dumps(json_safe(dict(moves=moves,terminal=terminal)),separators=(',',':'))))
        rows.append(dict(shape=shape,rank=rank,bits=bits,modes=result))
    return dict(cases=rows,scope='Abstract Z presentations with coprime square/cube donors; no knot verdict or timing claim. Both schedules and replay have normalization, expansion and equality disabled. Work counters compare structural operations on byte-identical word arenas.')


def inflated(bits):
    d=Diagram.from_braid(5,[1,2,3,4]);alive,words=_presentation(d,_Budget(lambda:None,10000,100000))
    arena=WordArena(max_work=20000000);roots=[arena.from_word(w) for w in words];k=1<<bits
    roots=[arena.cyclic_reduce(x) for x in arena.substitute(roots,powered_images(arena,alive,1,{1,2},k))]
    moves=[dict(kind='whitehead_power',multiplier=1,subset=[1,2],exponent=k)];terminal={}
    assert _search(arena,roots,alive,moves,primitive_terminal=terminal,primitive_forest=True)
    c=dict(version=7,method='wirtinger-cyclic-group',status='UNKNOT',input_pd=[list(r) for r in d.pd],moves=moves,terminal=terminal)
    assert verify_group_certificate(d,c,compressed=True,max_work=20000000)
    if bits==4:assert verify_group_certificate(d,c,max_work=20000000)
    return dict(bits=bits,certificate=c)


def audit(old,old_search,old_group,hashes):
    inputs=list(corpus());rng=random.Random(261008504)
    for index in range(240):
        strands=rng.randrange(2,6);word=[rng.choice((-1,1))*rng.randrange(1,strands) for _ in range(rng.randrange(1,15))]
        try:d=Diagram.from_braid(strands,word)
        except DiagramError:continue
        inputs.append(dict(name=f'random-{index}',pd=d.pd,braid=dict(strands=strands,word=word)))
    for strands in (4,5,9,17,33,65):
        d=Diagram.from_braid(strands,list(range(1,strands)));inputs.append(dict(name=f'stabilized-circle-{strands}',pd=d.pd))
    rows=[]
    for source in inputs:
        options=dict(relator_moves=True,max_work=20_000_000);d=Diagram.from_pd(source['pd']);od=old.Diagram.from_pd(source['pd'])
        before=old_search.compressed_certificate(od,**options);assert before==compressed_certificate(d,**options)
        prior=old_search.compressed_certificate(od,primitive_projection=True,**options)
        assert prior==compressed_certificate(d,primitive_projection=True,**options)
        stats={};after=compressed_certificate(d,stats=stats,primitive_forest=True,**options)
        if after:
            for compressed in (False,True):assert verify_group_certificate(d,after,compressed=compressed,max_work=20_000_000)
        if after and not before:assert recognize(Diagram.from_pd(source['pd']),use_group=False,seconds=30).status=='UNKNOT'
        rows.append(dict(source=source,old_certificate=before,old_projection_certificate=prior,new_certificate=after,stats=stats))
    edges=[e for r in rows if r['new_certificate'] for m in r['new_certificate']['moves'] if m['kind']=='primitive_forest' for e in m['edges']]
    return dict(cases=rows,diagrams=len(rows),baseline_source_sha256=hashes,
        forest_certificates=sum(bool(r['new_certificate'] and r['new_certificate']['version']==7) for r in rows),
        forest_edges=len(edges),proper_power_edges=sum(e['proof']['exponent']>1 for e in edges),
        newly_closed=sum(bool(r['new_certificate'] and not r['old_certificate']) for r in rows),
        lost_positives=sum(bool(r['old_certificate'] and not r['new_certificate']) for r in rows),
        inflated_source_cases=[inflated(bits) for bits in (4,128,1024)],capacity=capacity(old_search),
        scope='Actual validated PDs, exact old/default and old-projection/current-projection equality. Every forest-enabled positive has independent literal and compressed source replay. Raw algebraic capacity fixtures and huge-prefix proofs are separate; stalled searches are inconclusive.')


def ratios(samples,pairs):
    result={}
    for label,a,b in pairs:
        values=[s['measurements'][a]['seconds']/s['measurements'][b]['seconds'] for s in samples if s['measurements'][a]['completed'] and s['measurements'][b]['completed']]
        result[label]=dict(count=len(values),median=median(values) if values else None)
    return result


def benchmark(old,old_search,old_group,hashes):
    functions=dict(old=(old.Diagram,old.recognize,{}),old_AA=(old.Diagram,old.recognize,{}),
        old_projection=(old.Diagram,old.recognize,dict(group_primitive_projection=True)),
        old_projection_AA=(old.Diagram,old.recognize,dict(group_primitive_projection=True)),
        current=(Diagram,recognize,{}),current_AA=(Diagram,recognize,{}),
        forest=(Diagram,recognize,dict(group_primitive_forest=True)),forest_AA=(Diagram,recognize,dict(group_primitive_forest=True)))
    rng=random.Random(SEED+1);rows=[];proofs={}
    common=dict(use_group=True,group_relators=True,group_compressed_search=True,group_seconds=10,
        group_max_work=20_000_000,seconds=12,max_objects=50_000)
    for source in corpus():
        samples,warmups=[],[]
        for iteration in range(-1,5):
            order=list(functions);rng.shuffle(order);measurements={}
            for arm in order:
                diagram,recognizer,extra=functions[arm];options=dict(common,**extra)
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
                measurements[arm]=dict(seconds=elapsed,completed=complete,status=result.status,method=result.method,groups=groups,reason=result.evidence.get('reason'))
            (warmups if iteration<0 else samples).append(dict(order=order,measurements=measurements))
        medians={arm:median([s['measurements'][arm]['seconds'] for s in samples if s['measurements'][arm]['completed']]) if any(s['measurements'][arm]['completed'] for s in samples) else None for arm in functions}
        q=ratios(samples,[('forest','old','forest'),('versus_projection','old_projection','forest'),('default','old','current'),('old_AA','old','old_AA'),('old_projection_AA','old_projection','old_projection_AA'),('current_AA','current','current_AA'),('forest_AA','forest','forest_AA')])
        rows.append(dict(source=source,samples=samples,warmups=warmups,medians=medians,paired_ratios=q))
        print(source['name'],json.dumps(dict(medians=medians,ratios=q)),flush=True)
    return dict(cases=rows,certificates=proofs,baseline_source_sha256=hashes,rounds=5,measured_calls=len(rows)*40,warmup_calls=len(rows)*8,
        completed_calls=sum(m['completed'] for r in rows for s in r['samples'] for m in s['measurements'].values()),
        scope='Complete fresh-PD recognition and mandatory independent replay. Entire prior package pinned. Eight shuffled arms: old default, old projection, current default, current forest, each with A/A control. Nondecisions retained and excluded from completed ratios.')


def stages(old,old_search,old_group,hashes):
    functions=dict(old=(old.Diagram,old_group.group_decide,{}),old_AA=(old.Diagram,old_group.group_decide,{}),
        projection=(old.Diagram,old_group.group_decide,dict(primitive_projection=True)),
        projection_AA=(old.Diagram,old_group.group_decide,dict(primitive_projection=True)),
        forest=(Diagram,group_decide,dict(primitive_forest=True)),forest_AA=(Diagram,group_decide,dict(primitive_forest=True)))
    rng=random.Random(SEED+2);rows=[]
    for rank in (8,16,32,64,128):
        pd=Diagram.from_braid(rank+1,list(range(1,rank+1))).pd;samples=[];warmups=[]
        for iteration in range(-1,5):
            order=list(functions);rng.shuffle(order);measurements={}
            for arm in order:
                diagram,decide,extra=functions[arm];opts=dict(seconds=20,max_work=20000000,compressed_search=True,**extra)
                start=time.perf_counter();result=decide(diagram.from_pd(pd),**opts);elapsed=time.perf_counter()-start
                complete=result['status']=='UNKNOT'
                record={k:v for k,v in result.items() if k not in ('seconds','certificate')};c=result.get('certificate')
                if c:record['certificate_bytes']=len(json.dumps(json_safe(c),sort_keys=True,separators=(',',':')).encode())
                measurements[arm]=dict(seconds=elapsed,completed=complete,**record)
            (warmups if iteration<0 else samples).append(dict(order=order,measurements=measurements))
        medians={arm:median([s['measurements'][arm]['seconds'] for s in samples if s['measurements'][arm]['completed']]) if any(s['measurements'][arm]['completed'] for s in samples) else None for arm in functions}
        q=ratios(samples,[('forest','old','forest'),('versus_projection','projection','forest'),('old_AA','old','old_AA'),('projection_AA','projection','projection_AA'),('forest_AA','forest','forest_AA')])
        rows.append(dict(rank=rank,pd=pd,samples=samples,warmups=warmups,medians=medians,paired_ratios=q))
        print(rank,json.dumps(dict(medians=medians,ratios=q)),flush=True)
    return dict(cases=rows,baseline_source_sha256=hashes,rounds=5,measured_calls=len(rows)*30,warmup_calls=len(rows)*6,
        completed_calls=sum(m['completed'] for r in rows for s in r['samples'] for m in s['measurements'].values()),
        scope='Fresh validated actual stabilized-circle PDs through the group stage plus mandatory independent replay only. Bypasses earlier diagram simplification; these timings are not whole-recognizer speedups or hard-unknot evidence. Six shuffled arms and A/A controls; timed nondecisions retained.')


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('mode',choices=('audit','benchmark','stages'));parser.add_argument('--output',required=True,type=Path)
    args=parser.parse_args();before=sources();start=time.perf_counter()
    with tempfile.TemporaryDirectory(prefix='unknot-forest-baseline-') as directory:
        baseline_args=baseline(directory);result=dict(audit=audit,benchmark=benchmark,stages=stages)[args.mode](*baseline_args)
    assert before==sources()
    result.update(mode=args.mode,baseline_commit=BASELINE,seed=SEED+(0 if args.mode=='audit' else 1 if args.mode=='benchmark' else 2),seconds=time.perf_counter()-start,
        python=platform.python_version(),platform=platform.platform(),source_sha256=before,source_hashes_unchanged=True)
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(json_safe(result),indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('cases','certificates','source_sha256','baseline_source_sha256','inflated_source_cases','capacity')},indent=2))


if __name__=='__main__':main()
