"""Audit optional boundary classification and measure its adaptive cone queries."""
import argparse
from contextlib import nullcontext
import hashlib
import importlib
from itertools import product
import json
from pathlib import Path
import platform
import random
import statistics
import subprocess
import sys
import time
import types
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from fastunknot import normal_surface_orbits as producer
from fastunknot.integer_codec import json_safe
from fastunknot.normal_surface_geometry import _TOPOLOGY_FIELDS, _BOUNDARY_FIELDS
from fastunknot.normal_surface_verify import verify_normal_surface_certificate as verify
from normal_orbit_research.fixtures import (
    layered_torus, boundary_cap, interior_vertex_torus, regina_triangulation,
    regina_surface, export_surface,
)

BASELINE = 'ce180ce1e64036f5724343e07a7f16dd7afa8225'
SEED = 261008503
ARCHIVE = ROOT.parent/'reports/47/snapshot/Topology/UnknotRecognition/fast/fastunknot'
RP2 = ROOT/'normal_orbit_research/data/projective_plane_torus.json'
AUDIT_INPUT = ROOT.parent/'synthesis/data/normal-certificate-native-audit.json'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def sources():
    paths = list((ROOT/'fastunknot').glob('*.py'))
    paths += [Path(__file__).resolve(), ROOT/'normal_orbit_research/fixtures.py',
              ROOT/'tests/test_normal_boundary.py', RP2, AUDIT_INPUT]
    paths += list(ARCHIVE.glob('*.py'))
    return {str(p.relative_to(ROOT.parent)): digest(p.read_bytes()) for p in paths}


def pinned():
    modules, hashes = [], {}
    for name in ('normal_surface_orbits', 'normal_surface_verify'):
        data = subprocess.check_output(['git', 'show', BASELINE +
            ':Topology/UnknotRecognition/fast/fastunknot/' + name + '.py'], cwd=ROOT)
        module = types.ModuleType('fastunknot._boundary_old_' + name)
        module.__package__ = 'fastunknot'
        exec(compile(data, BASELINE + ':' + name, 'exec'), module.__dict__)
        modules.append(module)
        hashes[name] = digest(data)
    return *modules, hashes


def combination(basis, weights):
    return [[sum(w*s[t][j] for w,s in zip(weights,basis)) for j in range(7)]
            for t in range(len(basis[0]))]


def topology(result, boundary=True):
    fields = _TOPOLOGY_FIELDS + (_BOUNDARY_FIELDS if boundary else ())
    return {k:result[k] for k in fields if k in result}


def force_cones():
    original = producer._classify_boundary
    def forced(*args, **kwargs):
        return original(*args, **kwargs, shortcuts=False)
    return patch.object(producer, '_classify_boundary', forced)


def audit():
    import regina
    old, old_check, hashes = pinned()
    package = types.ModuleType('_report47_boundary_audit')
    package.__path__ = [str(ARCHIVE)]
    sys.modules[package.__name__] = package
    reference = importlib.import_module(package.__name__ + '.normal_components')
    assert digest((ARCHIVE/'normal_components.py').read_bytes()) == '6e24cca28c374f47d4e9bddeae64b21f7a51399038f526e445610062a2798b5e'
    assert digest((ARCHIVE/'normal_interval_extraction.py').read_bytes()) == 'f5f04c611d23ea1a1d492e138df6e406e1d98863e5144f9ea6553e2ce4aaf859'
    inputs = []
    for source in json.loads(AUDIT_INPUT.read_text())['cases']:
        raw, meridian = layered_torus(1 if source.get('boundary_caps') else source['tetrahedra'])
        for _ in range(source.get('boundary_caps', 0)):
            raw, meridian = boundary_cap(raw, meridian)
        inputs.append(('layered_torus', raw, source['coordinates']))
    raw, basis = interior_vertex_torus()
    for weights in product(range(4), repeat=3):
        inputs.append(('interior_vertex', raw, combination(list(basis.values()),weights)))
    fixture = json.loads(RP2.read_text())
    raw = fixture['triangulation']
    tri = regina_triangulation(raw)
    base = [export_surface(s) for s in regina.NormalSurfaces(tri, regina.NS_STANDARD)]
    for vector in base:
        inputs.append(('torus_sum_RP3_vertex',raw,vector))
    for a,b in product(range(4),repeat=2):
        inputs.append(('torus_sum_RP3_mixed',raw,combination(
            [fixture['coordinates'],fixture['boundary_disk']],(a,b))))
    rng = random.Random(SEED)
    for _ in range(100):
        a,b = rng.choice(base),rng.choice(base)
        if any(sum(bool(x or y) for x,y in zip(u[4:],v[4:])) > 1 for u,v in zip(a,b)):
            continue
        inputs.append(('torus_sum_RP3_compatible',raw,combination([a,b],(rng.randrange(1,4),rng.randrange(1,4)))))
    rows=[]
    for name,raw,vector in inputs:
        before = old.normal_surface_topology(raw,vector,record_certificate=True)
        default = producer.normal_surface_topology(raw,vector,record_certificate=True)
        assert before == default
        assert verify(raw,vector,before['certificate'])
        assert old_check.verify_normal_surface_certificate(raw,vector,default['certificate'])
        actual = producer.normal_surface_topology(raw,vector,classify_boundary=True,record_certificate=True)
        with force_cones():
            direct = producer.normal_surface_topology(raw,vector,classify_boundary=True,record_certificate=True)
        assert topology(actual) == topology(direct)
        assert topology(actual,False) == topology(before,False)
        assert verify(raw,vector,actual['certificate']) and verify(raw,vector,direct['certificate'])
        report = reference.analyze_normal_surface(raw,vector,record_trace=True)
        assert reference.verify_normal_surface_certificate(raw,vector,report['certificate'])
        for key in _BOUNDARY_FIELDS:
            assert actual[key] == report['summary'][key],(name,key)
        surface=regina_surface(regina_triangulation(raw),vector)
        parts=surface.components()
        ob=sum(s.hasRealBoundary() and s.isOrientable() for s in parts)
        nb=sum(s.hasRealBoundary() and not s.isOrientable() for s in parts)
        oc=sum(not s.hasRealBoundary() and s.isOrientable() for s in parts)
        nc=sum(not s.hasRealBoundary() and not s.isOrientable() for s in parts)
        expected=dict(components=len(parts),orientable_components=ob+oc,nonorientable_components=nb+nc,
            boundary_components=surface.countBoundaries(),euler_characteristic=int(str(surface.eulerChar())),
            components_with_boundary=ob+nb,closed_components=oc+nc,
            orientable_components_with_boundary=ob,nonorientable_components_with_boundary=nb,
            closed_orientable_components=oc,closed_nonorientable_components=nc)
        assert all(actual[k] == value for k,value in expected.items()),(name,vector,expected,topology(actual))
        rows.append(dict(family=name,triangulation=raw,coordinates=vector,topology=topology(actual),
            adaptive_queries=list(actual['queries']),direct_queries=list(direct['queries']),
            adaptive_cycles=actual['cycles'],direct_cycles=direct['cycles']))
    return dict(cases=rows,comparisons=len(rows),baseline_source_sha256=hashes,
                regina_version=regina.versionString(),
                classes={k:sum(r['topology'][k]>0 for r in rows) for k in _BOUNDARY_FIELDS},
                queries={str(q):sum(len(r['adaptive_queries'])==q for r in rows) for q in (3,4,5)},
                scope='Native finite triangulations and supplied vectors; RP3 connected sum is deliberately not a knot exterior. Regina decomposition and delivered report47 agree with all six new fields. Default outputs and proofs equal actual baseline exactly.')


def benchmark():
    old, old_check, hashes = pinned()
    cases=[('meridian'+str(t),*layered_torus(t),1 if t>=32 else 5) for t in (8,32,96)]
    raw,vector=layered_torus(8)
    cases.append(('parallel5000',raw,[[v*(1<<5000) for v in row] for row in vector],3))
    raw,basis=interior_vertex_torus()
    for name,weights in [('closed',(1,0,0)),('one_boundary',(1,0,1)),('pure_orientable',(1,2,0)),
                         ('mixed_odd',(1,1,1)),('mixed_even',(2,2,2)),
                         ('mixed_even5000',((1<<5000),)*3),('mixed_odd5000',((1<<5000)+1,)*3)]:
        cases.append((name,raw,combination(list(basis.values()),weights),5))
    fixture=json.loads(RP2.read_text())
    cases.append(('closed_one_sided',fixture['triangulation'],
        combination([fixture['coordinates'],fixture['boundary_disk']],(3,2)),3))
    rows=[]
    arms=('direct','direct_AA','adaptive','adaptive_AA','direct_certified','adaptive_certified','old_default','new_default')
    rng=random.Random(SEED+1)
    for name,raw,vector,batch in cases:
        adaptive=producer.normal_surface_topology(raw,vector,classify_boundary=True,record_certificate=True)
        with force_cones():
            direct=producer.normal_surface_topology(raw,vector,classify_boundary=True,record_certificate=True)
        expected=topology(adaptive)
        assert expected==topology(direct)
        assert verify(raw,vector,adaptive['certificate']) and verify(raw,vector,direct['certificate'])
        assert old.normal_surface_topology(raw,vector,record_certificate=True)==producer.normal_surface_topology(raw,vector,record_certificate=True)
        def call(arm):
            if arm=='old_default':return old.normal_surface_topology(raw,vector)
            if arm=='new_default':return producer.normal_surface_topology(raw,vector)
            certified=arm.endswith('_certified')
            result=producer.normal_surface_topology(raw,vector,classify_boundary=True,record_certificate=certified)
            if certified:assert verify(raw,vector,result['certificate'])
            return result
        samples,warmups=[],[]
        for round_id in range(-1,5):
            order=list(arms);rng.shuffle(order);times={}
            for arm in order:
                # Bind the ablation outside timing. Both arms still reconstruct
                # all geometry, markings and queries on every measured call.
                with force_cones() if arm.startswith('direct') else nullcontext():
                    start=time.perf_counter()
                    for _ in range(batch):result=call(arm)
                    times[arm]=(time.perf_counter()-start)/batch
                assert topology(result,not arm.endswith('default'))==(
                    expected if not arm.endswith('default') else topology(adaptive,False))
            (warmups if round_id<0 else samples).append(dict(order=order,seconds=times))
        medians={arm:statistics.median(r['seconds'][arm] for r in samples) for arm in arms}
        ratios={label:statistics.median(r['seconds'][a]/r['seconds'][b] for r in samples)
                for label,a,b in [('count','direct','adaptive'),('certified','direct_certified','adaptive_certified'),
                                 ('direct_AA','direct','direct_AA'),('adaptive_AA','adaptive','adaptive_AA'),
                                 ('default','old_default','new_default')]}
        def info(result):
            proof=result['certificate']
            return dict(queries=result['queries'],cycles=result['cycles'],
                proof_bytes=len(json.dumps(json_safe(proof),separators=(',',':')).encode()),
                events=sum(len(q['operations']) for q in proof['queries'].values()))
        rows.append(dict(name=name,triangulation=raw,coordinates=vector,batch=batch,
            topology=expected,adaptive=info(adaptive),direct=info(direct),
            samples=samples,warmups=warmups,medians=medians,paired_ratios=ratios))
        print(name,json.dumps(dict(medians=medians,paired_ratios=ratios)),flush=True)
    return dict(cases=rows,rounds=5,excluded_warmups=1,baseline_source_sha256=hashes,
        measured_calls=sum(r['batch']*len(arms)*5 for r in rows),warmup_calls=sum(r['batch']*len(arms) for r in rows),
        scope='Fresh finite manifold/normal-coordinate validation and complete boundary classification in direct/adaptive arms; certified includes production and independent replay. Old/new default controls compute the smaller unchanged feature set and are not speedup baselines for classification. Multiplicity reduction enabled in both policies. No vector search, PD recognition or serialization is timed.')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=('audit','benchmark'))
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    before=sources();start=time.perf_counter()
    result=(audit if args.mode=='audit' else benchmark)()
    assert before==sources()
    result.update(mode=args.mode,seed=SEED if args.mode=='audit' else SEED+1,
        baseline_commit=BASELINE,seconds=time.perf_counter()-start,python=platform.python_version(),
        platform=platform.platform(),source_sha256=before,source_hashes_unchanged=True)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(json_safe(result),indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('cases','source_sha256')},indent=2))


if __name__=='__main__':main()
