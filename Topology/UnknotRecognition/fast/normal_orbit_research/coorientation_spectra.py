"""Full spectra against a frozen double-query baseline and component oracle."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import time
from types import ModuleType

from fastunknot.integer_codec import json_safe
from fastunknot.normal_topology import normal_topology_spectrum
from fastunknot.normal_topology_verify import verify_normal_topology_spectrum
from normal_orbit_research import seeds,spectra
from normal_orbit_research.fixtures import layered_torus
from topology_research.benchmark import coordinates_reference,verify_coordinates_reference

ROOT=Path(__file__).resolve().parents[1]
BASELINE='ea366dc9b37fa7ceff6956d144498490ba403bcd'


def baseline():
    modules=[];hashes={}
    for name in ('normal_topology','normal_topology_verify'):
        path='Topology/UnknotRecognition/fast/fastunknot/'+name+'.py'
        source=subprocess.check_output(['git','show',BASELINE+':'+path],cwd=ROOT)
        module=ModuleType('_weighted_coorientation_old_'+name);module.__package__='fastunknot'
        exec(compile(source,BASELINE+':'+path,'exec'),module.__dict__)
        modules.append(module);hashes[name]=sha256(source).hexdigest()
    return modules[0].normal_topology_spectrum,modules[1].verify_normal_topology_spectrum,hashes


def audit(old,old_check):
    rows=[];saved={}
    for i,(case,raw,coords) in enumerate(spectra.corpus()):
        target=spectra.expected(case['expected']['component_records'])
        for reduce in (False,True):
            for rule in ('fine_wilf','aht'):
                options=dict(reduce_core=reduce,periodic_rule=rule,record_certificate=True)
                before=old(raw,coords,**options)
                assert before==normal_topology_spectrum(raw,coords,coorientation=False,**options)
                after=normal_topology_spectrum(raw,coords,**options)
                assert after['status']=='COMPLETE' and after['topology_spectrum']==target
                assert {k:v for k,v in before.items() if k not in ('certificate','stats')}=={
                    k:v for k,v in after.items() if k not in ('certificate','stats')}
                assert old_check(raw,coords,before['certificate'])
                assert verify_normal_topology_spectrum(raw,coords,before['certificate'])
                assert verify_normal_topology_spectrum(raw,coords,after['certificate'])
                derived=after['certificate']['schema']=='normal-topology-spectrum-v2'
                if derived:
                    assert after['nonorientable_components']==0
                    assert after['stats']['queries']==2 and after['stats']['double']['orbit_cycles']==0
                    assert after['stats']['orbit_cycles']==before['stats']['orbit_cycles']-before['stats']['double']['orbit_cycles']
                else:assert after==before
                old_wire,new_wire=seeds.encode(before['certificate']),seeds.encode(after['certificate'])
                rows.append(dict(case_id=case['id'],reduce_core=reduce,periodic_rule=rule,derived=derived,
                    old_cycles=before['stats']['orbit_cycles'],new_cycles=after['stats']['orbit_cycles'],
                    old_bytes=len(old_wire),new_bytes=len(new_wire),spectrum=target))
                key=(case['category'],reduce,rule,derived)
                if key not in saved:
                    saved[key]=dict(case_id=case['id'],triangulation=raw,coordinates=coords,
                                   certificate=after['certificate'],legacy_certificate=before['certificate'])
        if i%200==0:print(i,'of 1275',flush=True)
    return dict(cases=rows,examples=list(saved.values()),legacy_exact_comparisons=len(rows),
        derived=sum(r['derived'] for r in rows),input_vectors=1275,
        component_oracle='independent component records in report 53')


def benchmark(old,old_check,rounds):
    inputs=spectra.inputs();raw,coords=layered_torus(256)
    inputs.append(('layered-256',(raw,coords)))
    cases=[('native/'+n,('native',raw,coords)) for n,(raw,coords) in inputs]
    cases += [('coordinates/'+n,('coordinates',raw,coords)) for n,(raw,coords) in inputs
              if n in ('layered-8','layered-32','layered-64')]

    def run(case,use_old):
        kind,raw,coords=case
        if use_old:
            if kind=='native':answer=old(raw,coords,record_certificate=True);verify=old_check
            else:answer=coordinates_reference(raw,coords,lambda:None);verify=verify_coordinates_reference
        else:answer=normal_topology_spectrum(raw,coords,record_certificate=True);verify=verify_normal_topology_spectrum
        assert answer['status']=='COMPLETE' and verify(raw,coords,answer['certificate'],check=lambda:None)
        wire=seeds.encode(answer['certificate']);signature=seeds.encode(answer['topology_spectrum'])
        return dict(completed=True,spectrum_sha256=sha256(signature).hexdigest(),
            certificate_sha256=sha256(wire).hexdigest(),certificate_bytes=len(wire),
            cycles=answer['stats']['orbit_cycles'],queries=answer['stats']['queries'])
    result=seeds.rounds(cases,run,rounds)
    for row in result['cases']:
        values=[v for s in row['samples']+row['warmups'] for v in s['measurements'].values()]
        assert all(v['completed'] and v['spectrum_sha256']==values[0]['spectrum_sha256'] for v in values)
        for arm in ('old','new'):
            values=[{k:v for k,v in s['measurements'][a].items() if k!='seconds'}
                    for s in row['samples']+row['warmups'] for a in (arm,arm+'_AA')]
            assert all(v==values[0] for v in values)
    return result


def pins():
    return spectra.pins()


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=('audit','benchmark'));parser.add_argument('--rounds',type=int,default=5)
    parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    if args.rounds<1:parser.error('rounds must be positive')
    old,old_check,hashes=baseline();before=pins();started=time.perf_counter()
    result=audit(old,old_check) if args.mode=='audit' else benchmark(old,old_check,args.rounds)
    assert before==pins()
    result.update(source_sha256=before,baseline=BASELINE,baseline_source_sha256=hashes,
                  seconds=time.perf_counter()-started,mode=args.mode)
    args.output.write_text(json.dumps(json_safe(result),indent=2)+'\n')
    print('complete',args.mode,result['seconds'],flush=True)


if __name__=='__main__':main()
