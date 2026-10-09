"""Repeat noisy fallback timings without overlapping other CPU jobs."""
from hashlib import sha256
import json
from pathlib import Path
import sys
import time

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.integer_codec import json_safe
from fastunknot.normal_topology import normal_topology_spectrum
from fastunknot.normal_topology_verify import verify_normal_topology_spectrum
from normal_orbit_research import seeds,spectra,coorientation_spectra as driver

old,old_check,hashes=driver.baseline();pins=driver.pins();started=time.perf_counter()
cases=[('native/'+name,(raw,coords)) for name,(raw,coords) in spectra.inputs()
       if name in ('mobius','mixed-components','binary-mixture')]

def run(case,use_old):
    raw,coords=case
    produce,verify=(old,old_check) if use_old else (normal_topology_spectrum,verify_normal_topology_spectrum)
    result=produce(raw,coords,record_certificate=True)
    assert result['status']=='COMPLETE' and verify(raw,coords,result['certificate'])
    assert result['certificate']['schema']=='normal-topology-spectrum-v1'
    wire=seeds.encode(result['certificate']);signature=seeds.encode(result['topology_spectrum'])
    return dict(completed=True,spectrum_sha256=sha256(signature).hexdigest(),
        certificate_sha256=sha256(wire).hexdigest(),certificate_bytes=len(wire),
        cycles=result['stats']['orbit_cycles'],queries=result['stats']['queries'])

result=seeds.rounds(cases,run,15)
for row in result['cases']:
    values=[{k:v for k,v in m.items() if k!='seconds'} for s in row['samples']+row['warmups']
            for m in s['measurements'].values()]
    assert all(v==values[0] for v in values)
assert pins==driver.pins()
result.update(reason='main binary-mixture old A/A median 0.775; retain a longer isolated fallback control',
    source_sha256=pins,baseline=driver.BASELINE,baseline_source_sha256=hashes,
    driver_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),seconds=time.perf_counter()-started)
(ROOT/'synthesis/data/weighted-coorientation-fallback-benchmark.json').write_text(json.dumps(json_safe(result),indent=2)+'\n')
print('complete',result['seconds'])
