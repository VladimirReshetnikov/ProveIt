#!/usr/bin/env python3
"""Read-only source/pin and report-parser controls; launches no process."""
import hashlib,importlib.util,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('Use python3 -I -S -B without optimization')
def need(b,s):
    if not b:raise RuntimeError(s)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
base=Path(__file__).resolve().parents[2]/'research';d=base/'current14-structured-endpoint-coherent-runner'
pins={'runner.py':'3a4b7f117198316969f8e9cdc5a8feb7480c1e96ba8c5c91f55a1710ed1758d3',
      'owned.py':'51f3ec69c2f4a11cfe118072f724a110c976a3557d1c68553ebb6a9c8108f498',
      'extension_supervisor.py':'d757473af0292410aae59b18ff0989269490e47e7d9b32e1e2ac750bf3d551da',
      'controls.py':'9308f1e657b3128425fd04a8dd99e5a6a4f66a05eafad4507d72c41f64b455b4',
      'controls-observation.json':'7423e8513b396f2487525785cc8dab1a46f3a06fbf7393662b369752b5af2426'}
for name,digest in pins.items():need(sha(d/name)==digest,'pin '+name)
control=json.loads((d/'controls-observation.json').read_text())
need(control['status']=='PASS','control status')
for name in ('runner.py','owned.py','extension_supervisor.py','controls.py'):
    need(control['files_sha256'][name]==pins[name],'control pin '+name)
for name in ('owned_success_sample_and_reap','supervisor_wait_retries_and_records_exception','optimized_controls_refused'):
    need(control['controls'][name] is True,'missing control '+name)
need('outside resource bounds' in control['controls']['late_finish_rejected'],'late timeout control')
# Importing the definitions does not invoke main(), compile, or spawn a process.
spec=importlib.util.spec_from_file_location('independent_client_runner_review',d/'runner.py')
r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)
need(r.CLIENTS==[
 ('Current14LiteralPorts',['DiophantineConsistency.CurrentKernel2011','DiophantineConsistency.CurrentMaskRecipes2011'],
 ['Current14LiteralPorts.beta_eq','Current14LiteralPorts.mu_eq','Current14LiteralPorts.omega_eq','Current14LiteralPorts.K_eq','Current14LiteralPorts.all_ports']),
 ('StructuredEndpoint',['Current14LiteralPorts','DiophantineConsistency.IPRAStandardCurrentEndpoint'],
 ['Current14StructuredEndpoint.recipe_endpoint'])],'client lists')
for p,h in r.PINS.items():need(p.is_file() and sha(p)==h,'runner pin '+str(p))
need([sha(p) for p in r.SOURCES]==['b19dfc3f5ea1639dcd6003613cd587992d3ab64f707cbe7c9fb61a466092f8b0','31b2869c63f33610beac36cec7bcbcbcbfc00579b106fbc130ce0f754702a392'],'client source pins')
text=r.SOURCES[1].read_text()
need('theorem recipe_endpoint : ∃ p : Fin 4 → ℤ' in text and 'standardTheory ⊢ noZeroAt p' in text,'endpoint quantifier/derivability scope')
def reject(text,names,part):
    try:r.reports(text,names)
    except Exception as e:
        need(part in str(e),'wrong parser rejection '+repr(e));return True
    raise RuntimeError('report parser accepted '+part)
name='Review.test';good="'Review.test' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
need(r.reports(good,[name])==[(name,'propext, Classical.choice, Quot.sound')],'parser positive')
need(r.reports("'Review.test' does not depend on any axioms\n",[name])==[(name,'')],'parser no-axiom case')
checks={'warning':reject(good+'warning: injected\n',[name],'warning'),
        'wrong_name':reject(good,['Review.other'],'axiom names mismatch'),
        'unexpected_axiom':reject("'Review.test' depends on axioms: [Alien.bad]\n",[name],'unexpected axiom'),
        'duplicate_report':reject(good+good,[name],'axiom names mismatch'),
        'sorryAx':reject(good+'sorryAx\n',[name],'sorry'),
        'error':reject(good+'error: injected\n',[name],'error')}
out={'status':'PASS_SOURCE_AND_PARSER_REVIEW','script_sha256':sha(__file__),
     'files_sha256':pins,'independent_parser_controls':checks,
     'client_source_sha256':{p.name:sha(p) for p in r.SOURCES},
     'scope':'Read-only review and parser tests only; no supervisor, coordinator, client build, independent exit observation or live-base audit.'}
print(json.dumps(out,indent=2,sort_keys=True))
