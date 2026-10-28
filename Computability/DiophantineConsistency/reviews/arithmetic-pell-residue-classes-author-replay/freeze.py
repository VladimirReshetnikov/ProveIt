from pathlib import Path
import hashlib, json, shutil

ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
DC=ROOT/'Computability/DiophantineConsistency'
BUNDLE=DC/'reviews/arithmetic-pell-residue-classes-author-replay'
PACKET=DC/'reviews/arithmetic-pell-residue-classes-replay.json'


def require(ok,message):
    if not ok: raise RuntimeError(message)


def record(path):
    p=Path(path); data=p.read_bytes()
    return dict(path=str(p),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))


def check(pin):
    actual=record(pin['path'])
    require(actual['sha256']==pin['sha256'],'hash '+pin['path'])
    if 'bytes' in pin: require(actual['bytes']==pin['bytes'],'size '+pin['path'])
    return actual


def copy(source,destination):
    destination.parent.mkdir(parents=True,exist_ok=True)
    require(not destination.exists(),'fresh destination '+str(destination))
    shutil.copyfile(source,destination)
    require(record(source)['sha256']==record(destination)['sha256'],'copy bytes')


paths=[Path(p) for p in Path('/tmp/arithmetic-pell-residue-classes-author-runs.txt').read_text().splitlines()]
require(len(paths)==3,'exact three attempts')
states=[json.loads((p/'state.json').read_text()) for p in paths]
require([s['status'] for s in states]==['FAILED','FAILED','PASS'],'attempt chronology')
require(not BUNDLE.exists() and not PACKET.exists(),'fresh bundle and packet')
final=states[-1]; finaldir=paths[-1]
inputs=json.loads((finaldir/'inputs.json').read_text())
plan=json.loads(Path(inputs['plan']['path']).read_text())
require(inputs['counts']==dict(custom=99,Foundation=95,artifacts=384,external=38,
    external_companions=114,fresh_prerequisites=0),'exact closure')
authentication=json.loads((finaldir/'authentication.json').read_text())
for pin in authentication['pins']: check(pin)
snapshots={}
for state in states:
    for rec in state['records']:
        for field in ['snapshot','log','timing']: check(rec[field])
        require(rec['snapshot']['sha256']==rec['source']['sha256'],'source snapshot')
        snapshots[rec['snapshot']['sha256']]=rec['snapshot']
        if 'object' in rec: check(rec['object'])
for p,state in zip(paths,states):
    old=json.loads((p/'inputs.json').read_text())
    for source in old['sources']:
        require(source['sha256'] in snapshots,'historical source snapshot '+source['path'])
    require(record(p/'driver.py')['sha256']==state['driver']['sha256'],'executed driver')
require(states[1]['records'][0]['object']['sha256']==final['records'][0]['object']['sha256'],
        'repeated final main byte equality')
for rec in final['records']:
    check(rec['source']); check(rec['object'])
require(len(final['records'][1]['axiom_reports'])==15,'all fifteen reports')
for name,axioms in final['records'][1]['axiom_reports']:
    require(set(x.strip() for x in axioms.split(','))<=
            {'propext','Classical.choice','Quot.sound'},'standard-only '+name)
BUNDLE.mkdir()
for i,(p,state) in enumerate(zip(paths,states),1):
    dest=BUNDLE/('attempt-'+str(i))
    for name in ['state.json','inputs.json','providers.json','authentication.json','driver.py']:
        copy(p/name,dest/name)
    for rec in state['records']:
        for field in ['snapshot','log','timing']:
            source=Path(rec[field]['path']); copy(source,dest/source.name)
    copy(Path('/tmp/arithmetic-pell-residue-classes-author-attempt'+str(i)+'.log'),dest/'stdout.log')
copy(Path(inputs['plan']['path']),BUNDLE/'plan.json')
copy(Path(inputs['proposal']['path']),BUNDLE/'proposal.md')
copy(Path(__file__),BUNDLE/'freeze.py')
packet=dict(status='PASS',scope='Actual internal IΣ1 x-coordinate residue classes, signed doubled '
    'step-down and odd-index witnesses. No carrier index, strong integrality, cofinality or HA endpoint.',
    counts=inputs['counts'],attempts=[dict(private=str(p),state=record(p/'state.json'),status=s['status'])
        for p,s in zip(paths,states)],records=final['records'],final_private=str(finaldir),
    plan=inputs['plan'],proposal=inputs['proposal'],inputs=record(finaldir/'inputs.json'),
    providers=record(finaldir/'providers.json'),authentication=record(finaldir/'authentication.json'),
    compiler=inputs['compiler'],LEAN_PATH=inputs['LEAN_PATH'],driver=final['driver'],
    final_state=record(finaldir/'state.json'),final_free_bytes=final['final_free_bytes'],
    provider_count=498,final_observed_paths=final['final_observed_paths'],
    reused_main_byte_identical=True,
    historical_note='Attempt1 Checks was not executed; its input bytes are preserved by the identical '
        'attempt2 Checks snapshot. Attempt1 main failed elaboration; attempt2 main passed and Checks '
        'failed only literal model-numeral normalization. No statement, cap or import changed.')
PACKET.write_text(json.dumps(packet,indent=2)+'\n')
print(json.dumps(dict(packet=record(PACKET),bundle=str(BUNDLE),attempts=len(states),
    main=final['records'][0]['source'],checks=final['records'][1]['source'])))
