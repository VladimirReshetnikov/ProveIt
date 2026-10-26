"""UNSEALED two_anchor8191 draft: I/O and complete reviewed-input authentication."""
from hashlib import sha256
import json
from pathlib import Path
import shutil
import sys

sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[2]
PAGE=ROOT/'candidates/one-page-compact66-two-anchor8191'
REPO=ROOT.parents[1]
SOURCE_OUTPUTS=['coefficients/beta.bin.gz','coefficients/K.bin.gz','coefficients/MC.bin.gz',
                'coefficients/MF_source.bin.gz','polynomial.json','COEFFICIENT_BINDING.json',
                'CALIBRATION_BINDING.json','SOURCE_INDEX.json']
RENDER_OUTPUTS=['equation.pdf','equation.txt','RENDER.txt','TEX_DIAGNOSTICS.txt','RENDER_DATA.json']
ROLES=['build','source-audit','source-audit-optimized','build-check','build-check-optimized',
       'render','audit','audit-optimized','rerender','rerender-optimized']
FRESH={'build-check','build-check-optimized','audit','audit-optimized','rerender','rerender-optimized'}


def need(ok,message):
    if not ok:raise ValueError(message)


def digest(raw):return sha256(raw).hexdigest()
def encoded(value):return (json.dumps(value,indent=2,sort_keys=True)+'\n').encode()


def pairs(items):
    result={}
    for k,v in items:
        need(k not in result,'duplicate JSON key '+str(k));result[k]=v
    return result


def reject_constant(value):raise ValueError('nonfinite JSON constant '+value)
def decode(raw):return json.loads(raw,object_pairs_hook=pairs,parse_constant=reject_constant)
def load(path):return decode(path.read_bytes())
def pin(raw):return {'bytes':len(raw),'sha256':digest(raw)}


def typed_equal(a,b):
    if type(a) is not type(b):return False
    if type(a) is dict:return set(a)==set(b) and all(typed_equal(a[k],b[k]) for k in a)
    if type(a) is list:return len(a)==len(b) and all(typed_equal(x,y) for x,y in zip(a,b))
    return a==b


def ordinary_context(record):
    """The ENTIRE actual d9c94077c3 record was read before this adapter.

    Its schema/status/source_whole4/both_full_nonauthor_pairs differ from
    comp3. These are literal ACTUAL paths,not a predicted comp3 projection.
    """
    attachment=record.get('ordinary_acceptance')
    need(type(attachment) is dict and set(attachment)=={'path','record','acceptance_record'},
         'DRAFT ONLY: actual TWO-anchor8191 ordinary acceptance is not attached')
    need(attachment['path']=='reviews/compact66-complemented-two-anchor-radix47-mersenne8191-ordinary-acceptance.json',
         'separate ROOT TWO-anchor8191 ordinary acceptance path')
    path=safe(ROOT,attachment['path']);need(pin(path.read_bytes())==attachment['record'],'whole ROOT ordinary acceptance')
    actual=load(path)
    need(type(actual) is dict and typed_equal(actual,attachment['acceptance_record']) and
         actual['schema']=='two_weighted_anchor47_mersenne8191_separate_ROOT_conditional_ordinary_acceptance_v1' and
         actual['status']=='ACCEPTED_CONDITIONAL_ORDINARY_MATHEMATICS',
         'entire actual separate ROOT TWO-anchor8191 ordinary acceptance schema/status')
    sources=actual['source_whole4']
    need(type(sources) is dict and set(sources)=={'MANIFEST.json','README.md','SOURCE_PINS.json','SOURCE_SNAPSHOT.json'} and
         typed_equal(sources['MANIFEST.json'],{'path':'Computability/DiophantineConsistency/research/compact66-complemented-two-anchor-radix47-mersenne8191/MANIFEST.json',
             'bytes':1093,'sha256':'7e1b1057b79c6790a784be7c4a6a7d6cb54492ceb5ae3a73ea24ba758c4deddf'}),
         'exact accepted TWO-anchor8191 whole source association')
    for item in sources.values():
        need(type(item) is dict and set(item)=={'path','bytes','sha256'} and
             pin(safe(REPO,item['path']).read_bytes())=={k:item[k] for k in ['bytes','sha256']},
             'whole actual accepted ordinary source member')
    peer_stem='Computability/DiophantineConsistency/reviews/compact66-complemented-two-anchor-radix47-mersenne8191-ordinary-'
    peers=actual['both_full_nonauthor_pairs']
    need(type(peers) is dict and set(peers)=={peer_stem+suffix for suffix in ['peer.md','peer.json','second-peer.md','second-peer.json']},
         'exact two FULL nonauthor ordinary review pairs')
    for name,item in peers.items():need(pin(safe(REPO,name).read_bytes())==item,'whole actual ordinary peer report')
    return actual


def current_provenance(record):
    """Only four current placed plaintexts and their exact ROOT association.

    The retired ZIP is actual historical Git provenance. It is NEVER opened,
    restored,extracted or treated as a current runtime filesystem input here.
    """
    name='reviews/common-remainders47-retired-archive-provenance-association.json'
    association=load(safe(ROOT,name))
    need(association['schema']=='common_remainders47_retired_archive_ROOT_provenance_association_v1' and
         association['original_archive']['current_path_absent'] is True and
         association['all_other_historical_archive_payloads_not_adopted'] is True,'exact ROOT retired-archive provenance scope')
    need(typed_equal(record['placed_plaintext_provenance'],association['plaintext_bindings']) and
         len(association['plaintext_bindings'])==4,'complete four placed plaintext provenance bindings')
    for row in association['plaintext_bindings']:
        need(type(row['placed_current_path']) is str and row['placed_current_path'].startswith('Computability/DiophantineConsistency/'),
             'repository-relative placed plaintext path')
        raw=safe(REPO,row['placed_current_path']).read_bytes();expected=row['record']
        need(pin(raw)=={k:expected[k] for k in ['bytes','sha256']} and len(raw.splitlines())==expected['lines'],
             'whole current placed plaintext association')
    return association


def controller_context():
    """Fail closed until actual acceptance exists; no invented acceptance schema.

    The final pins must contain the ENTIRE actual acceptance record and a
    reviewed literal field projection into the page's private context below.
    These null draft attachments are NOT a P2 controller certificate. Neither
    this function nor a caller searches for a prime or imports the probe.
    """
    attachment=load(PAGE/'SOURCE_PINS.json').get('accepted_controller')
    need(type(attachment) is dict and set(attachment)=={'acceptance_record','projection','context'},
         'DRAFT ONLY: actual accepted TWO-anchor8191 P2 record and literal projection are not attached')
    path=ROOT/'reviews/compact66-complemented-two-anchor-radix47-mersenne8191-finite-controller-acceptance.json'
    actual=load(path)
    need(type(attachment['acceptance_record']) is dict and typed_equal(actual,attachment['acceptance_record']),
         'entire actual finite-controller acceptance record')
    context=attachment['context'];projection=attachment['projection']
    keys={'ordinary_parent_manifest','evidence_manifest','lambda','kappa','B_order',
          'B_order_factorization','lift','unit_certificates'}
    need(type(context) is dict and set(context)==keys and type(projection) is dict and set(projection)==keys,
         'complete page-private controller context and accepted field projection')
    for key,steps in projection.items():
        need(type(steps) is list and steps and all(type(k) in [str,int] and
             (type(k) is str and k or type(k) is int and k>=0) for k in steps),'literal accepted JSON field path')
        value=actual
        for step in steps:
            need(type(value) is dict and type(step) is str and step in value or
                 type(value) is list and type(step) is int and step<len(value),'defined accepted context path')
            value=value[step]
        need(typed_equal(value,context[key]),'actual acceptance association of controller field '+key)
    need(typed_equal(context['ordinary_parent_manifest'],{'bytes':1093,
         'sha256':'7e1b1057b79c6790a784be7c4a6a7d6cb54492ceb5ae3a73ea24ba758c4deddf'}),
         'exact NEW TWO-anchor8191 ordinary parent')
    for field in ['lambda','kappa','B_order']:
        need(type(context[field]) is int and context[field]>0,'genuine positive controller integer '+field)
    need(context['lambda']>47*8191 and context['lambda']%2==1 and context['kappa']==context['lambda']-1 and
         context['kappa']%299==0 and context['B_order']>2,'complete P2 prime/order spacing context')
    need(type(context['B_order_factorization']) is list and context['B_order_factorization'] and
         all(type(row) is list and len(row)==2 and all(type(v) is int and v>0 for v in row)
             for row in context['B_order_factorization']),'typed complete accepted order factorization')
    lift=context['lift']
    need(type(lift) is dict and set(lift)=={'modulus','residue'} and
         all(type(v) is int for v in lift.values()) and lift['modulus']==context['lambda']**2 and
         0<=lift['residue']<lift['modulus'],'typed accepted lambda-squared lift context')
    rows=context['unit_certificates']
    need(type(rows) is list and len(rows)==3,'all three accepted controller rows')
    for row,prime in zip(rows,[47,8191,context['lambda']]):
        need(type(row) is dict and set(row)=={'prime','rho_mod','B_mod','K_mod','Hctrl_mod','unit'} and
             all(type(row[k]) is int and 0<=row[k]<prime for k in ['rho_mod','B_mod','K_mod','Hctrl_mod']) and
             type(row['prime']) is int and row['prime']==prime and row['unit'] is True and row['Hctrl_mod']!=0,
             'strict entire accepted unit row')
    evidence=context['evidence_manifest']
    need(type(evidence) is dict and set(evidence)=={'bytes','sha256'} and type(evidence['bytes']) is int and
         evidence['bytes']>0 and type(evidence['sha256']) is str and len(evidence['sha256'])==64 and
         all(c in '0123456789abcdef' for c in evidence['sha256']),
         'complete accepted finite evidence identity')
    return context


def safe(base,name):
    need(type(name) is str and name and '\\' not in name,'literal relative POSIX path')
    p=Path(name)
    need(not p.is_absolute() and p.as_posix()==name and all(s not in ['.','..'] for s in p.parts),'canonical relative path without traversal')
    path=base/p
    need(path.resolve()==path.absolute() and all(not a.is_symlink() for a in [path,*path.parents]),'no symbolic path components')
    return path


def authenticate(materialized=False):
    record=load(PAGE/'SOURCE_PINS.json')
    need(record['schema']=='held_complete_two_anchor8191_page_pins_v1','new47 reviewed pins schema')
    need(record.get('preparation_only') is False and type(record.get('ordinary_acceptance')) is dict,
         'DRAFT ONLY: two complete nonauthor reviews and separate ROOT ordinary acceptance are not attached')
    ordinary_context(record)
    hold=load(PAGE/'HOLD_INVENTORY.json')
    need(hold['schema']=='held_complete_two_anchor8191_page_inventory_v1','new47 complete HOLD schema')
    expected=set(hold['files'])|{'HOLD_INVENTORY.json'}
    actual={p.relative_to(PAGE).as_posix() for p in PAGE.rglob('*') if p.is_file()}
    need(expected<=actual and actual-expected<=set(SOURCE_OUTPUTS+RENDER_OUTPUTS),'only reviewed held files and declared outputs')
    for name,item in hold['files'].items():
        need(type(item) is dict and set(item)=={'bytes','sha256'} and type(item['bytes']) is int,'strict HOLD member schema')
        need(pin(safe(PAGE,name).read_bytes())==item,'entire frozen held member '+name)
    for group in ['external_files','own_core']:
        need(type(record[group]) is dict,'complete pin table')
        for name,item in record[group].items():
            need(type(item) is dict and set(item)=={'bytes','sha256'} and type(item['bytes']) is int,'strict source pin schema')
            need(pin(safe(ROOT,name).read_bytes())==item,'whole reviewed source '+name)
    for key in ['preserved_radix55_candidate','preserved_radix53_candidate']:
        preserved=record[key];folder=safe(ROOT,preserved['folder'])
        actual={p.relative_to(folder).as_posix() for p in folder.rglob('*') if p.is_file()}
        need(actual==set(preserved['files']),'entire preserved accepted candidate membership '+key)
        for name,item in preserved['files'].items():
            need(pin(safe(folder,name).read_bytes())==item,'whole preserved predecessor '+key+'/'+name)
    closures=record['closed_dependencies']
    need(type(closures) is list and len({d['folder'] for d in closures})==len(closures),'distinct closed parents')
    for d in closures:
        folder=safe(ROOT,d['folder']);raw=(folder/'MANIFEST.json').read_bytes()
        need(digest(raw)==d['manifest_sha256'],'whole accepted parent seal '+d['folder'])
        entries=load(folder/'MANIFEST.json')['files']
        inventory={p.relative_to(folder).as_posix() for p in folder.rglob('*') if p.is_file() and p!=folder/'MANIFEST.json'}
        need(inventory==set(entries),'whole accepted parent inventory '+d['folder'])
        for name,item in entries.items():
            raw=safe(folder,name).read_bytes()
            need((pin(raw) if type(item) is dict else digest(raw))==item,'whole parent payload '+name)
    for d in record['closed_held_dependencies']:
        folder=safe(ROOT,d['folder']);raw=safe(folder,d['inventory_name']).read_bytes()
        need(digest(raw)==d['inventory_sha256'],'whole retained code-only source seal '+d['folder'])
        entries=decode(raw)['files']
        inventory={p.relative_to(folder).as_posix() for p in folder.rglob('*')
                   if p.is_file() and p!=folder/d['inventory_name']}
        need(inventory==set(entries),'whole retained code-only source inventory '+d['folder'])
        for name,item in entries.items():
            need(pin(safe(folder,name).read_bytes())==item,'whole retained code-only payload '+name)
    for command,item in record['runtime_tools'].items():
        path=Path(sys.executable) if command=='python' else Path(shutil.which(command) or '/nonexistent-reviewed-command')
        need(str(path.resolve())==item['resolved_path'] and pin(path.read_bytes())==item['record'],
             'reviewed executable bytes and command resolution '+command)
    current_provenance(record)
    controller_context()
    if materialized:source_index()
    return record


def source_index():
    index=load(PAGE/'SOURCE_INDEX.json')
    need(set(index)=={'schema','files','producer_sha256','source_pins_sha256'} and
         index['schema']=='two_anchor8191_p66_source_inventory_v1','entire new47 source inventory schema')
    need(set(index['files'])==set(SOURCE_OUTPUTS)-{'SOURCE_INDEX.json'},'all seven complete new47 source payloads')
    for name,item in index['files'].items():need(pin(safe(PAGE,name).read_bytes())==item,'entire new47 materialized source '+name)
    need(index['producer_sha256']==digest((PAGE/'build.py').read_bytes()) and
         index['source_pins_sha256']==digest((PAGE/'SOURCE_PINS.json').read_bytes()),'actual new47 producer and pins')
    return index


def snapshot():
    record=load(PAGE/'SOURCE_PINS.json');paths={PAGE/'SOURCE_PINS.json',PAGE/'HOLD_INVENTORY.json'}
    for group in ['external_files','own_core']:
        paths.update(safe(ROOT,n) for n in record[group])
    for key in ['preserved_radix55_candidate','preserved_radix53_candidate']:
        preserved=record[key];folder=safe(ROOT,preserved['folder'])
        paths.update(safe(folder,n) for n in preserved['files'])
    for d in record['closed_dependencies']:
        folder=safe(ROOT,d['folder']);paths.add(folder/'MANIFEST.json')
        paths.update(safe(folder,n) for n in load(folder/'MANIFEST.json')['files'])
    for d in record['closed_held_dependencies']:
        folder=safe(ROOT,d['folder']);paths.add(safe(folder,d['inventory_name']))
        paths.update(safe(folder,n) for n in load(folder/d['inventory_name'])['files'])
    paths.update(safe(PAGE,n) for n in SOURCE_OUTPUTS+RENDER_OUTPUTS if (PAGE/n).exists())
    return {str(p):pin(p.read_bytes()) for p in sorted(paths)}


def unchanged(before,allowed=()):
    authenticate()
    excluded={str(safe(PAGE,n)) for n in allowed}
    after=snapshot()
    need({p:v for p,v in before.items() if p not in excluded}==
         {p:v for p,v in after.items() if p not in excluded},'complete before/after reviewed-input bytes unchanged')


def receipt_path(role,path):
    need(role in ROLES,'declared receipt role')
    permitted={Path('/tmp/two-anchor8191-page-'+role+'.json')}
    if role in FRESH:permitted.add(Path('/tmp/two-anchor8191-page-root-'+role+'.json'))
    need(path in permitted and path.absolute()==path.resolve() and not path.is_symlink() and
         not path.exists() and path.parent==Path('/tmp'),'fixed fresh external receipt path')
    return path


def receipt(role,raw,path):
    receipt_path(role,path)
    with path.open('xb') as out:out.write(raw)
    print(raw.decode(),end='')
