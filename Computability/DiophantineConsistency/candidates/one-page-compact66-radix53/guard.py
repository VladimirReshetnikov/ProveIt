"""Held radix53 page I/O and complete reviewed-input authentication only."""
from hashlib import sha256
import json
from pathlib import Path
import shutil
import sys

sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[2]
PAGE=ROOT/'candidates/one-page-compact66-radix53'
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


def safe(base,name):
    need(type(name) is str and name and '\\' not in name,'literal relative POSIX path')
    p=Path(name)
    need(not p.is_absolute() and p.as_posix()==name and all(s not in ['.','..'] for s in p.parts),'canonical relative path without traversal')
    path=base/p
    need(path.resolve()==path.absolute() and all(not a.is_symlink() for a in [path,*path.parents]),'no symbolic path components')
    return path


def authenticate(materialized=False):
    record=load(PAGE/'SOURCE_PINS.json')
    need(record['schema']=='held_complete_radix53_page_pins_v1','new53 reviewed pins schema')
    hold=load(PAGE/'HOLD_INVENTORY.json')
    need(hold['schema']=='held_complete_radix53_page_inventory_v1','new53 complete HOLD schema')
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
    preserved=record['preserved_radix55_candidate']
    folder=safe(ROOT,preserved['folder'])
    actual={p.relative_to(folder).as_posix() for p in folder.rglob('*') if p.is_file()}
    need(actual==set(preserved['files']),'entire preserved accepted radix55 candidate membership')
    for name,item in preserved['files'].items():
        need(pin(safe(folder,name).read_bytes())==item,'whole preserved radix55 predecessor '+name)
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
    if materialized:source_index()
    return record


def source_index():
    index=load(PAGE/'SOURCE_INDEX.json')
    need(set(index)=={'schema','files','producer_sha256','source_pins_sha256'} and
         index['schema']=='radix53_p66_source_inventory_v1','entire new53 source inventory schema')
    need(set(index['files'])==set(SOURCE_OUTPUTS)-{'SOURCE_INDEX.json'},'all seven complete new53 source payloads')
    for name,item in index['files'].items():need(pin(safe(PAGE,name).read_bytes())==item,'entire new53 materialized source '+name)
    need(index['producer_sha256']==digest((PAGE/'build.py').read_bytes()) and
         index['source_pins_sha256']==digest((PAGE/'SOURCE_PINS.json').read_bytes()),'actual new53 producer and pins')
    return index


def snapshot():
    record=load(PAGE/'SOURCE_PINS.json');paths={PAGE/'SOURCE_PINS.json',PAGE/'HOLD_INVENTORY.json'}
    for group in ['external_files','own_core']:
        paths.update(safe(ROOT,n) for n in record[group])
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
    permitted={Path('/tmp/radix53-page-'+role+'.json')}
    if role in FRESH:permitted.add(Path('/tmp/radix53-page-root-'+role+'.json'))
    need(path in permitted and path.absolute()==path.resolve() and not path.is_symlink() and
         not path.exists() and path.parent==Path('/tmp'),'fixed fresh external receipt path')
    return path


def receipt(role,raw,path):
    receipt_path(role,path)
    with path.open('xb') as out:out.write(raw)
    print(raw.decode(),end='')
