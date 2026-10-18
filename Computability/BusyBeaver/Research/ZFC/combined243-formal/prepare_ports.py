#!/usr/bin/env python3
"""Own source-only mechanical ports; no Lean/compiler or supplied-code execution."""
from pathlib import Path
import hashlib,json,re,difflib
B=Path(__file__).resolve().parent
def d(p):return {'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
def translate(text,nums):
    words={'Routing245':'Rotation244','Compensated244':'Combined243',
      'compensated244_common':'combined243_common','exceptionalRow244':'exceptionalRow243',
      'embedState244':'embedState243','embedAction244':'embedAction243','embedConfig244':'embedConfig243'}
    # Simultaneous numeric substitutions preserve old/new state-count distinction.
    text=re.sub(r'\b(245|244)\b',lambda m:nums.get(m.group(),m.group()),text)
    return re.sub('|'.join(map(re.escape,sorted(words,key=len,reverse=True))),lambda m:words[m.group()],text)
specs=[
 ('invariant',Path('/tmp/zfc244-routing245-invariant'),'Routing245Invariant','Rotation244Invariant',{'245':'244'},
  'The local predecessor invariant for the rotated244 table.\n'
  'This is a source-only port of the checked original Routing245 invariant.\n'
  'Its incoming rows68/81/167 are unchanged by the QT rotation.\n'
  'Every Core configuration (arbitrary finite-support tape) and natural duration\n'
  'is quantified; no register-frame or runtime hypothesis is introduced.\n'
  'The new table/provider and this port await independent kernel checking.'),
 ('blocks',Path('/tmp/zfc244-compensated-lean/blocks'),'Compensated244Blocks','Combined243Blocks',{'245':'244','244':'243'},
  'Seven literal positive-block identities comparing Rotation244 and Combined243.\n'
  'This is a source-only port of the checked compensated244 block calculations.\n'
  'All row dependencies are unaffected by the QT edit/delete26. Every unspecified\n'
  'tape cell and the exact list representation are retained. Explicit read\n'
  'premises are supplied by Rotation244Invariant at the167 and81 entries.\n'
  'No global simulation or actual kernel acceptance is asserted here.'),
 ('simulation',Path('/tmp/zfc244-compensated-lean/simulation'),'Compensated244Simulation','Combined243Simulation',{'245':'244','244':'243'},
  'Concrete positive-block simulation of Combined243 against Rotation244.\n'
  'Source-only mechanical port of the checked compensated244 simulation.\n'
  'The relation retains the old-side local tape invariant and excludes old92\n'
  'from paired endpoints; old122 is absent from the new state set.\n'
  'The imported generic PositiveBlockBisimulation remains unchanged.\n'
  'Results concern arbitrary finite-support Core tapes, including blank.\n'
  'No calibration of Rotation244, completed kernel proof, or PA endpoint is claimed.')]
manifest={'status':'SOURCE_ONLY_PORTS_UNBUILT','compiler_invoked':False,'units':[]}
for folder,parent,oldmod,newmod,nums,doc in specs:
    out=B/folder;out.mkdir(exist_ok=True)
    source=parent/(oldmod+'.lean');audit=parent/'Audit.lean'
    old=source.read_text();new=translate(old,nums)
    new=re.sub(r'/\-!.*?\-/',lambda m:'/-!\n'+doc+'\n-/',new,count=1,flags=re.S)
    # Fully qualify every printed declaration, including inherited short probes.
    aud=translate(audit.read_text(),nums)
    aud=re.sub(r'(?m)^#print axioms (\w+)$',lambda m:'#print axioms SetTheory.BusyBeaver.ZFC.'+newmod+'.'+m.group(1),aud)
    for n,t in [(newmod+'.lean',new),('Audit.lean',aud)]:
        target=out/n
        assert not target.exists(),target
        target.write_text(t)
    (out/'source-port.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile=str(source),tofile=str(out/(newmod+'.lean')))))
    (out/'audit-port.diff').write_text(''.join(difflib.unified_diff(audit.read_text().splitlines(True),aud.splitlines(True),fromfile=str(audit),tofile=str(out/'Audit.lean'))))
    # Inverse equality outside the documentary module comment is exact.
    clean=lambda t:re.sub(r'/\-!.*?\-/','',t,count=1,flags=re.S)
    assert clean(new)==clean(translate(old,nums))
    probes=re.findall(r'^#print axioms (.+)$',aud,re.M)
    assert all(p.startswith('SetTheory.BusyBeaver.ZFC.'+newmod+'.') for p in probes)
    assert not re.search(r'\b(sorry|axiom|set_option)\b',clean(new))
    manifest['units'].append({'name':newmod,'source':d(out/(newmod+'.lean')),'audit':d(out/'Audit.lean'),
      'passed_predecessor_source':d(source),'passed_predecessor_audit':d(audit),
      'source_diff':d(out/'source-port.diff'),'audit_diff':d(out/'audit-port.diff'),
      'probes':len(probes),'callers':len(re.findall(r'^example\b',aud,re.M)),
      'qualified_probes':probes,'numeric_state_count_substitutions':nums,
      'proof_body_change':'Only module/machine/embedding/row-lemma names and machine-state types; documentary header replaced. Invariant probe names fully qualified.'})

alltext='\n'.join((B/u['name'].replace('Rotation244Invariant','invariant').replace('Combined243Blocks','blocks').replace('Combined243Simulation','simulation')/(u['name']+'.lean')).read_text() for u in manifest['units'])
external=sorted(set(re.findall(r'\b(?:foldRow(?:Rotation244|Combined243)_old\d+_(?:true|false)|embedState243_old\d+|combined243_common_(?:action|next)|exceptionalRow243|embedConfig243_initial)\b',alltext)))
manifest['expected_table_api']=external
manifest['pending_parents']=['BusyBeaver.ZFC.TableRotation244','BusyBeaver.ZFC.TableCombined243']
manifest['existing_generic_parent']='BusyBeaver.ZFC.PositiveBlockBisimulation (unchanged checked theorem)'
manifest['scope']='All finite-support Core tapes from old95; blank halting equivalence Rotation244↔Combined243 only. No source-calibration bridge or PA internalization.'
manifest['emitter']=d(Path(__file__))
(B/'source-inventory.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(d(B/'source-inventory.json'),indent=2))
