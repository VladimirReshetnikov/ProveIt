#!/usr/bin/env python3
"""Emit only the next serial exact246 bootstrap group; generated data are untrusted."""
from pathlib import Path
import argparse, hashlib, json, re
HERE=Path(__file__).resolve().parent
REPO=Path('/home/codex/.codex/worktrees/ec20/Proofs')
TABLE=REPO/'Computability/BusyBeaver/Research/ZFC/candidate-prefix246/zfc_prefix246.tm'
TABLE_SHA='89cda615b3ea9fcac07ad6b08e0351faa34841a56935b6f5846d3920f13bc0fc'
FIRST=HERE.parent/'bootstrap-first/run1/verification.json'
FIRST_SHA='15f05525b6910028930b4fc22b7e89f00967bbca7cede98b56597b79ae648b95'
START=1024; PROBE_START=394351; END=410735; DEPTH=14; GROUP_SIZE=4

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def need(c,m):
    if not c: raise ValueError(m)
def dump(p,x): p.write_text(json.dumps(x,indent=2)+'\n')
def segments():
    at=START; out=[]
    while at+(1<<DEPTH)<=PROBE_START:
        out.append(dict(start=at,end=at+(1<<DEPTH),depth=DEPTH));at+=1<<DEPTH
    for d in range(DEPTH-1,-1,-1):
        if at+(1<<d)<=PROBE_START:
            out.append(dict(start=at,end=at+(1<<d),depth=d));at+=1<<d
    need(at==PROBE_START and len(out)==30,'Unexpected segment plan.')
    return [out[i:i+GROUP_SIZE] for i in range(0,len(out),GROUP_SIZE)]
def inspect_parent(path,module,expected_sha=None):
    if expected_sha: need(sha(path)==expected_sha,'Selected first record changed.')
    r=json.loads(path.read_text())
    need(r['status']=='PASS' and r['only_standard_axioms'] and r['all_input_provider_postchecks'] and
         r['all_fresh_objects_unchanged_after_audit'] and r['source_object_recorded_before_audit'],'Incomplete predecessor.')
    need([c['label'] for c in r['commands']]==['source','audit'] and all(c['exit_code']==0 for c in r['commands']),'Predecessor commands failed.')
    fs=[f for f in r['fresh_modules'] if f['module']==module];need(len(fs)==1,'Wrong predecessor module.')
    need(sha(Path(fs[0]['path']))==fs[0]['sha256'] and sha(Path(r['source']['path']))==r['source']['sha256'],'Predecessor bytes changed.')
    return r

def simulate(rows,times):
    # Two configurations: one finite zipper, one independent sparse tape.
    q=h=qs=hs=0;left=[];right=[];ones=set();saved={}
    for t in range(1,END+1):
        w,d,qs=rows[qs,int(hs in ones)]
        if w: ones.add(hs)
        else: ones.discard(hs)
        hs += 1 if d=='R' else -1
        w,d,q=rows[q,right[0] if right else 0]
        if d=='R':left,right,h=[w]+left,right[1:],h+1
        else:right,left,h=[left[0] if left else 0,w]+right[1:],left[1:],h-1
        need(q==qs and h==hs and q<246,'Independent configurations disagree or halt.')
        if t in times:
            support={h-i-1 for i,b in enumerate(left) if b}|{h+i for i,b in enumerate(right) if b}
            need(support==ones,'Complete tape support differs.')
            saved[t]=dict(state=q,head=h,left=left.copy(),right=right.copy(),ones=sorted(ones))
    return saved

def bits(xs):
    return ' ++\n      '.join('['+', '.join('true' if b else 'false' for b in xs[i:i+96])+']' for i in range(0,len(xs),96)) or '[]'
def conf(name,z):
    return f'''def {name} : ZipConfig 246 :=
  {{ state := some ⟨{z['state']}, by decide⟩, head := {z['head']},
    left := {bits(z['left'])},
    right := {bits(z['right'])} }}
'''
def parse_conf(text,name):
    m=re.search(r'def '+name+r' : ZipConfig 246 :=\s*\{(.*?)\n?\s*\}',text,re.S);need(m is not None,'Missing literal checkpoint.')
    s=m.group(1);state=int(re.search(r'state := some ⟨(\d+),',s)[1]);head=int(re.search(r'head := (-?\d+)',s)[1])
    l,r=s.split('left :=',1)[1].split('right :=',1)
    return dict(state=state,head=head,left=[int(v=='true') for v in re.findall(r'\b(true|false)\b',l)],right=[int(v=='true') for v in re.findall(r'\b(true|false)\b',r)])

def main():
    a=argparse.ArgumentParser(description=__doc__)
    a.add_argument('--group',type=int,required=True);a.add_argument('--output',type=Path,required=True)
    a.add_argument('--previous-record',type=Path);a.add_argument('--probe-record',type=Path)
    x=a.parse_args();groups=segments();need(1<=x.group<=len(groups),'Invalid group index.')
    out=x.output.resolve();need(not out.is_relative_to(REPO) and (not out.exists() or not any(out.iterdir())),'Use new empty external directory.')
    ns=f'BootPrefix246Chunk{x.group:03d}';module='BusyBeaver.ZFC.'+ns
    prev_ns='BootPrefix246First' if x.group==1 else f'BootPrefix246Chunk{x.group-1:03d}'
    prev_module='BusyBeaver.ZFC.'+prev_ns
    parent=(x.previous_record or FIRST).resolve();need(x.group==1 or x.previous_record is not None,'A successful previous group is required.')
    record=inspect_parent(parent,prev_module,FIRST_SHA if x.group==1 else None)
    parents=[dict(path=str(parent),sha256=sha(parent),module=prev_module)]
    final=x.group==len(groups);probe=None
    if final:
        need(x.probe_record is not None,'Final group requires the successful local16384 record.')
        pp=x.probe_record.resolve();probe=inspect_parent(pp,'BusyBeaver.ZFC.BootPrefix246Probe16384')
        parents.append(dict(path=str(pp),sha256=sha(pp),module='BusyBeaver.ZFC.BootPrefix246Probe16384'))
    need(sha(TABLE)==TABLE_SHA,'Canonical table changed.');rows={}
    for line in TABLE.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split();key=int(q),int(b);need(key not in rows,'Duplicate action.');rows[key]=int(w),d,int(t)
    need(set(rows)=={(q,b) for q in range(246) for b in range(2)},'Incomplete table.')
    group=groups[x.group-1];times={START,END,PROBE_START,group[0]['start']}|{s['end'] for s in group}
    data=simulate(rows,times)
    first=inspect_parent(FIRST,'BusyBeaver.ZFC.BootPrefix246First',FIRST_SHA)
    literal=parse_conf(Path(first['source']['path']).read_text(),'checkpoint1024')
    need(all(literal[k]==data[1024][k] for k in literal),'First checkpoint data differ.')
    if probe:
        for name,t in [('start',PROBE_START),('finish',END)]:
            literal=parse_conf(Path(probe['source']['path']).read_text(),name)
            need(all(literal[k]==data[t][k] for k in literal),'Probe literal data differ.')
    imports=[prev_module]+(['BusyBeaver.ZFC.BootPrefix246Probe16384'] if final else [])
    s=''.join('import '+m+'\n' for m in imports)+f'''
/-! Serial exact246 blank-run continuation, group{x.group}/{len(groups)}.
Untrusted expected data are discharged by kernel-checked local equalities.
Each equality immediately extends the actual blank-run ZipRep. Default
proof limits apply; runtime-frame and consistency theorems remain separate. -/
namespace SetTheory.BusyBeaver.ZFC.{ns}
open FiniteZipper FastTablePrefix246

'''
    probes=[];examples=[]
    prev_z=f'{prev_ns}.checkpoint{group[0]["start"]}'
    prev_h=f'{prev_ns}.first1024' if x.group==1 else f'{prev_ns}.reached{group[0]["start"]}'
    for seg in group:
        t=seg['end'];z='checkpoint'+str(t);h='reached'+str(t);block='block'+str(t);d=seg['depth']
        s+=(f'def {z} : ZipConfig 246 := BootPrefix246Probe16384.start\n' if final and t==PROBE_START else conf(z,data[t]))+'\n'
        s+=f'''theorem {block} : zipBlock fastMachine {d} {prev_z} = {z} := by
  decide +kernel

theorem {h} : ZipRep (machinePrefix246.run {t}) {z} :=
  BootPrefix246First.advance_checkpoint {seg['start']} {d} {prev_h} {block}

'''
        probes.extend([block,h]);examples.extend([f'example : zipBlock fastMachine {d} {prev_z} = {z} := {block}',f'example : ZipRep (machinePrefix246.run {t}) {z} := {h}'])
        prev_z=z;prev_h=h
    if final:
        s+='''theorem bootstrap410735 :
    ZipRep (machinePrefix246.run 410735) BootPrefix246Probe16384.finish := by
  change ZipRep (machinePrefix246.run (394351 + 16384)) _
  rw [Machine.run_add_eq_runFrom]
  exact BootPrefix246Probe16384.transfer16384 reached394351

theorem bootstrap_state : (machinePrefix246.run 410735).state = some ⟨88, by decide⟩ :=
  bootstrap410735.1

theorem bootstrap_head : (machinePrefix246.run 410735).head = -5 := bootstrap410735.2.1

theorem bootstrap_tape (pos : Int) :
    Tape.read (machinePrefix246.run 410735).tape pos =
      frameRead BootPrefix246Probe16384.finish pos :=
  read_eq_frameRead bootstrap410735 pos

theorem bootstrap_active_through :
    ∀ elapsed, elapsed ≤ 410735 → (machinePrefix246.run elapsed).state ≠ none := by
  apply active_through_of_endpoint
  rw [bootstrap_state]
  decide

'''
        probes+=['bootstrap410735','bootstrap_state','bootstrap_head','bootstrap_tape','bootstrap_active_through']
        examples+=['example : ZipRep (machinePrefix246.run 410735) BootPrefix246Probe16384.finish := bootstrap410735','example : (machinePrefix246.run 410735).state = some ⟨88, by decide⟩ := bootstrap_state','example : (machinePrefix246.run 410735).head = -5 := bootstrap_head','example (p : Int) : Tape.read (machinePrefix246.run 410735).tape p = frameRead BootPrefix246Probe16384.finish p := bootstrap_tape p','example (t : Nat) (h : t ≤ 410735) : (machinePrefix246.run t).state ≠ none := bootstrap_active_through t h']
    else:
        t=group[-1]['end']
        examples += [f'example : (machinePrefix246.run {t}).state = {prev_z}.state := {prev_h}.1',f'example : (machinePrefix246.run {t}).head = {prev_z}.head := {prev_h}.2.1',f'example (p : Int) : Tape.read (machinePrefix246.run {t}).tape p = frameRead {prev_z} p :=\n  read_eq_frameRead {prev_h} p']
    s+=f'end SetTheory.BusyBeaver.ZFC.{ns}\n'
    names=['SetTheory.BusyBeaver.ZFC.'+ns+'.'+p for p in probes]
    audit=f'import {module}\n\nopen SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC\nopen FiniteZipper FastTablePrefix246 {ns}\n\n'+'\n'.join('#print axioms '+n for n in names)+'\n\n'+'\n\n'.join(examples)+'\n'
    out.mkdir(parents=True,exist_ok=True);src=out/(ns+'.lean');aud=out/'Audit.lean';src.write_text(s);aud.write_text(audit)
    data_record=dict(status='UNTRUSTED_GENERATED_INPUTS',canonical_sha256=TABLE_SHA,group=x.group,group_count=len(groups),segments=group,all_groups=groups,checkpoints=data,independent_sparse_and_zipper_states_heads_and_checkpoint_support_agree=True,proof_execution=False)
    dump(out/'data.json',data_record)
    config=dict(module=module,source_name=src.name,source_sha256=sha(src),audit_sha256=sha(aud),data_sha256=sha(out/'data.json'),generator=str(Path(__file__).resolve()),generator_sha256=sha(Path(__file__).resolve()),template=str(HERE/'check-template.py'),template_sha256=sha(HERE/'check-template.py'),parents=parents,imports=imports,probes=names,callers=len(examples),scope=f'Actual blank-run continuation {group[0]["start"]} to {group[-1]["end"]}'+('; completed410735 via checked local16384' if final else '; final410735 and runtime/consistency remain separate'))
    template=(HERE/'check-template.py').read_text();need(template.count('__CONFIG__')==1,'Invalid guard template.')
    (out/'check.py').write_text(template.replace('__CONFIG__',repr(config)))
    dump(out/'source-inventory.json',dict(status='SOURCE_ONLY_READY_NOT_INVOKED',config=config,files={str(p):sha(p) for p in [src,aud,out/'data.json',out/'check.py',Path(__file__).resolve(),HERE/'check-template.py']},compiler_or_checker_calls=[],limits=dict(threads=1,memory_mebibytes=4096,shared_wall_seconds=120,proof_limits='Lean defaults')))
    print(json.dumps(dict(output=str(out),source_sha256=sha(src),audit_sha256=sha(aud),guard_sha256=sha(out/'check.py'),segments=len(group),probes=len(names),callers=len(examples),actual_endpoint=group[-1]['end']),indent=2))
if __name__=='__main__':main()
