#!/usr/bin/env python3
"""Bind both complete Lean arrays to .tm files, then compile a fresh proof.

Requires official Lean4.32.0 (no Mathlib). The relative theorem quantifies
arbitrary Int→Bool tapes and heads from inherited start95. Calibration of
the original243 machine is an explicit separate obligation.
"""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,subprocess,time
HERE=Path(__file__).resolve().parent
SOURCES=['Tables242.lean','BlockSimulation.lean','Reduction242.lean','Audit242.lean']
EXPECTED_OLD='4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300'
ALLOWED_AXIOMS={'propext','Quot.sound'}
def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def table(p):
    out={}
    for line in Path(p).read_text().splitlines():
        if not line.strip()or line.startswith('#'):continue
        q,b,w,d,t=line.split();key=(int(q),int(b))
        assert key not in out and b in ('0','1')and w in ('0','1')and d in ('L','R')
        out[key]=(int(w),d,int(t))
    assert set(out)=={(q,b)for q,_ in out for b in (0,1)}
    return out

def lean_array(text,name):
    body=text.split('def '+name+' : Array (Option (Action × Action)) := #[',1)[1].split('\n]\n',1)[0]
    rows={};labels=[]
    pat=re.compile(r'^\s*(none|some \(⟨(true|false), (true|false), (\d+)⟩, ⟨(true|false), (true|false), (\d+)⟩\)),? -- (\d+)$')
    for line in body.splitlines():
        if not line.strip():continue
        m=pat.fullmatch(line);assert m,repr(line)
        q=int(m[8]);labels.append(q)
        if m[1]!='none':
            for b,w,d,t in [(0,m[2],m[3],m[4]),(1,m[5],m[6],m[7])]:
                rows[q,b]=(int(w=='true'),'R'if d=='true'else'L',int(t))
    assert labels==list(range(256))
    return rows

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--old',type=Path,default=HERE.parent/'reference/zfc_combined243_old.tm')
    ap.add_argument('--new',type=Path,default=HERE.parent/'machine/zfc242_old.tm')
    ap.add_argument('--lean',default='lean')
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();assert __debug__
    old,new=table(args.old),table(args.new)
    assert digest(args.old)==EXPECTED_OLD and len(old)==486 and len(new)==484
    assert max(q for q,b in old)==max(q for q,b in new)==255
    patched={k:v for k,v in old.items()if k[0]!=15}
    patched[11,0]=(0,'R',27);patched[27,1]=(1,'R',22)
    assert new==patched
    txt=(HERE/'Tables242.lean').read_text()
    assert lean_array(txt,'oldRows')==old
    assert lean_array(txt,'newRows')==new
    files=[HERE/x for x in SOURCES]+[args.old.resolve(),args.new.resolve(),Path(__file__).resolve()]
    before={str(p.resolve()):digest(p)for p in files}
    for name in SOURCES:
        source=(HERE/name).read_text()
        assert not re.search(r'\b(sorry|admit|native_decide|unsafe|axiom)\b',source)
    probes=re.findall(r'^#print axioms (\S+)$',(HERE/'Audit242.lean').read_text(),re.M)
    assert len(probes)==18
    callers=len(re.findall(r'^example\b',(HERE/'Audit242.lean').read_text(),re.M))
    assert callers==13
    executable=shutil.which(args.lean)or(str(Path(args.lean).resolve())if Path(args.lean).is_file()else None)
    assert executable,'Lean executable not found.'
    executable=str(Path(executable).resolve())
    version=subprocess.run([executable,'--version'],text=True,capture_output=True,check=True).stdout.strip()
    assert re.search(r'\bversion 4\.32\.0\b',version),version
    output=args.output.resolve()
    assert not output.exists()or(output.is_dir()and not any(output.iterdir())),'Fresh output directory required.'
    output.mkdir(parents=True,exist_ok=True)
    snapshots=output/'sources';objects=output/'objects';snapshots.mkdir();objects.mkdir()
    for name in SOURCES:shutil.copyfile(HERE/name,snapshots/name)
    result=dict(status='RUNNING',lean_executable=executable,lean_sha256=digest(executable),
        lean_version=version,table_rows=dict(old=len(old),new=len(new)),
        maximum_working_inherited_label=255,source_arrays_exactly_match_both_tables=True,
        old_sha256=digest(args.old),new_sha256=digest(args.new),before=before,
        source_snapshots={name:digest(snapshots/name)for name in SOURCES},
        resource_settings={'Tables242.maxRecDepth':4096,'Tables242.maxHeartbeats':2000000},
        probes=probes,typed_callers=callers,commands=[],objects=[],
        scope='Relative halting/nonhalting equivalence for arbitrary Int→Bool tape and head from inherited95. No source/logic calibration theorem is imported.')
    def save():(output/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    save()
    try:
        env=dict(os.environ,LEAN_PATH=str(objects))
        for name in SOURCES:
            module=Path(name).stem;obj=objects/(module+'.olean')
            command=[executable,'-o',str(obj),str(snapshots/name)]
            started=time.monotonic()
            process=subprocess.run(command,cwd=snapshots,env=env,text=True,capture_output=True,timeout=120)
            text=process.stdout+process.stderr
            (output/(module+'.log')).write_text(text)
            result['commands'].append(dict(module=module,command=command,exit_code=process.returncode,
                seconds=time.monotonic()-started,output=text))
            save()
            assert process.returncode==0,(module,text)
            assert 'warning:'not in text and 'sorryAx'not in text,(module,text)
            result['objects'].append(dict(module=module,sha256=digest(obj)))
        out=result['commands'][-1]['output']
        reports=re.findall(r"^'([^\n]+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.M)
        assert [n for n,_ in reports]==probes
        result['axioms']=[dict(name=n,axioms=[x.strip()for x in a.split(',')if x.strip()])for n,a in reports]
        assert all(set(row['axioms'])<=ALLOWED_AXIOMS for row in result['axioms'])
        result['after']={p:digest(p)for p in before};assert before==result['after']
        assert result['source_snapshots']=={name:digest(snapshots/name)for name in SOURCES}
        result.update(status='PASS',warnings=0,no_custom_axioms=True,all_inputs_unchanged=True)
    except BaseException as exc:
        result.update(status='FAIL',error=repr(exc));save();raise
    save()
    print(json.dumps({k:v for k,v in result.items()if k not in ('before','after','commands','axioms')},indent=2))

if __name__=='__main__':main()
