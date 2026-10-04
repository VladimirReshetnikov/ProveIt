#!/usr/bin/env python3
"""Release-only replay tests. Mutations are confined to new fixture copies."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys


def canonical_directory(raw, *, fresh=False):
    """Safety preflight before this harness creates any fixture or work file."""
    p = Path(raw)
    if not p.is_absolute() or str(p) != raw or '..' in p.parts or raw.startswith('//'):
        raise ValueError('noncanonical absolute path: '+raw)
    current = Path(p.parts[0])
    for index, component in enumerate(p.parts[1:],1):
        current /= component
        last = index == len(p.parts)-1
        try:
            s = current.lstat()
        except FileNotFoundError:
            if fresh and last:
                return p
            raise ValueError('missing input or work parent: '+str(current))
        if stat.S_ISLNK(s.st_mode) or not stat.S_ISDIR(s.st_mode):
            raise ValueError('linked or nondirectory path component: '+str(current))
        if last and fresh:
            raise ValueError('work root must not exist: '+str(p))
    if fresh:
        raise ValueError('work root must not exist: '+str(p))
    return p


def snapshot(root):
    result = {}
    for p in [root]+sorted(root.rglob('*')):
        s = p.lstat()
        row = {'mode':s.st_mode,'mtime_ns':s.st_mtime_ns,'size':s.st_size,
               'inode':s.st_ino,'device':s.st_dev,'nlink':s.st_nlink}
        if stat.S_ISREG(s.st_mode):
            row['sha256'] = hashlib.sha256(p.read_bytes()).hexdigest()
        result[str(p.relative_to(root))] = row
    return result


def main():
    if sys.flags.optimize:
        raise ValueError('optimized Python is forbidden for this assertion-based test harness')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--science-root',required=True)
    parser.add_argument('--audit-root',required=True)
    parser.add_argument('--adapter-root',required=True)
    parser.add_argument('--work-root',required=True)
    args = parser.parse_args()
    science = canonical_directory(args.science_root)
    audit = canonical_directory(args.audit_root)
    adapter = canonical_directory(args.adapter_root)
    work = canonical_directory(args.work_root,fresh=True)
    if not all(root != work and root not in work.parents and work not in root.parents
               for root in (science,audit,adapter)):
        raise ValueError('work root overlaps a protected input')
    original_before = {'science':snapshot(science),'audit':snapshot(audit)}
    adapter_before = snapshot(adapter)
    protected_directories = {(entry['device'],entry['inode'])
                             for tree in (*original_before.values(),adapter_before)
                             for entry in tree.values() if stat.S_ISDIR(entry['mode'])}
    for parent in work.parents:
        s = parent.lstat()
        if (s.st_dev,s.st_ino) in protected_directories:
            raise ValueError('work parent aliases a protected input directory')
    work.mkdir(mode=0o700)
    results = []

    def invoke(name, *, s=science,a=audit,p=adapter/'PINNED_INPUTS.json',
               tool=adapter/'replay.py',out=None, expected=None, existing=False):
        destination = work/('out-'+name) if out is None else out
        run = subprocess.run(
            [sys.executable,'-I','-S','-B',str(tool),
             '--science-root',str(s),'--audit-root',str(a),'--pins',str(p),
             '--output-root',str(destination)],
            stdin=subprocess.DEVNULL,stdout=subprocess.PIPE,stderr=subprocess.PIPE,
            timeout=60,check=False,
        )
        if expected is None:
            assert run.returncode == 0, (name,run.stderr)
            receipt = json.loads((destination/'replay_receipt.json').read_text())
            assert receipt['passed'] and receipt['deterministic_evidence_byte_equal']
            assert (destination/'independent_affine_evidence.json').read_bytes() == (audit/'independent_affine_evidence.json').read_bytes()
        else:
            assert run.returncode == 2 and expected in run.stderr.decode(), (name,run.returncode,run.stderr)
            if not existing:
                assert not os.path.lexists(destination), (name,'output unexpectedly created')
        results.append({'name':name,'passed':True,'returncode':run.returncode,
                        'expected_rejection':expected,
                        'stderr':run.stderr.decode(),'output_root':str(destination)})

    def fixture(name):
        base = work/('fixture-'+name)
        base.mkdir()
        shutil.copytree(science,base/'science')
        shutil.copytree(audit,base/'audit')
        return base,base/'science',base/'audit'

    invoke('original-inputs')
    base,s,a = fixture('read-only-relocation')
    for root in (s,a):
        for p in sorted(root.rglob('*'),reverse=True):
            p.chmod(0o555 if p.is_dir() else 0o444)
        root.chmod(0o555)
    readonly_before = {'science':snapshot(s),'audit':snapshot(a)}
    invoke('read-only-relocation',s=s,a=a)
    assert readonly_before == {'science':snapshot(s),'audit':snapshot(a)}

    base,s,a = fixture('complete-portable-relocation')
    relocated_adapter = base/'adapter'
    shutil.copytree(adapter,relocated_adapter)
    for root in (s,a,relocated_adapter):
        for p in sorted(root.rglob('*'),reverse=True):
            p.chmod(0o555 if p.is_dir() else 0o444)
        root.chmod(0o555)
    portable_before = {str(root):snapshot(root) for root in (s,a,relocated_adapter)}
    invoke('complete-portable-relocation',s=s,a=a,p=relocated_adapter/'PINNED_INPUTS.json',
           tool=relocated_adapter/'replay.py')
    assert portable_before == {str(root):snapshot(root) for root in (s,a,relocated_adapter)}

    bad_pins = work/'invalid-pins.json'
    bad_pins.write_bytes((adapter/'PINNED_INPUTS.json').read_bytes()+b'\n')
    invoke('invalid-pins',p=bad_pins,expected='pins authentication failed')

    base,s,a = fixture('science-corruption')
    (s/'PROOF.md').write_bytes((s/'PROOF.md').read_bytes()+b'\n')
    invoke('science-corruption',s=s,a=a,expected='content/hash mismatch')
    base,s,a = fixture('checker-corruption')
    (a/'independent_affine_checks.py').write_bytes((a/'independent_affine_checks.py').read_bytes()+b'\n')
    invoke('checker-corruption',s=s,a=a,expected='content/hash mismatch')
    base,s,a = fixture('expected-evidence-corruption')
    (a/'independent_affine_evidence.json').write_bytes((a/'independent_affine_evidence.json').read_bytes()+b'\n')
    invoke('expected-evidence-corruption',s=s,a=a,expected='content/hash mismatch')
    base,s,a = fixture('extra-file')
    (s/'UNEXPECTED.txt').write_text('not part of frozen input\n')
    invoke('extra-file',s=s,a=a,expected='unexpected inventory entry')
    base,s,a = fixture('extra-directory')
    (a/'unexpected-empty-directory').mkdir()
    invoke('extra-directory',s=s,a=a,expected='unexpected inventory entry')
    base,s,a = fixture('missing-file')
    (s/'README.md').unlink()
    invoke('missing-file',s=s,a=a,expected='missing inventory entries')

    base,s,a = fixture('symlink-file')
    target = base/'real-readme'
    (s/'README.md').rename(target)
    (s/'README.md').symlink_to(target)
    invoke('symlink-file',s=s,a=a,expected='symbolic-link input rejected')
    base,s,a = fixture('hardlink-file')
    os.link(s/'README.md',base/'second-name')
    invoke('hardlink-file',s=s,a=a,expected='hard-linked file rejected')
    base,s,a = fixture('special-file')
    (s/'README.md').unlink()
    os.mkfifo(s/'README.md')
    invoke('special-file',s=s,a=a,expected='not a regular file')

    root_link = work/'science-link'
    root_link.symlink_to(science,target_is_directory=True)
    invoke('symlink-root',s=root_link,expected='symbolic-link path rejected')
    parent_link = work/'parent-link'
    parent_link.symlink_to(science.parent,target_is_directory=True)
    invoke('symlink-parent',s=parent_link/science.name,expected='symbolic-link path rejected')
    invoke('same-root-alias',a=science,expected='overlap or alias')
    invoke('parent-components',s=str(science)+'/../'+science.name,expected='canonical spelling')
    invoke('dot-component',s=str(science)+'/.',expected='canonical spelling')
    invoke('double-leading-slash',s='/'+str(science),expected='canonical spelling')
    invoke('relative-root',s='relative/science',expected='path must be absolute')
    invoke('output-overlap',out=science/'forbidden-output',expected='output overlaps')
    invoke('adapter-output-overlap',out=adapter/'forbidden-output',expected='output overlaps')
    already = work/'existing-output'
    already.mkdir()
    invoke('existing-output',out=already,expected='fresh and nonexistent',existing=True)
    linked_output = work/'linked-output'
    linked_output.symlink_to(already,target_is_directory=True)
    invoke('symlink-output',out=linked_output,expected='symbolic-link path rejected',existing=True)
    linked_parent = work/'output-parent-link'
    linked_parent.symlink_to(already,target_is_directory=True)
    invoke('symlink-output-parent',out=linked_parent/'new-output',expected='symbolic-link path rejected')

    # Regression guards on the test harness itself; both abort before any work.
    base,s,a = fixture('harness-parent-alias')
    harness_parent = work/'harness-parent-link'
    harness_parent.symlink_to(s,target_is_directory=True)
    for name,flags,new_work,expected in (
        ('harness-parent-alias',[],harness_parent/'forbidden-work','linked or nondirectory path component'),
        ('harness-optimized',['-O'],work/'optimized-forbidden-work','optimized Python is forbidden'),
    ):
        run = subprocess.run(
            [sys.executable,'-I','-S','-B',*flags,str(Path(__file__)),
             '--science-root',str(s),'--audit-root',str(a),'--adapter-root',str(adapter),
             '--work-root',str(new_work)],
            stdin=subprocess.DEVNULL,stdout=subprocess.PIPE,stderr=subprocess.PIPE,
            timeout=60,check=False,
        )
        assert run.returncode != 0 and expected in run.stderr.decode(), (name,run.stderr)
        assert not os.path.lexists(new_work), (name,'harness created forbidden work')
        results.append({'name':name,'passed':True,'returncode':run.returncode,
                        'expected_rejection':expected,'stderr':run.stderr.decode(),
                        'output_root':str(new_work)})

    assert original_before == {'science':snapshot(science),'audit':snapshot(audit)}
    report = {
        'passed':True,'case_count':len(results),'cases':results,
        'original_science_and_audit_unchanged':True,
        'read_only_relocated_inputs_unchanged':True,
        'read_only_relocated_adapter_and_inputs_unchanged':True,
        'read_only_modes':'files 0444; directories 0555, including each relocated root',
        'test_boundary':'Only fixture copies mutated; successful runs execute the pinned reviewer checker, never author code or dependency code',
        'adapter_sha256':hashlib.sha256((adapter/'replay.py').read_bytes()).hexdigest(),
        'pins_sha256':hashlib.sha256((adapter/'PINNED_INPUTS.json').read_bytes()).hexdigest(),
        'test_source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'limitations':'No adversarial concurrent-mutation, bind-mount manipulation, interpreter-compromise or network-sandbox test',
    }
    (work/'TEST_RESULTS.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'passed':True,'case_count':len(results),'report':str(work/'TEST_RESULTS.json')},sort_keys=True))


if __name__ == '__main__':
    main()
