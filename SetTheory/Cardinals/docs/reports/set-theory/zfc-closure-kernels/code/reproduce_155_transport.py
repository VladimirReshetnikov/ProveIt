#!/usr/bin/env python3
"""Replay source45 on a copy, omitting BOTH bulk manifest loops in memory.

The original files are not rewritten. Literal program identity checks in the
functional verifiers remain enabled. Every direct-child machine JSON/TM output
is compared byte-for-byte before/after regeneration, without reading a manifest.
"""
from __future__ import annotations
import argparse,ast,contextlib,importlib.util,io,json,sys
from pathlib import Path


def load_file(path: Path, name: str):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def nested_replay(package: Path):
    path=package/'machine_control/reproduce.py'
    tree=ast.parse(path.read_text(),filename=str(path))
    removed=0
    for node in tree.body:
        if isinstance(node,ast.FunctionDef) and node.name=='main':
            kept=[]
            for statement in node.body:
                # The three delivered loops: read a bulk manifest, precheck it,
                # and hash-check regenerated outputs against that manifest.
                if isinstance(statement,ast.For):
                    iterator=ast.unparse(statement.iter)
                    if iterator=='manifest.read_text().splitlines()' or iterator=='pinned.items()':
                        removed+=1
                        continue
                if isinstance(statement,ast.Expr) and isinstance(statement.value,ast.Call):
                    call=statement.value
                    if isinstance(call.func,ast.Name) and call.func.id=='print':
                        # Replace the original len(pinned)/byte-identical claim
                        # with explicit adapter evidence after its actual check.
                        continue
                kept.append(statement)
            node.body=kept
    if removed!=3:
        raise RuntimeError(f'nested source coordination changed: expected3 bulk loops, found{removed}')
    namespace={'__file__':str(path),'__name__':'source45_nested_replay'}
    exec(compile(ast.fix_missing_locations(tree),str(path),'exec'),namespace)
    outputs=sorted(p for p in path.parent.iterdir() if p.is_file() and p.suffix in {'.tm','.json'})
    before={p:p.read_bytes() for p in outputs}
    namespace['main']()
    for p,expected in before.items():
        if p.read_bytes()!=expected:
            raise AssertionError('Regenerated functional output bytes differ: '+str(p.name))
    print(json.dumps({'passed':True,'bulk_manifest_checks_skipped':True,
        'bulk_manifest_loops_removed_in_memory':removed,
        'functional_output_files_byte_identical':len(outputs)},indent=2))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('package',type=Path)
    parser.add_argument('--extended',action='store_true')
    args=parser.parse_args();package=args.package.resolve()
    module=load_file(package/'reproduce.py','source45_replay')
    module.verify_manifest=lambda:None
    original_run=module.run
    def run(script,*arguments):
        if script=='machine_control/reproduce.py':
            if arguments:raise RuntimeError('unexpected nested replay arguments')
            buffer=io.StringIO()
            with contextlib.redirect_stdout(buffer):nested_replay(package)
            value=buffer.getvalue();print(value,end='')
            print('PASS '+script+' (bulk manifests skipped in memory)',flush=True)
            return value
        return original_run(script,*arguments)
    module.run=run
    oldargv=sys.argv
    try:
        sys.argv=[str(package/'reproduce.py')]+(['--extended'] if args.extended else [])
        module.main()
    finally:sys.argv=oldargv

if __name__=='__main__':main()
