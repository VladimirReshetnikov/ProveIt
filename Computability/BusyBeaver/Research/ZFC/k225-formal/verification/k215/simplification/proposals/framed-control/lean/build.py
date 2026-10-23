#!/usr/bin/env python3
"""Fresh sequential Lean 4.32.0 build of the complete framed-control component.

  python3 lean/build.py --lean /path/to/lean --work /path/to/new-directory

Only source files in the transitive import closure of FrameCallers and
FrameRouteSound are copied. No packaged or previously built object is reused.
All output goes to the fresh work directory; the delivered package is read-only.
This builds a component, not KEndpoint215 or an internal ZFC derivation.
"""
from pathlib import Path, PurePosixPath
import argparse
import datetime
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT_MODULES = ('FrameCallers', 'FrameRouteSound')
PINNED_COMMIT = 'cbf94cb552a3b49509e0eee80e7455d4eb5974c6'
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
MODULE_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def without_comments(text):
    """Preserve line structure and strings; erase nested Lean block comments."""
    out = []
    i = depth = 0
    in_string = False
    while i < len(text):
        pair = text[i:i+2]
        if depth:
            if pair == '/-':
                depth += 1; i += 2
            elif pair == '-/':
                depth -= 1; i += 2
            else:
                if text[i] == '\n':
                    out.append('\n')
                i += 1
        elif in_string:
            out.append(text[i])
            if text[i] == '\\' and i + 1 < len(text):
                out.append(text[i+1]); i += 2
            else:
                if text[i] == '"':
                    in_string = False
                i += 1
        elif pair == '/-':
            out.append(' '); depth = 1; i += 2
        elif pair == '--':
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            out.append(text[i])
            if text[i] == '"':
                in_string = True
            i += 1
    require(depth == 0, 'Unclosed Lean block comment')
    return ''.join(out)


def source_imports(text):
    result = []
    for line in without_comments(text).splitlines():
        m = re.match(r'^\s*(?:public\s+|private\s+)?import\s+(.+?)\s*$', line)
        if m:
            for module in m.group(1).split():
                require(MODULE_RE.fullmatch(module) is not None,
                        'Unsupported import syntax: ' + module)
                result.append(module)
    return result


def relative_source(module):
    require(MODULE_RE.fullmatch(module) is not None, 'Invalid module name')
    return Path(*module.split('.')).with_suffix('.lean')


def load_pins():
    path = HERE / 'UPSTREAM_PINS.json'
    data = json.loads(path.read_text())
    require(data.get('commit') == PINNED_COMMIT, 'Upstream commit is not the reviewed pin')
    pins = {}
    for item in data['unchanged_upstream_modules']:
        raw_path = PurePosixPath(item['component_path'])
        require(not raw_path.is_absolute() and '..' not in raw_path.parts,
                'Unsafe upstream source path')
        require(raw_path.suffix == '.lean', 'Upstream pin is not a Lean source')
        module = '.'.join(raw_path.with_suffix('').parts)
        require(module not in pins, 'Duplicate upstream module pin')
        path = HERE / Path(*raw_path.parts)
        require(path.is_file() and not path.is_symlink(), 'Missing or linked upstream source: ' + str(raw_path))
        require(path.stat().st_size == item['bytes'] and digest(path) == item['sha256'],
                'Upstream source identity mismatch: ' + str(raw_path))
        pins[module] = item
    return data, pins


def plan_sources(pins):
    sources, ordered, active, done, external = {}, [], set(), set(), set()
    def visit(module):
        if module == 'Init':
            external.add(module); return
        if module in done:
            return
        require(module not in active, 'Import cycle at ' + module)
        relative = relative_source(module)
        path = HERE / relative
        require(path.is_file() and not path.is_symlink(),
                'Unresolved import (only external Init is allowed): ' + module)
        raw = path.read_bytes()
        text = raw.decode('utf-8')
        imports = source_imports(text)
        clean = without_comments(text)
        if module not in pins:
            require(re.search(r'\b(?:sorry|admit|native_decide)\b', clean) is None,
                    'Admission or native decision in new source: ' + module)
            require(re.search(r'^\s*(?:(?:private|protected|noncomputable)\s+)*axiom\b', clean, re.M) is None,
                    'Added axiom declaration in new source: ' + module)
        sources[module] = dict(component_path=relative.as_posix(), sha256=hashlib.sha256(raw).hexdigest(),
            bytes=len(raw), imports=imports, unchanged_upstream=module in pins,
            expected_assumption_reports=len(re.findall(r'^\s*#print\s+axioms\s+', clean, re.M)))
        active.add(module)
        for imported in imports:
            visit(imported)
        active.remove(module)
        done.add(module)
        ordered.append(module)
    for root in ROOT_MODULES:
        visit(root)
    return sources, ordered, sorted(external)


def assumption_reports(log):
    pattern = re.compile(r"^'([^\n]+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", re.M)
    reports = []
    for match in pattern.finditer(log):
        names = [] if match.group(2) is None else [x.strip() for x in match.group(2).split(',') if x.strip()]
        reports.append(dict(declaration=match.group(1), axioms=names))
    return reports


def compiler_path(value):
    found = shutil.which(value)
    if found is None and Path(value).is_file():
        found = str(Path(value).resolve())
    require(found is not None, 'Lean compiler was not found: ' + value)
    return str(Path(found).resolve())


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--lean', default='lean', help='Lean 4.32.0 executable')
    ap.add_argument('--work', type=Path, required=True, help='New directory; it must not already exist')
    ap.add_argument('--plan-only', action='store_true', help='Check and copy the source closure without invoking Lean')
    args = ap.parse_args()
    work = args.work.resolve()
    require(not work.exists(), 'Work directory already exists; choose a fresh path')
    require(HERE.parent not in work.parents and work != HERE.parent,
            'Build output must be outside the delivered package')
    provenance, pins = load_pins()
    sources, order, external = plan_sources(pins)
    work.mkdir(parents=True)
    source_dir, logs = work/'sources', work/'logs'
    source_dir.mkdir(); logs.mkdir()
    for module in order:
        relative = Path(sources[module]['component_path'])
        destination = source_dir/relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(HERE/relative, destination)
        require(digest(destination) == sources[module]['sha256'], 'Copied source mismatch')
    start = time.perf_counter()
    result = dict(status='PLANNED', scope='Fresh framed-control component only; KEndpoint215 is not rebuilt',
        repository=provenance['repository'], commit=PINNED_COMMIT,
        roots=list(ROOT_MODULES), project_modules=len(order),
        unchanged_upstream_modules=sum(m in pins for m in order),
        new_modules=sum(m not in pins for m in order), external_toolchain_imports=external,
        no_project_object_reuse=True, source_plan=sources, compilation_order=order, records=[],
        started_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
    result_path = work/'BUILD_RESULT.json'
    def save():
        result['elapsed_seconds'] = round(time.perf_counter()-start, 6)
        result_path.write_text(json.dumps(result, indent=2)+'\n')
    save()
    if args.plan_only:
        result['status']='SOURCE_PLAN_PASS_NO_COMPILATION';save()
        print(json.dumps({k:result[k] for k in ('status','project_modules','unchanged_upstream_modules','new_modules')}))
        return
    try:
        lean = compiler_path(args.lean)
        env = os.environ.copy()
        env['LEAN_PATH'] = str(source_dir)
        env['NO_COLOR'] = '1'
        version = subprocess.run([lean, '--version'], capture_output=True, text=True, env=env)
        version_log = version.stdout+version.stderr
        (logs/'compiler-version.log').write_text(version_log)
        require(version.returncode == 0, 'Lean --version failed')
        require(re.search(r'\bversion\s+4\.32\.0(?=[\s,)])', version_log) is not None,
                'Expected exactly Lean 4.32.0; got ' + version_log.strip())
        result['compiler'] = dict(path=lean, sha256=digest(lean), version=version_log.strip(),
            version_log_sha256=digest(logs/'compiler-version.log'))
        result['status']='RUNNING';save()
        prior = {}
        for module in order:
            info=sources[module]
            relative=Path(info['component_path'])
            obj=relative.with_suffix('.olean')
            require(not (source_dir/obj).exists(), 'An object already exists before compilation')
            dependency_bindings={}
            for imported in info['imports']:
                if imported != 'Init':
                    dep=prior[imported]
                    dep_path=source_dir/relative_source(imported).with_suffix('.olean')
                    require(digest(dep_path)==dep['object_sha256'], 'Dependency object changed: '+imported)
                    dependency_bindings[imported]=dict(source_sha256=sources[imported]['sha256'],
                        object_sha256=dep['object_sha256'], log_sha256=dep['log_sha256'])
            command=[lean,'-o',obj.as_posix(),relative.as_posix()]
            tick=time.perf_counter()
            cp=subprocess.run(command,cwd=source_dir,env=env,stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT,text=True)
            log_path=logs/(module.replace('.','__')+'.log')
            log_path.write_text(cp.stdout)
            warnings=re.findall(r'^.*\bwarning:.*$',cp.stdout,re.M)
            reports=assumption_reports(cp.stdout)
            reasons=[]
            if cp.returncode != 0:reasons.append('nonzero compiler exit')
            if re.search(r'(^|\n)(?:[^\n]*:\s*)?error:',cp.stdout):reasons.append('compiler error diagnostic')
            if 'sorryAx' in cp.stdout:reasons.append('sorryAx reported')
            if warnings:
                known=(module=='BusyBeaver.ZFC.KZip' and module in pins and len(warnings)==1
                       and 'This simp argument is unused' in warnings[0])
                if not known:reasons.append('unexpected warning')
            for report in reports:
                if set(report['axioms'])-ALLOWED_AXIOMS:
                    reasons.append('unexpected axiom profile for '+report['declaration'])
            if len(reports)!=info['expected_assumption_reports']:
                reasons.append('missing or unexpected printed assumption report')
            if not (source_dir/obj).is_file():reasons.append('missing compiled object')
            if digest(source_dir/relative)!=info['sha256']:reasons.append('source changed during compile')
            record=dict(module=module,command=command,exit_code=cp.returncode,
                elapsed_seconds=round(time.perf_counter()-tick,6),
                source_sha256=info['sha256'],source_bytes=info['bytes'],imports=info['imports'],
                dependency_bindings=dependency_bindings,
                object_sha256=digest(source_dir/obj) if (source_dir/obj).is_file() else None,
                object_bytes=(source_dir/obj).stat().st_size if (source_dir/obj).is_file() else None,
                log=str(log_path.relative_to(work)),log_sha256=digest(log_path),
                warning_count=len(warnings),warnings=warnings,assumption_reports=reports,
                status='PASS' if not reasons else 'FAILED',failure_reasons=reasons)
            result['records'].append(record);save()
            print(json.dumps(dict(module=module,status=record['status'],
                seconds=record['elapsed_seconds'],warnings=len(warnings),reports=len(reports))),flush=True)
            require(not reasons, module+': '+', '.join(reasons)+'; see '+str(log_path))
            prior[module]=record
        result['status']='COMPONENT_KERNEL_CHECK_PASS'
        result['completed_at_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
        result['assumption_reports']=sum(len(r['assumption_reports'])for r in result['records'])
        result['warning_count']=sum(r['warning_count']for r in result['records'])
        save()
        print(json.dumps(dict(status=result['status'],project_modules=len(order),
            result=str(result_path),elapsed_seconds=result['elapsed_seconds'])),flush=True)
    except BaseException as exc:
        result['status']='FAILED'
        result['failure']=str(exc)
        save()
        raise


if __name__=='__main__':
    try:
        main()
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        print('BUILD FAILED: '+str(error),file=sys.stderr)
        sys.exit(1)
