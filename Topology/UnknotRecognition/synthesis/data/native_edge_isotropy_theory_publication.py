"""Bind the proved native edge-isotropy theory without pending audit claims.

Only metadata and bytes are read. No historical main, test, solver, algebra
audit, geometry replay or PDF build is executed. Native files are unchanged.
"""
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess

from strict_pachner32_publication import included_tex, python_dependencies

DATA = Path(__file__).resolve().parent
ROOT = DATA.parent.parent
PREFIX = 'native-edge-isotropy-theory'
REVISION = 'cb075f7b539360f71ed4c8d3a83c98155e2d5997'
GIT_PREFIX = 'Topology/UnknotRecognition/'
PARENT = DATA/'sparse-separator-publication.json'
PARENT_SHA256 = 'd04c0117e70dcf52d27f75b010e94b7ca3a7c29b31ba3c583a59023808d9962b'
DOCUMENT_EXCEPTIONS = frozenset(('synthesis/README.md','synthesis/report.tex',
    'synthesis/marked_cut_handlebodies.tex','synthesis/report.pdf'))
NEW_CHAPTER = ROOT/'synthesis/native_edge_isotropy.tex'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def same(left, right):
    if type(left) is not type(right):
        return False
    if type(left) is dict:
        return left.keys()==right.keys() and all(same(left[key],right[key]) for key in left)
    if type(left) in (list,tuple):
        return len(left)==len(right) and all(same(a,b) for a,b in zip(left,right))
    return left==right


def equal(left, right, message):
    require(same(left,right),message)


def load(path):
    return json.loads(path.read_bytes())


def historical_checkpoint():
    require(digest(PARENT)==PARENT_SHA256,'unaltered parent publication manifest')
    repository=subprocess.check_output(['git','rev-parse','--show-toplevel'],cwd=ROOT,text=True).strip()
    committed=subprocess.check_output(['git','show',REVISION+':'+GIT_PREFIX+str(PARENT.relative_to(ROOT))],
        cwd=repository)
    require(sha256(committed).hexdigest()==PARENT_SHA256,'parent manifest committed at declared revision')
    parent=load(PARENT)
    expected=dict(schema='sparse-separator-publication-v1',passed=True,tests=408,
        test_modules=45,skipped_tests=0,tested_files=363,native_modules=299,
        general_quasipolynomial=False,new_timing_claims=False,retained_test_coverage=True,
        new_tests_run=0,new_recognition_calls=0)
    fields=tuple(expected)
    equal({key:parent[key] for key in fields},expected,'parent native/test coverage and limits')
    stdout=DATA/'sparse-separator-publication.txt'
    equal(load(stdout),{key:value for key,value in parent.items() if key!='files_sha256'},
        'retained parent publication stdout')
    pins=parent['files_sha256']
    require(type(pins) is dict and len(pins)==989,'complete prior989-file pin map')
    require(DOCUMENT_EXCEPTIONS<=pins.keys(),'document exceptions are existing parent files')
    paths,changed=set(),[]
    for name,expected_hash in pins.items():
        require(type(name) is str and type(expected_hash) is str and
            re.fullmatch('[0-9a-f]{64}',expected_hash),'literal parent hash entry')
        path=(ROOT/name).resolve()
        require(path.is_relative_to(ROOT) and path.is_file(),'retained dependency exists within project')
        paths.add(path)
        if digest(path)!=expected_hash:
            require(name in DOCUMENT_EXCEPTIONS,'unexpected parent file change: '+name)
            changed.append(name)
    # Every native package member, including its two non-Python support files,
    # is retained; no newly added unpinned native file is silently admitted.
    old_native={ROOT/name for name in pins if name.startswith('fast/fastunknot/')}
    current_native={path for path in (ROOT/'fast/fastunknot').rglob('*') if path.is_file() and
        '__pycache__' not in path.parts and path.suffix!='.pyc'}
    equal(current_native,old_native,'complete unchanged301-file native package')
    require(len(current_native)==301 and len([p for p in current_native if p.suffix=='.py'])==299,
        'native package coverage')
    snapshot_path=DATA/'native-lex-prefix-test-source.json'
    snapshot=load(snapshot_path)
    equal(snapshot['schema'],'native-lex-prefix-test-source-v1','retained pre-run test manifest')
    equal(snapshot['expected_tests'],408,'retained broad test count')
    require(type(snapshot['files_sha256']) is dict and len(snapshot['files_sha256'])==363,
        'all363 historical tested inputs retained')
    for name,value in snapshot['files_sha256'].items():
        equal(pins[name],value,'parent pins contain exact pre-run tested input')
    require('synthesis/coordinate_separator_obstruction.tex' in pins,
        'earlier separator chapter retained without documentary exception')
    return parent,dict(revision=REVISION,manifest_sha256=PARENT_SHA256,historical_files=989,
        unchanged_files=989-len(changed),actual_document_changes=sorted(changed),
        allowed_document_changes=sorted(DOCUMENT_EXCEPTIONS),native_package_files=301,
        native_modules=299,tested_files=363,native_test_and_whole_call_evidence_unchanged=True), \
        paths|{PARENT,stdout}


def diagnostics(contents):
    result=Counter()
    for line in contents.splitlines():
        if 'Warning:' in line or re.match(r'^(?:Over|Under)full \\[hv]box\b',line):
            line=re.sub(r'\bat lines \d+--\d+\b','at lines <range>',line.strip())
            line=re.sub(r'\bat line \d+\b','at line <number>',line)
            result[line]+=1
    return result


def final_build(parent):
    baseline=DATA/'sparse-separator-latex-3.txt'
    equal(digest(baseline),parent['files_sha256'][str(baseline.relative_to(ROOT))],
        'unchanged final parent build diagnostic reference')
    logs=[DATA/f'{PREFIX}-latex-{i}.txt' for i in (1,2,3)]
    for path in logs:
        contents=path.read_text()
        require('Output written on report.pdf' in contents,'all three PDF passes completed')
        require(not re.search(r'^!|Emergency stop|Fatal error occurred',contents,re.M),'no build failure')
    final=logs[-1].read_text()
    require(not re.search(r'undefined references|undefined on input|Rerun to get|Label\(s\) may have changed|multiply.defined labels',final),
        'final references settled')
    require(not (diagnostics(final)-diagnostics(baseline.read_text())),'no additional final build diagnostics')
    match=re.search(r'Output written on report\.pdf \((\d+) pages, (\d+) bytes\)',final)
    require(match is not None,'final page/byte report')
    pdf=ROOT/'synthesis/report.pdf'
    require(pdf.read_bytes().startswith(b'%PDF-') and pdf.stat().st_size==int(match[2]),
        'current PDF matches final build bytes')
    tex=included_tex(ROOT/'synthesis/report.tex')
    require({NEW_CHAPTER,ROOT/'synthesis/coordinate_separator_obstruction.tex',
        ROOT/'synthesis/sparse_coordinate_separators.tex'}<=tex,'new native chapter and prior obstructions included')
    return dict(report_pages=int(match[1]),report_bytes=int(match[2]),included_tex_files=len(tex)), \
        tex|set(logs)|{pdf,baseline}


def main():
    if not __debug__:
        raise RuntimeError('publication verification requires assertions enabled')
    output=DATA/f'{PREFIX}-publication.json'
    if output.exists():
        raise FileExistsError('Refuse to overwrite retained publication: '+str(output))
    parent,history,files=historical_checkpoint()
    build,build_files=final_build(parent)
    files|=build_files|{Path(__file__).resolve()}
    # Retain the complete earlier dependency set plus the new helper's static
    # closure. Historical helper mains and evidence checkers are never called.
    files=python_dependencies(files)
    require(all(path.is_file() and path.is_relative_to(ROOT) for path in files),'complete pin closure')
    result=dict(schema='native-edge-isotropy-theory-publication-v1',passed=True,maintained_native_sources_changed=False,
        tests=408,test_modules=45,skipped_tests=0,tested_files=363,native_modules=299,
        retained_test_coverage=True,new_tests_run=0,new_recognition_calls=0,
        new_original_diagram_chain_replays=0,historical_checkpoint=history,**build,
        finite_audit_results_claimed=False,
        general_quasipolynomial=False,native_separator_lower_bound_claimed=False,
        new_timing_claims=False,tests_or_build_run_by_this_helper=False,
        solver_discovery_run_by_this_helper=False,certificate_replay_run_by_this_helper=False,
        historical_publication_mains_executed=False,
        files_sha256={str(path.relative_to(ROOT)):digest(path) for path in sorted(files)})
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({key:value for key,value in result.items() if key!='files_sha256'},sort_keys=True))


if __name__=='__main__':
    main()
