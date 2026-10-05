#!/usr/bin/env python3
"""Fresh read-only byte/route collector. No delivered or earlier program is run."""
import argparse
import collections
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import zipfile

ROOT = Path('/home/codex/.codex/worktrees/2a71/Proofs')
COMMIT = '62b16914ebf724b672badca7d4851f90b2ba6f2b'
ARRIVAL = 'e3839ad2c6be32ac5c6fdc422507da07f85f4fb6'
PLACEMENT = '111c380120cb27a886eb8be5df1920d31e3d111c'
HOST = 'Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders/'
WIP = 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/'
LABEL = re.compile(r'\\label(?:\[[^\]]*\])?\{([^{}]+)\}')
REF = re.compile(r'\\(?:[cC]ref|eqref|ref|pageref|autoref)\*?\{([^{}]+)\}')

def require(ok, message):
    if not ok:
        raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)

def raw(commit, path):
    return git('show', commit + ':' + path)

def pin(commit, path):
    data = raw(commit, path)
    return {'commit': commit, 'path': path,
            'blob': git('rev-parse', commit + ':' + path).decode().strip(),
            'bytes': len(data), 'sha256': sha(data)}

def span(data, first, last):
    lines = data.decode('utf-8').splitlines()
    require(1 <= first <= last <= len(lines), 'invalid read span')
    normalized = ('\n'.join(lines[first-1:last]) + '\n').encode()
    return {'first_line': first, 'last_line': last, 'lines': last-first+1,
            'normalized_utf8_bytes': len(normalized), 'sha256': sha(normalized)}

def merge_ranges(ranges):
    out = []
    for a, b in sorted(ranges):
        if out and a <= out[-1][1]+1:
            out[-1][1] = max(out[-1][1], b)
        else:
            out.append([a,b])
    return out

def read_context(commit, path, ranges, scope):
    data = raw(commit, path)
    if ranges == 'full':
        ranges = [(1,len(data.decode().splitlines()))]
    return dict(pin(commit,path), scope=scope,
                read_spans=[span(data,a,b) for a,b in merge_ranges(ranges)])

def labels(data):
    return [{'label':m.group(1), 'line':data[:m.start()].count('\n')+1}
            for m in LABEL.finditer(data)]

def main():
    parent = git('rev-parse', COMMIT+'^').decode().strip()
    intake_path = WIP+'review_beyond_ord_e3839ad2c.json'
    placement_path = WIP+'review_beyond_ord_placement_111c38012.json'
    intake = json.loads(raw(COMMIT,intake_path))
    placed = json.loads(raw(COMMIT,placement_path))
    require(intake['arrival_commit']==ARRIVAL, 'arrival mismatch')
    require(placed['placement']==PLACEMENT, 'placement mismatch')
    changes = []
    changed_paths = git('diff-tree','--no-commit-id','--name-only','-r',COMMIT).decode().splitlines()
    require(set(changed_paths)=={HOST+n for n in ['README.md','article.tex','article.pdf']}, 'changed paths')
    for path in changed_paths:
        diff = git('diff','--no-ext-diff','--no-renames','--unified=3',parent,COMMIT,'--',path)
        ranges = []
        if path.endswith('README.md'):
            ranges = [(1,len(diff.decode().splitlines()))]
        elif path.endswith('article.tex'):
            ranges = [(1,520)]
        changes.append({'path':path,'before':pin(parent,path),'after':pin(COMMIT,path),
                        'diff_bytes':len(diff),'diff_sha256':sha(diff),
                        'diff_line_count':len(diff.decode().splitlines()),
                        'diff_read_spans':[span(diff,a,b) for a,b in ranges],
                        'coverage':('complete raw guide diff' if path.endswith('README.md') else
                                    'first 520 raw diff lines and separate selected source spans' if path.endswith('.tex') else
                                    'binary metadata only; not rendered')})
    article=raw(COMMIT,HOST+'article.tex').decode()
    oldarticle=raw(parent,HOST+'article.tex').decode()
    nowlabels=labels(article); beforelabels=labels(oldarticle)
    labelmap=collections.defaultdict(list)
    for x in nowlabels: labelmap[x['label']].append(x['line'])
    require(all(len(v)==1 for v in labelmap.values()),'duplicate literal label')
    require({x['label'] for x in beforelabels} <= set(labelmap),'old label disappeared')
    prefix = {'Beyond_Ord_Class_Well_Orders.zip':'swo:dh:',
              'Beyond_Ord_Research.zip':'swo:dc:', 'beyond_ord.zip':'swo:bo:',
              'class_orders_beyond_ord.zip':'swo:fc:'}
    archives=[]; source_routes=[]; member_data={}; old_archive_read=[]
    for old in intake['archives']:
        path=old['path']; data=raw(ARRIVAL,path)
        require(sha(data)==old['sha256'],'old archive pin')
        archive=dict(pin(ARRIVAL,path),members=[],checksum_matches=[])
        with zipfile.ZipFile(io.BytesIO(data)) as z:
            infos=[i for i in z.infolist() if not i.is_dir()]
            require(len({i.filename for i in infos})==len(infos),'duplicate ZIP member')
            oldmembers={m['path']:m for m in old['members']}
            require(set(oldmembers)=={i.filename for i in infos},'ZIP census changed')
            for info in infos:
                body=z.read(info); m=oldmembers[info.filename]
                require(len(body)==m['bytes'] and sha(body)==m['sha256'],'member pin')
                member_data[(path,info.filename)]=body
                record={'path':info.filename,'bytes':len(body),'sha256':sha(body),
                        'crc32':f'{info.CRC:08x}','compressed_bytes':info.compress_size,
                        'coverage':'metadata; no new manuscript read inferred',
                        'executed_or_imported':False,'prior_read_spans_reauthenticated':[]}
                for s in m.get('read_spans',[]):
                    actual=span(body,s['first_line'],s['last_line'])
                    require(actual['sha256']==s['sha256'],'prior read span mismatch')
                    record['prior_read_spans_reauthenticated'].append(actual)
                    old_archive_read.append((info.filename,actual['lines']))
                if info.filename.endswith('.tex'):
                    record['literal_labels']=labels(body.decode())
                    routes=[]
                    for x in record['literal_labels']:
                        target=prefix[Path(path).name]+x['label']
                        require(target in labelmap,'source label missing: '+target)
                        routes.append({'source_label':x['label'],'source_line':x['line'],
                                       'target_label':target,'target_line':labelmap[target][0]})
                    source_routes.append({'archive':path,'member':info.filename,
                                          'sha256':sha(body),'prefix':prefix[Path(path).name],
                                          'routes':routes,
                                          'scope':'Literal locators only; not statement or body equivalence.'})
                archive['members'].append(record)
            for check in old['checksum_matches']:
                manifest=z.read(check['manifest']).decode()
                target=check['target']; digest=sha(z.read(target))
                matching=[]
                for line in manifest.splitlines():
                    match=re.match(r'^([0-9a-fA-F]{64})\s+[* ]?(.+?)\s*$',line)
                    if match and (Path(check['manifest']).parent/ match.group(2)).as_posix()==target:
                        matching.append(match.group(1).lower())
                require(matching==[digest] and digest==check['sha256'],'delivered checksum')
                archive['checksum_matches'].append({'manifest':check['manifest'],'target':target,
                                                    'sha256':digest,'matches':True})
        archives.append(archive)
    placements=[]
    for old in placed['changes']:
        if old['status']!='A': continue
        data=member_data[(old['archive'],old['member'])]
        at_placement=raw(PLACEMENT,old['path']); at_publication=raw(COMMIT,old['path'])
        require(data==at_placement==at_publication,'placement bytes differ')
        placements.append({'archive':old['archive'],'member':old['member'],
                           'source_sha256':sha(data),'first_placement':pin(PLACEMENT,old['path']),
                           'at_publication':pin(COMMIT,old['path']),'matches':True})
    prior_contexts=[]
    for c in intake['contexts']:
        data=raw(c['commit'],c['path'])
        require(sha(data)==c['sha256'],'prior context pin')
        rr=[]
        for s in c['read_spans']:
            got=span(data,s['first_line'],s['last_line'])
            require(got['sha256']==s['sha256'],'old context span')
            rr.append(got)
        prior_contexts.append(dict(pin(c['commit'],c['path']),read_spans_reauthenticated=rr,
                                   scope='Previously read, byte reauthentication only this turn.'))
    article_ranges=[(54888,55186),(55360,55458),(57498,57625),(57745,57830),
                    (58403,58523),(64268,64384),(66870,66910)]
    guide_ranges=[(440,477),(958,995),(1492,1532)]
    contexts=[read_context(COMMIT,HOST+'article.tex',article_ranges,'Selected current interfaces/proof/editorial text; not full body.'),
              read_context(COMMIT,HOST+'README.md',guide_ranges,'Additional exact postimage reads; full diff separately recorded.'),
              read_context(COMMIT,'Algebra/SurrealNumbers/AGENTS.md','full','Applicable instructions.'),
              read_context(COMMIT,'docs/incoming/README.md',[(426,440)],'Retention rule.'),
              read_context(COMMIT,WIP+'review_beyond_ord_e3839ad2c.md','full','Earlier bounded intake; no inherited unread-proof coverage.'),
              read_context(COMMIT,WIP+'review_beyond_ord_placement_111c38012.md','full','Earlier placement-only scope.'),
              read_context(COMMIT,WIP+'ordinal_two_type_effectivity_boundary.md','full','Promised two-type effectivity obstruction.'),
              read_context(COMMIT,'SetTheory/ZF/Lean/ZF/Zf.lean',[(1,42),(108,145)],'Static declaration/import names; no Lean build.'),
              read_context(COMMIT,'SetTheory/ZF/Lean/lakefile.toml','full','Static package context.'),
              read_context(COMMIT,'lake-manifest.json',[(1,22)],'Actual Mathlib dependency pin.'),
              read_context(COMMIT,'Algebra/SurrealNumbers/lake-manifest.json',[(1,17)],'Actual local Mathlib dependency pin.'),
              read_context('8f7d4a5c8','lake-manifest.json',[(1,15)],'Source32 historic repository Mathlib pin.'),
              read_context(COMMIT,HOST+'code/35-completion-finite_notation_checks.py',[(109,163)],'Static last55 lines only; never executed/imported.')]
    refs=[]
    for first,last in merge_ranges(article_ranges):
        start=sum(len(s) for s in article.splitlines(keepends=True)[:first-1])
        part=''.join(article.splitlines(keepends=True)[first-1:last])
        for m in REF.finditer(part):
            for target in m.group(1).split(','):
                target=target.strip()
                refs.append({'line':first+part[:m.start()].count('\n'),'target':target,
                             'target_lines':labelmap.get(target,[]),'resolves':target in labelmap})
    require(all(x['resolves'] for x in refs),'selected literal reference unresolved')
    rootmanifest=json.loads(raw(COMMIT,'lake-manifest.json'))
    package=next(p for p in rootmanifest['packages'] if p['name']=='mathlib')
    require(package['inputRev']=='v4.32.0','unexpected actual mathlib version')
    tex_lines=sum(n for p,n in old_archive_read if p.endswith('.tex'))
    all_lines=sum(n for p,n in old_archive_read)
    require(tex_lines==1665 and all_lines==2468,'read-count finding')
    output={'schema':'review_beyond_ord_write/v1','commit':COMMIT,'parent':parent,
            'arrival':ARRIVAL,'placement':PLACEMENT,
            'reviewer_helper_sha256':sha(Path(__file__).read_bytes()),
            'changed_files':changes,'contexts':contexts,
            'prior_receipts':[pin(COMMIT,intake_path),pin(COMMIT,placement_path)],
            'archives':archives,'placements':placements,'prior_contexts_reauthenticated':prior_contexts,
            'source_label_routes':source_routes,
            'labels':{'before':beforelabels,'after':nowlabels,
                      'added':sorted(set(labelmap)-{x['label'] for x in beforelabels}),
                      'deleted':[],'duplicates':[],
                      'scope':'Literal source labels only; not TeX expansion/build.'},
            'selected_literal_references':refs,
            'actual_mathlib_package':package,
            'prior_archive_read_census':{'tex':tex_lines,'other':all_lines-tex_lines,'total':all_lines},
            'findings':[
                {'id':'R1','location':'README.md1513;article.tex58499–58500','kind':'coverage provenance',
                 'claim':'2,468 selected lines of the four manuscripts',
                 'correction':'2,468 archive-member lines, comprising 1,665 TeX manuscript lines and 803 other lines.'},
                {'id':'R2','location':'README.md976–977;article.tex57615–57620','kind':'dependency metadata',
                 'claim':'repository pins Mathlib v4.31.0','correction':'Both manifests pin v4.32.0; no independent Mathlib API/deprecation audit.'},
                {'id':'R3','location':'README.md465–467','kind':'output-path metadata',
                 'claim':'source35 writes artifacts/finite_notation_results.json relative to cwd',
                 'correction':'Actual source line 161 uses Path(__file__).with_name: beside the script.'}],
            'scope':{'repository_mutated':False,'supplied_programs_executed':False,
                     'predecessor_or_frozen_helpers_executed':False,'builds_run':False,
                     'PDFs_read_or_rendered':False,'whole_manuscripts_certified':False,
                     'whole_normalized_body_equivalence_claimed':False,'external_citations_verified':False,
                     'fresh_own_metadata_only':True,'new_ordinary_integer_compiler_established':False}}
    output['totals']={'changed_files':len(changes),'before_after_blobs':2*len(changes),
                      'archives':len(archives),'members':sum(len(a['members']) for a in archives),
                      'delivered_checksums':sum(len(a['checksum_matches']) for a in archives),
                      'placed_files':len(placements),'source_label_routes':sum(len(s['routes']) for s in source_routes),
                      'labels_before':len(beforelabels),'labels_after':len(nowlabels),'labels_added':len(output['labels']['added']),
                      'guide_diff_read_lines':next(c['diff_line_count'] for c in changes if c['path'].endswith('README.md')),
                      'article_raw_diff_read_lines':520,
                      'current_article_selected_lines':sum(b-a+1 for a,b in merge_ranges(article_ranges)),
                      'current_context_read_spans':sum(len(c['read_spans']) for c in contexts),
                      'selected_literal_reference_occurrences':len(refs)}
    peer=[]
    for extension,expected in [('md','f79d9caf8a3d51c9b7850d8833b04650ea7f6d60dca26bf847bfa3f019c027e6'),
                               ('json','aa2759996a6fd225ece66ea39edee693b71c07cf0839d486c44b8e06b0df604a')]:
        path=Path('/tmp/review_beyond_ord_gb_62b16914e.'+extension)
        data=path.read_bytes(); require(sha(data)==expected,'peer review pin')
        peer.append({'path':path.name,'bytes':len(data),'sha256':sha(data),
                     'coverage':'full review prose read' if extension=='md' else 'receipt pin and schema only; separate peer span census'})
    output['independent_proof_review']=peer
    parser=argparse.ArgumentParser();group=parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--output');group.add_argument('--check');args=parser.parse_args()
    encoded=(json.dumps(output,indent=2,sort_keys=True)+'\n').encode()
    if args.output:
        with open(args.output,'xb') as f: f.write(encoded)
    else:
        require(Path(args.check).read_bytes()==encoded,'receipt replay mismatch')
    print(json.dumps({'status':'PASS','totals':output['totals']},sort_keys=True))

if __name__=='__main__':
    main()
