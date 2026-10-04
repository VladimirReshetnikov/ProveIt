#!/usr/bin/env python3
"""Independent authentication of a frozen review receipt. No predecessor execution."""
from pathlib import Path
import argparse
import collections
import hashlib
import json
import re
import subprocess

ROOT = Path('/home/codex/.codex/worktrees/2a71/Proofs')
INPUT = Path('/tmp/review_reciprocal_c70ced0dd')
OUTPUT = Path('/tmp/reauth_reciprocal_c70ced0dd.json')
PINS = {'md':'2734c01162e098d281143d320ca5f343cdfc5c0df5e925710e55b8e2879bcf28',
        'json':'e1b112cf454b61783078b57d8fc145a7ed6dff59820104510615f63dfd02b010',
        'py':'54d445aa245b50def87c0e1ddb6959281cca30ef39672b77a15dbacb40407494'}
CHECKS = []
CACHE = {}

def sha(b):
    return hashlib.sha256(b).hexdigest()

def check(ok, name):
    if not ok:
        raise ValueError(name)
    CHECKS.append(name)

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)

def content(c, p):
    key = (c,p)
    if key not in CACHE:
        CACHE[key] = git('show',c+':'+p)
    return CACHE[key]

def normalized(b):
    return b.decode('utf-8').replace('\r\n','\n').replace('\r','\n')

def authenticate(record, title):
    c,p = record['commit'],record['path']
    b = content(c,p)
    oid = git('rev-parse',c+':'+p).decode().strip()
    check(oid == record['blob'],title+' blob')
    check(len(b) == record['bytes'],title+' bytes')
    check(sha(b) == record['sha256'],title+' SHA256')
    return b

def label_list(b):
    return re.findall(r'\\label\s*(?:\[[^\]]*\])?\s*\{([^}]+)\}',b.decode())

def bib_list(b):
    return re.findall(r'\\bibitem\s*(?:\[[^\]]*\])?\s*\{([^}]+)\}',b.decode())

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--expect',type=Path)
    args = ap.parse_args()
    input_records = []
    for extension,expected in PINS.items():
        path = INPUT.with_suffix('.'+extension)
        raw = path.read_bytes()
        check(sha(raw) == expected,'frozen input '+extension)
        input_records.append({'path':str(path),'bytes':len(raw),'sha256':sha(raw)})
    review = json.loads(INPUT.with_suffix('.json').read_bytes())
    commits = {x['commit']:x['parent'] for x in review['commits']}
    for c,parent in commits.items():
        check(git('rev-parse',c+'^').decode().strip() == parent,'commit parent '+c)
        paths = git('diff-tree','--no-commit-id','--name-only','-r',c).decode().splitlines()
        recorded = [f['path'] for f in review['files'] if f['after']['commit'] == c]
        check(paths == recorded,'complete ordered changed-file list '+c)
    diffs = []
    declarations = []
    rebuilt_crossrefs = []
    broad_crossrefs = []
    for k,f in enumerate(review['files']):
        before = authenticate(f['before'],'file'+str(k)+' before')
        after = authenticate(f['after'],'file'+str(k)+' after')
        c,p = f['after']['commit'],f['path']
        check(f['before']['commit'] == commits[c] and f['before']['path'] == p,'file path/commit relation '+str(k))
        d = git('diff','--no-ext-diff','--no-textconv','--unified=3',commits[c],c,'--',p)
        check(sha(d) == f['diff_sha256'],'diff hash '+str(k))
        check(len(d) == f['diff_bytes'],'diff bytes '+str(k))
        dr = {'commit':c,'path':p,'bytes':len(d),'sha256':sha(d)}
        if 'hunks' in f:
            lines = d.decode().splitlines()
            additions = [x[1:] for x in lines if x.startswith('+') and not x.startswith('+++')]
            deletions = [x[1:] for x in lines if x.startswith('-') and not x.startswith('---')]
            check(len(lines) == f['diff_line_count'],'diff line count '+str(k))
            check(len(additions) == f['added_lines'] and len(deletions) == f['removed_lines'],'diff add/delete count '+str(k))
            hs = []
            for line in lines:
                m = re.match(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@',line)
                if m:
                    a,an,b,bn = (int(m[1]),int(m[2] or 1),int(m[3]),int(m[4] or 1))
                    hs.append({'before_start':a,'before_count':an,'after_start':b,'after_count':bn})
            check(hs == f['hunks'],'diff hunk coordinates '+str(k))
            dr.update({'hunks':hs,'added':len(additions),'deleted':len(deletions)})
            if p.endswith('.tex'):
                added = '\n'.join(additions)
                for m in re.finditer(r'\\(?:lbl|replabel|cref|ref|leref|eqref)\{([^}]+)\}',added):
                    for lab in m[1].split(','):
                        rebuilt_crossrefs.append({'commit':c,'source_path':p,'label':lab})
                for m in re.finditer(r'\\(?:lbl|replabel|[Cc]ref|[Cc]pageref|ref|pageref|autoref|leref|eqref)\*?\s*(?:\[[^\]]*\])?\s*\{([^}]+)\}',added):
                    for lab in m[1].split(','):
                        broad_crossrefs.append({'commit':c,'source_path':p,'label':lab.strip()})
        diffs.append(dr)
        if 'labels' in f:
            old,new = label_list(before),label_list(after)
            rec = f['labels']
            check(len(old)==rec['before_count'] and len(new)==rec['after_count'],'label counts '+str(k))
            check(old==new and rec['ordered_unchanged'],'unchanged ordered labels '+str(k))
            encoding = json.dumps(new,ensure_ascii=False,separators=(',',':')).encode()
            check(sha(encoding)==rec['ordered_sha256'],'ordered label hash '+str(k))
            bo,bn = bib_list(before),bib_list(after)
            br = f['bibliography_keys']
            check(len(bo)==br['before_count'] and len(bn)==br['after_count'],'bibliography counts '+str(k))
            check(bo==bn and br['ordered_unchanged'],'unchanged ordered bibliography keys '+str(k))
            declarations.append({'commit':c,'path':p,'labels':new,'bibliography_keys':bn,'unchanged':True})
    reconstructed_spans = []
    for k,r in enumerate(review['human_read_spans']):
        b = authenticate(r,'spanfile'+str(k))
        check(r['normalization']=='UTF-8, CRLF/CR to LF, preserved final newline status','span normalization '+str(k))
        lines = normalized(b).splitlines(keepends=True)
        a,z = r['start_line'],r['end_line']
        check(1<=a<=z<=len(lines),'span bounds '+str(k))
        payload = ''.join(lines[a-1:z]).encode()
        check(sha(payload)==r['span_sha256'],'span hash '+str(k))
        reconstructed_spans.append({'commit':r['commit'],'path':r['path'],'start_line':a,'end_line':z,'bytes':len(payload),'sha256':sha(payload)})
    index = collections.defaultdict(lambda:collections.defaultdict(list))
    for k,r in enumerate(review['label_index_files']):
        b = authenticate(r,'indexfile'+str(k))
        for n,line in enumerate(b.decode().splitlines(),1):
            for label in re.findall(r'\\label\s*(?:\[[^\]]*\])?\s*\{([^}]+)\}',line):
                index[r['commit']][label].append({'path':r['path'],'line':n,'blob':r['blob']})
    check(len(rebuilt_crossrefs)==len(review['new_article_crossrefs']),'crossref list length')
    actual_matches = []
    for k,(base,r) in enumerate(zip(rebuilt_crossrefs,review['new_article_crossrefs'])):
        check(base=={x:r[x] for x in base},'crossref extraction '+str(k))
        matches = index[r['commit']][r['label']]
        key=lambda x:(x['path'],x['line'],x['blob'])
        check(sorted(matches,key=key)==sorted(r['matches'],key=key),'crossref target set '+str(k))
        check(bool(matches),'crossref resolved '+str(k))
        actual_matches.append({**base,'matches':matches})
    as_tuple = lambda r:(r['commit'],r['source_path'],r['label'])
    original_counts = collections.Counter(map(as_tuple,rebuilt_crossrefs))
    expanded_counts = collections.Counter(map(as_tuple,broad_crossrefs))
    check(not original_counts-expanded_counts,'expanded syntax includes every recorded reference')
    extra_references = []
    for (c,p,lab),number in (expanded_counts-original_counts).items():
        matches = index[c][lab]
        check(bool(matches),'additional expanded-syntax target resolved '+lab)
        extra_references.append({'commit':c,'source_path':p,'label':lab,'occurrences':number,'matches':matches})
    totals = {'changed_files':len(review['files']), 'text_files':sum('hunks' in x for x in review['files']),
              'pdf_files':sum(x['path'].endswith('.pdf') for x in review['files']),
              'text_additions':sum(x.get('added',0) for x in diffs), 'text_deletions':sum(x.get('deleted',0) for x in diffs),
              'human_read_span_records':len(reconstructed_spans), 'crossref_occurrences':len(actual_matches),
              'crossrefs_without_index_match':sum(not x['matches'] for x in actual_matches)}
    check(totals==review['totals'],'entire declared totals')
    result={'schema':'independent reciprocal-review reauthentication v1',
            'helper_sha256':sha(Path(__file__).read_bytes()),'inputs':input_records,
            'status':'PASS','issues':[], 'commits':review['commits'], 'diffs':diffs,
            'reauthenticated_spans':reconstructed_spans,'declaration_inventories':declarations,
            'matched_crossrefs':actual_matches,'declared_totals_reproduced':totals,
            'expanded_reference_check':{'occurrences':len(broad_crossrefs),'additional':extra_references,
                'explanation':'The original extractor handles lowercase cref but not uppercase Cref; these additional literal references are separately authenticated.'},
            'achieved_totals':{'file_record_instances':54+len(review['human_read_spans'])+len(review['label_index_files']),
                               'unique_git_files':len(CACHE), 'diffs':len(diffs),
                               'label_index_records':len(review['label_index_files']),
                               'unchanged_label_and_bibliography_lists':len(declarations),
                               'checks':len(CHECKS)},
            'check_names':CHECKS,
            'limits':['Authentication of declared read spans, not a claim that this reauthentication rereads their mathematics.',
                      'Literal labels/references and bibliography keys only; no macro expansion, PDF reference numbers or theorem-proof certification.',
                      'No archive/placement records exist in this review schema; none are claimed checked.',
                      'No current working-file corrections, builds, tests, external sources or historical execution results authenticated.',
                      'Original collector read only as inert schema documentation for hash serialization/extraction conventions; never executed or imported.']}
    out=(json.dumps(result,indent=2,ensure_ascii=False)+'\n').encode()
    if args.expect:
        check(out==args.expect.read_bytes(),'exact receipt replay')
    else:
        OUTPUT.write_bytes(out)
    print(json.dumps({'status':'PASS','receipt_sha256':sha(out),**result['achieved_totals'],**totals},sort_keys=True))

if __name__=='__main__':
    main()
