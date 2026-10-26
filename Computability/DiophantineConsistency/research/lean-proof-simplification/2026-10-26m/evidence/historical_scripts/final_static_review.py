from pathlib import Path
import hashlib, json, re

ROOT=Path('/workspace/scratch/1d789f58b615')
BASE=ROOT/'ProveIt'
PROPOSED=ROOT/'proposed'

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def mask_comments(s):
    out=list(s);i=0;depth=0;string=False
    while i<len(s):
        if depth:
            if s.startswith('/-',i):
                out[i]=out[i+1]=' ';depth+=1;i+=2;continue
            if s.startswith('-/',i):
                out[i]=out[i+1]=' ';depth-=1;i+=2;continue
            if s[i]!='\n':out[i]=' '
            i+=1;continue
        if string:
            if s[i]=='\\':i+=2;continue
            if s[i]=='"':string=False
            i+=1;continue
        if s[i]=='"':string=True;i+=1;continue
        if s.startswith('/-',i):out[i]=out[i+1]=' ';depth=1;i+=2;continue
        if s.startswith('--',i):
            j=s.find('\n',i)
            if j<0:j=len(s)
            for k in range(i,j):out[k]=' '
            i=j;continue
        i+=1
    assert depth==0
    return ''.join(out)

decl=re.compile(r'^(?P<attr>(?:@\[[^\n]*?\]\s*)*)(?P<mod>(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*)(?P<kind>theorem|lemma|def|abbrev|structure|inductive|opaque|axiom)\s+(?P<name>[^\s({:]+)',re.M)
command=re.compile(r'^(?:@\[[^\n]*?\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(?:theorem|lemma|def|abbrev|structure|inductive|opaque|axiom|namespace|section|end|open|variable|attribute|import|set_option|#print|#check|#eval)\b',re.M)

def parse(p):
    text=p.read_text();masked=mask_comments(text);commands=list(command.finditer(masked));scope=[];result={}
    for idx,c in enumerate(commands):
        end=commands[idx+1].start() if idx+1<len(commands) else len(masked)
        segment=masked[c.start():end]
        line=segment.splitlines()[0]
        if line.startswith('namespace '):scope.append(('namespace',line.split()[1]));continue
        if line.startswith('section'):scope.append(('section',''));continue
        if line.startswith('end'):
            if scope:scope.pop()
            continue
        d=decl.match(segment)
        if not d:continue
        name='.'.join([v for k,v in scope if k=='namespace']+[d['name']])
        assert name not in result,(p,name)
        sep=segment.find(':=')
        if sep<0:sep=len(segment)
        header=' '.join(segment[:sep].split())
        body=' '.join(segment[sep:].split())
        result[name]={'kind':d['kind'],'line':masked[:c.start()].count('\n')+1,'header':header,'body':body,'source_span':[c.start(),end],'private':'private' in d['mod'].split(),'attributes':d['attr'].strip()}
    return result

expected_changed={
'DiophantineConsistency.GraphRep.unpairLeftCoordinate',
'DiophantineConsistency.GraphRep.unpairRightCoordinate',
'DiophantineConsistency.QuadraticNatPairing.pairRepresentation',
'DiophantineConsistency.QuadraticNatPairing.leftRepresentation',
'DiophantineConsistency.QuadraticNatPairing.rightRepresentation',
'DiophantineConsistency.QuadraticTreeCodeGraphs.treeLeftRepresentation',
'DiophantineConsistency.QuadraticTreeCodeGraphs.treeRightRepresentation',
'DiophantineConsistency.QuadraticBoolean.zeroRepresentation',
'DiophantineConsistency.QuadraticBoolean.conditionalRepresentation',
}

experiment_paths=[ROOT/'experiments/structural/PairingClients.lean',ROOT/'experiments/structural/BooleanClients.lean']
tested={}
for p in experiment_paths:
    for n,d in parse(p).items():tested[n]=(p,d)

files=[];existing_total=0;data_total=0;changed_seen=set()
for p in sorted(PROPOSED.rglob('*.lean')):
    rel=p.relative_to(PROPOSED);old=BASE/rel;b=parse(p);a=parse(old) if old.exists() else {}
    status={'path':str(rel),'old_lines':len(old.read_text().splitlines()) if old.exists() else 0,'new_lines':len(p.read_text().splitlines()),'old_bytes':old.stat().st_size if old.exists() else 0,'new_bytes':p.stat().st_size,'old_sha256':sha(old) if old.exists() else None,'new_sha256':sha(p),'removed':sorted(set(a)-set(b)),'added':sorted(set(b)-set(a)),'changed_signatures':[],'computational_definitions':[]}
    for n,x in a.items():
        existing_total+=1
        if n not in b:continue
        y=b[n]
        if x['header']!=y['header']:status['changed_signatures'].append({'name':n,'old':x['header'],'new':y['header']})
        if x['kind'] in ('def','abbrev','opaque','structure','inductive'):
            data_total+=1
            entry={'name':n,'kind':x['kind'],'body_unchanged_ignoring_comments_whitespace':x['body']==y['body']}
            if x['body']!=y['body']:
                changed_seen.add(n)
                entry['expected_proof_only_constructor_change']=n in expected_changed
                q,z=tested[n+'_short']
                entry['matches_compiled_short_constructor_body']=y['body']==z['body']
                entry['compiled_constructor_source']=str(q.relative_to(ROOT))
                entry['compiled_constructor_source_sha256']=sha(q)
                eq=tested[n+'_short_eq'][1]
                entry['equality_theorem']=n+'_short_eq'
                entry['equality_proof_is_rfl']=eq['body']==':= rfl'
                # All proof-only consumer changes start at `intro v`.
                before=x['body'].split('intro v',1)[0]
                after=y['body'].split('intro v',1)[0]
                entry['constructor_data_prefix_unchanged']=before==after
            status['computational_definitions'].append(entry)
    files.append(status)

totals={k:sum(f[k] for f in files) for k in ('old_lines','new_lines','old_bytes','new_bytes')}
totals['saved_lines']=totals['old_lines']-totals['new_lines'];totals['saved_bytes']=totals['old_bytes']-totals['new_bytes']
checks={'all_existing_signatures_unchanged':not any(f['changed_signatures'] for f in files),'no_existing_declarations_removed':not any(f['removed'] for f in files),'changed_computational_declarations_exactly_expected':changed_seen==expected_changed,'all_nine_tested_bodies_match':all(x.get('matches_compiled_short_constructor_body',True) for f in files for x in f['computational_definitions']),'all_nine_equality_proofs_are_rfl':all(x.get('equality_proof_is_rfl',True) for f in files for x in f['computational_definitions']),'all_nine_constructor_data_prefixes_unchanged':all(x.get('constructor_data_prefix_unchanged',True) for f in files for x in f['computational_definitions']),'expected_line_totals':totals['old_lines']==1999 and totals['new_lines']==1893}
report=ROOT/'output/additional_lean_simplifications_2026-10-26/report/additional_lean_simplifications.tex'
out={'repository_commit':'7fa06d530df54d4aeb2e18027409df082234c69e','method':'Namespace-qualified source parser, with nested Lean comments masked. Existing declaration headers compared after whitespace normalization; every computational declaration body compared. This is a static source check, not an independent Lean environment/type audit. No additional compiler invocations performed. Existing compiler receipts for the nine whole-value rfl comparisons were inspected separately.','files':files,'totals':totals,'existing_declarations_compared':existing_total,'existing_computational_declarations_compared':data_total,'changed_constructor_count':len(changed_seen),'checks':checks,'report_review':{'path':str(report.relative_to(ROOT)),'sha256_at_static_pass':sha(report),'complete_at_static_pass':'\\end{document}' in report.read_text(),'status':'Pending complete manuscript review.'}}
(ROOT/'final_review.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'checks':checks,'totals':totals,'existing_declarations':existing_total,'existing_computational_declarations':data_total},indent=2))
