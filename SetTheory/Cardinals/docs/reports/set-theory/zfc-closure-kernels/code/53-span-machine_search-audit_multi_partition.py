#!/usr/bin/env python3
"""Check every lazy partition step and exact remaining frontier.

Arithmetic uses Python integers. This audits coverage of the finite checker
family, not semantic correctness of the checker or of rejected machines.
"""
import argparse,csv,hashlib,json
from collections import Counter,defaultdict
from pathlib import Path

def digest_file(path):
    digest=hashlib.sha256()
    with path.open('rb')as source:
        for chunk in iter(lambda:source.read(1024*1024),b''):digest.update(chunk)
    return digest.hexdigest()

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--prefix',type=Path,required=True)
    ap.add_argument('--data',type=Path,required=True);ap.add_argument('--min-degree',type=int,required=True)
    ap.add_argument('--max-degree',type=int,required=True);ap.add_argument('--actions',type=int,required=True)
    ap.add_argument('--source',type=Path,required=True);ap.add_argument('--output',type=Path,required=True)
    a=ap.parse_args();assert a.actions in(251,1008)
    fam=[]
    for line in(a.data/'family.tsv').read_text().splitlines():
        x=list(map(int,line.split()));d,q=x[:2]
        if a.min_degree<=d<=a.max_degree:fam.append((d,q))
    assert fam
    prefix=str(a.prefix);ledger=Path(prefix+'.ledger.tsv')
    summary=list(csv.DictReader(Path(prefix+'.summary.tsv').open(),delimiter='\t'))
    supplied=defaultdict(list)
    for line in Path(prefix+'.frontier.tsv').read_text().splitlines():
        g,q,assign,w=line.split('\t');g,q,w=map(int,(g,q,w));assign=tuple(map(int,assign.split(',')))
        assert(g<len(fam)and fam[g]==(len(assign),q))
        assert w==a.actions**sum(v<0 for v in assign)
        supplied[g].append((assign,w))
    counts=Counter();by=[];group=-1;stack=[];totals=Counter();per_reasons=Counter()
    def finish():
        nonlocal stack,totals,per_reasons
        if group<0:return
        d,q=fam[group]
        expected=[(node,a.actions**sum(v<0 for v in node))for node in stack]
        assert supplied[group]==expected,('frontier_mismatch',group)
        remaining=sum(w for node,w in expected)
        assert a.actions**d==totals['pruned']+totals['survivors']+remaining
        row=summary[group]
        assert int(row['group'])==group and int(row['deleted'])==q and int(row['degree'])==d
        for name,value in(('planned',a.actions**d),('pruned',totals['pruned']),('survivors',totals['survivors']),('remaining',remaining),('nodes',totals['nodes'])):
            assert int(row[name])==value,(group,name,row[name],value)
        by.append({'group':group,'deleted':q,'degree':d,'planned':a.actions**d,'pruned':totals['pruned'],
            'remaining':remaining,'survivors':totals['survivors'],'nodes':totals['nodes'],'branches':totals['branches'],
            'failure_reasons':dict(per_reasons),'frontier_nodes':len(expected),'checks':int(row['checks'])})
    for v in csv.DictReader(ledger.open(),delimiter='\t'):
        g,q=int(v['group']),int(v['deleted']);assign=tuple(map(int,v['assignments'].split(',')))
        if g!=group:
            finish();assert g==group+1 and not stack
            group=g;stack=[tuple([-1]*fam[group][0])];totals=Counter();per_reasons=Counter()
        assert fam[group]==(len(assign),q)
        assert stack and stack.pop()==assign,('traversal_mismatch',group,assign)
        assert all(-1<=x<a.actions for x in assign)
        totals['nodes']+=1;outcome=v['outcome'];index=int(v['case_or_needed']);reason=int(v['reason']);w=int(v['weight'])
        if outcome=='branch':
            assert 0<=index<len(assign)and assign[index]<0 and reason==0 and w==0
            for choice in reversed(range(a.actions)):
                nxt=list(assign);nxt[index]=choice;stack.append(tuple(nxt))
            totals['branches']+=1
        elif outcome=='prune':
            assert 0<=index<8391 and reason in(1,2,3,4,5)
            assert w==a.actions**sum(x<0 for x in assign)
            totals['pruned']+=w;per_reasons[reason]+=1
        else:
            assert outcome=='survivor'and min(assign)>=0 and w==1;totals['survivors']+=1
        counts[outcome]+=1
    finish();assert len(summary)==group+1
    for g in range(group+1,len(fam)):
        d,q=fam[g];node=tuple([-1]*d);planned=a.actions**d
        assert supplied[g]==[(node,planned)]
        by.append({'group':g,'deleted':q,'degree':d,'planned':planned,'pruned':0,'remaining':planned,
                   'survivors':0,'nodes':0,'branches':0,'failure_reasons':{},'frontier_nodes':1,'checks':0})
    total={k:sum(x[k]for x in by)for k in('planned','pruned','remaining','survivors','nodes','branches','frontier_nodes','checks')}
    assert total['planned']==total['pruned']+total['remaining']+total['survivors']
    r={'status':'PASS','scope':'Complete arithmetic branch/prune/frontier partition audit, without rerunning affine failures.',
       'actions_per_incoming':a.actions,'min_degree':a.min_degree,'max_degree':a.max_degree,
       **total,'outcomes':dict(counts),'per_group':by,'source_sha256':hashlib.sha256(a.source.read_bytes()).hexdigest(),
       'ledger_sha256':digest_file(ledger),'ledger_bytes':ledger.stat().st_size,
       'elapsed_seconds':float(summary[-1]['seconds']) if summary else 0,
       'checks_include_interrupted_lookups':True}
    a.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items()if k!='per_group'}))

if __name__=='__main__':main()
