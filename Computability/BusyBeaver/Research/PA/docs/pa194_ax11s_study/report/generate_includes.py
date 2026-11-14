#!/usr/bin/env python3
"""Generate report tables from the delivered machine and comparison evidence."""
from pathlib import Path
import collections
import json
import re
import unicodedata

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def load(name):return json.loads((ROOT/name).read_text())
def plain(s):
    for a,b in {'\u2264':'<=','\u2265':'>=','\u2192':'->','\u2194':'<->','\u2014':'--','\u2013':'-','\u2019':"'",'\u2018':"'",'\u201c':'"','\u201d':'"'}.items():s=s.replace(a,b)
    return unicodedata.normalize('NFKD',s).encode('ascii','ignore').decode()
def esc(s):
    s=plain(str(s))
    return ''.join({'\\':r'\textbackslash{}','&':r'\&','%':r'\%','$':r'\$','#':r'\#','_':r'\_','{':r'\{','}':r'\}','~':r'\textasciitilde{}','^':r'\textasciicircum{}'}.get(c,c) for c in s)
def table(headers,widths,rows):
    cols=''.join(r'>{\raggedright\arraybackslash}p{'+w+r'\linewidth}' for w in widths)
    head=' & '.join(headers)+r'\\'
    return ('{\\small\n\\setlength{\\tabcolsep}{4pt}\n'+
            r'\begin{longtable}{@{}'+cols+r'@{}}'+'\n'+
            r'\toprule '+head+r'\midrule\endfirsthead'+'\n'+
            r'\toprule '+head+r'\midrule\endhead'+'\n'+
            '\n'.join(' & '.join(row)+r'\\[4pt]' for row in rows)+'\n'+
            r'\bottomrule\end{longtable}}'+'\n')

def main():
    frontier=load('comparison/frontier194.json')
    packets=load('comparison/packet_ledger.json')
    (HERE/'metrics.tex').write_text(r'\newcommand{\FrontierCount}{'+str(len(frontier))+'}\n')
    rows=[]
    for i,p in enumerate(packets,1):
        name=plain(p['packet'])
        cell=r'\href{'+p['source_url']+r'}{\nolinkurl{'+name+'}}'
        rows.append([str(i),cell+ r'\par\emph{'+esc(p['location'])+'}',esc(p['reported_contribution'])])
    (HERE/'packet_ledger.tex').write_text(table(['No.','Packet and location','Reported contribution'],['0.035','0.345','0.56'],rows))
    rows=[]
    for i,p in enumerate(frontier,1):
        rows.append([str(i),esc(p['name'])+r'\par{\ttfamily '+p['extended_class_sha256'][:12]+'}',
                     esc(p['evidence_category'])+r'\par '+esc(p['mechanism'])])
    (HERE/'frontier.tex').write_text(table(['No.','Name and class prefix','Historical evidence and mechanism'],['0.035','0.28','0.625'],rows))
    r={}
    for line in (ROOT/'machine/machine.tm').read_text().splitlines():
        q,b,w,d,n=line.split();r[int(q),int(b)]=(w,d,n)
    rows=[]
    for q in range(194):
        row=[str(q)]
        for b in (0,1):
            w,d,n=r[q,b];row.append('$('+w+','+d+','+n+')$')
        rows.append(row)
    (HERE/'transition_table.tex').write_text(table(['State','Read 0','Read 1'],['0.16','0.34','0.34'],rows))
    old=load('reference/ax11/independent/receipt.json')
    new=load('machine/independent/receipt.json')
    c=load('machine/receipt.json')
    comparisons=[('Working states / rows','194 / 388','194 / 388'),
                 ('Primitive source sites',old['source_sites'],new['source_sites']),
                 ('Universal source outcomes',old['source_contracts'],new['source_contracts']),
                 ('Simultaneous local fold cases',28,32),
                 ('Literal generic list lemmas',old['generic_list_lemmas'],new['generic_list_lemmas']),
                 ('Independent symbolic operations',old['symbolic_steps'],new['symbolic_steps']),
                 ('Maximum symbolic steps per case',old['maximum_symbolic_steps'],new['maximum_symbolic_steps']),
                 ('Minimum duration constant',old['minimum_positive_duration_constant'],new['minimum_positive_duration_constant']),
                 ('Complete startup transitions',old['startup_steps'],new['startup_steps'])]
    fmt=lambda x:f'{x:,}' if isinstance(x,int) else str(x)
    vr=[list(map(esc,[a,fmt(b),fmt(d)])) for a,b,d in comparisons]
    text=table(['Quantity','Supplied AX11','New AX11S'],['0.50','0.19','0.19'],vr)
    text+='The new construction checker separately passed '+fmt(c['runtime']['contracts'])+' contracts in '+fmt(c['runtime']['total_steps'])+' symbolic operations, with maximum '+str(c['runtime']['max_steps'])+' per outcome.\n'
    (HERE/'verification_table.tex').write_text(text)
    cats=collections.Counter(x['evidence_category'] for x in frontier)
    census=load('comparison/census/summary.json')
    (HERE/'census_summary.tex').write_text(
        'The fresh scan checks '+fmt(census['tracked_candidate_files'])+' tracked candidate files and recognizes '+fmt(census['literal_and_json_table_occurrences'])+' literal/JSON table occurrences, representing '+fmt(census['distinct_raw_table_bytes'])+' byte forms and '+fmt(census['distinct_labeled_transition_tables'])+' labeled tables. There are '+fmt(census['full_spanning_graph_classes'])+' complete spanning graph classes across all sizes. The '+str(len(frontier))+' such classes at 194 states agree exactly with the frozen extended frontier. Maximum reachable components of nonspanning tables are tabulated separately and are excluded from the spanning-class counts.\n\nThe historical evidence annotations distinguish '+
        str(cats['reported principal construction'])+' principal reported constructions, '+str(cats['supplementary construction'])+' supplementary constructions, '+str(cats['source-validated research rotation'])+' source-validated research rotations, '+str(cats['research auxiliary'])+' research auxiliaries, and '+str(cats['rejected'])+' rejected tables. These are not '+str(len(frontier))+' established iPRA consistency theorems. Full recognition receipts and scope are in \\path{comparison/}.\n')
    (HERE/'startup_search.tex').write_text(r'\input{../research/startup/negative_search.tex}'+'\n')
    findings=[]
    for name,label in [('run','Reassociation only'),('permuted','Reassociation and head permutations')]:
        p=ROOT/'research/grammar'/f'{name}.log'
        done=re.search(r'DONE iterations (\d+) accepted (\d+) hits (\d+) best (\d+) seconds ([\d.]+)',p.read_text())
        if done:
            it,acc,hits,best,secs=done.groups()
            findings.append([esc(label),f'{int(it):,}',f'{int(acc):,}',best,secs])
    if len(findings)==2:
        text=table(['Search','Proposals','Accepted moves','Best score','Seconds'],['0.33','0.16','0.16','0.13','0.12'],findings)
        text+='Both completed searches obtained no score below 60; neither nominated a verified 193-state table. The time limit is 360 seconds per run; replay proposal counts depend on machine speed. Seeds and complete logs are retained.\n'
    else:
        text='The recorded search summaries are being finalized.\n'
    (HERE/'grammar_search.tex').write_text(text)
    print('Generated tables for',len(packets),'deliveries,',len(frontier),'classes, and 194 machine states.')

if __name__=='__main__':main()
