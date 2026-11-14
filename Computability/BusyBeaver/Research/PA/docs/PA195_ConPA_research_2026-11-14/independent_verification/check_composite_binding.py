"""Bind each composite's arithmetic command tails to the proved loop templates."""
from pathlib import Path
import sys,json,hashlib
HERE=Path(__file__).resolve().parent
BASE=HERE/'reference'
AX=BASE/'emitter'
sys.path.insert(0,str(BASE))
import source_language as s
sys.path.insert(0,str(AX))
import verify_emitter as emitter
OP={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}

def graph(rows):
    rows=[[p,OP[op],arg]for p,op,arg in rows]
    g,_=s.graph_arithmetic(rows);assert g==s.graph_intervals(rows)
    out=[]
    for eff,targets in g:
        op=eff[0]
        out.append(tuple([{'identity':'jump','increment':'inc','decrement':'dec','halt':'halt'}[op]]+eff[1:]+targets))
    return out

def main():
    reports=[]
    for family in ['diagonal196','separate196']:
        old_rows=json.loads((AX/family/'sites.json').read_text())
        old=graph([(r['path'],r['op'],r['arg'])for r in old_rows])
        inp=HERE/'inputs'/family
        new_rows=json.loads((inp/'sites.json').read_text())
        new=graph(new_rows)
        n=len(new);assert len(old)==n+24
        E,F,S=n-15,n-12,n-11
        oldF,oldS=len(old)-13,len(old)-12
        relocate={oldF:F,oldS:S}
        changed=[]
        for i in range(E):
            oi,ni=old[i],new[i]
            nargs=1 if oi[0]=='jump' else 2
            if oi[0]=='halt':assert oi==ni;continue
            expect=oi[:nargs]+tuple(relocate.get(t,t)for t in oi[nargs:])
            assert expect==ni,(family,i,oi,ni,expect)
            if oi!=ni:changed.append([i,list(oi),list(ni)])
        expected=[('dec',4,F,E+1),('inc',5,E+2),('jump',E),('jump',25),
                  ('dec',1,S+2,S+1),('jump',S),('dec',5,S+6,S+3),
                  ('inc',1,S+4),('inc',6,S+5),('jump',S+2),
                  ('dec',6,S+9,S+7),('inc',5,S+8),('jump',S+6),
                  ('inc',6,S+10),('jump',0)]
        assert new[E:]==expected
        assert [row[0]for row in changed]==[48,n-96,n-16]
        emission=emitter.audit(family)
        report=dict(family=family,old_sites=len(old),new_sites=n,unchanged_prefix_sites=E,
                    ax_final_site=n-96,mp_success_entry=E,fetch_return=F,shift_entry=S,
                    relocated_rows=changed,exact_tail=[list(x)for x in expected],
                    old_emitter_free_algebra=emission,
                    source_sha256=hashlib.sha256((inp/'sites.json').read_bytes()).hexdigest(),
                    status='PASS',scope='finite source binding and exact emitter, not an endpoint kernel theorem')
        reports.append(report)
    out=HERE/'recorded/composite_binding.json';out.write_text(json.dumps(reports,indent=2)+'\n')
    print(json.dumps(reports,indent=2))

if __name__=='__main__':main()
