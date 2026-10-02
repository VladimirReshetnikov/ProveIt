"""Rebuild the complete matrix from the compact definition in the article."""
from pathlib import Path
import hashlib,json
from verify_frontend import NAMES,INDEX,read_sources
ROOT=Path(__file__).resolve().parents[1]

def build():
    _,source,table,_=read_sources(); rows={}
    for D,O in [('Left','Right'),('Right','Left')]:
        r={n:0 for n in NAMES};r[D+'Tape']=10
        for n in [D+'Mult',D+'Div0',D+'Div1']:r[n]=9
        rows[D+'Tape']=r
        r={n:0 for n in NAMES};r[D+'Temp']=8;r[D+'Trans']=7;rows[D+'Temp']=r
        r={n:2 for n in NAMES};r[D+'Tape']=4;r[D+'Temp']=0;rows[D+'Trans']=r
        r={n:2 for n in NAMES};r[D+'Tape']=0;r[D+'Temp']=6;rows[D+'Mult']=r
        for s in range(2):
            r={n:2 for n in NAMES};r[D+'Tape']=0;r[D+'Temp']=2+2*s
            for O2 in ['Left','Right']:
                r[O2+'Div'+str(s)]=3;r[O2+'Div'+str(1-s)]=1
            for q in range(15):r['Trans'+chr(65+q)+str(s)]=3;r['Trans'+chr(65+q)+str(1-s)]=1
            rows[D+'Div'+str(s)]=r
            r={n:9 for n in NAMES};r[D+'Write'+str(s)]=11;r[O+'Mult']=0;r[D+'Tape']=5+2*s
            for n in ['Temp','Trans','Mult']:r[D+n]=5
            r[D+'Div0']=r[D+'Div1']=0;rows[D+'Write'+str(s)]=r
    for q,cell in enumerate(table):
        for s in range(2):
            name='Trans'+chr(65+q)+str(s);rule=cell[3*s:3*s+3]
            if rule=='---':rows[name]={n:0 for n in NAMES};continue
            w=int(rule[0]);D='Left' if rule[1]=='L' else 'Right';O='Right' if D=='Left' else 'Left';qn=ord(rule[2])-65
            r={D+'Tape':0,D+'Temp':2,D+'Trans':3,D+'Mult':10,O+'Tape':4,O+'Temp':6,O+'Trans':7,O+'Mult':5}
            for t in range(2):
                a=int(t==s)-int(t==0)
                r[D+'Div'+str(t)]=1+a;r[O+'Div'+str(t)]=10+a
                r[D+'Write'+str(t)]=10;r[O+'Write'+str(t)]=8 if t==w else 10
                for u in range(15):r['Trans'+chr(65+u)+str(t)]=10-int(u==qn)+int(u==q)+a
            assert len(r)==46;rows[name]=r
    out=[[rows[i][j] for j in NAMES] for i in NAMES]
    assert out==source
    return dict(status='PASS',checked_entries=46*46,matrix_sha256=read_sources()[3],definition='Complete compact trigger rules in Appendix A')
if __name__=='__main__':
    result=build();(ROOT/'receipts/matrix-definition.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
