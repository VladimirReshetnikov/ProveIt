"""Generate/verify a 2^m-dimensional block with a non-involutory 3x3 core."""
import pathlib,sys,json,time,statistics
ROOT=pathlib.Path(__file__).resolve().parents[1];sys.path[:0]=[str(ROOT/'src'),str(ROOT)]
from unknot_frobenius.verify import verify_spec

def specification(m=40):
    if m<2: raise ValueError('at least two modes required')
    def vec(j,side,weight):
        factors=[]
        for k in range(m):
            if k<2:
                factors.append([0,1] if (j>>k)&1 else [1,0])
            else:
                factors.append([1,1] if k%2==side else [1,0])
        return [dict(weight=weight,factors=factors)]
    x,y=1<<1,1<<2
    return dict(schema='unknot-frobenius-interface-v1',variables=2,modes=m,
                description='Complementary product supports with a three-step radical core; same-matching algebraic block only.',
                u_columns=[vec(0,0,0),vec(0,0,x),vec(1,0,y)],
                v_rows=[vec(j,1,1) for j in range(3)],
                c_columns=[vec(2,0,1)],d_rows=[vec(0,1,1)],e=[[0]],expected_schur=[[1<<3]])

if __name__=='__main__':
    spec=specification()
    (ROOT/'examples'/'succinct_interface_2pow40.json').write_text(json.dumps(spec,indent=2)+'\n')
    records=[]
    for m in [10,20,40,80,160]:
        times=[]
        for _ in range(9):
            s=specification(m);start=time.perf_counter_ns();result=verify_spec(s);times.append((time.perf_counter_ns()-start)/1e9)
        records.append(dict(modes=m,represented_dimension=str(1<<m),seconds=times,median_seconds=statistics.median(times),result=result))
    (ROOT/'results'/'succinct.json').write_text(json.dumps(records,indent=2)+'\n')
    print(json.dumps(verify_spec(spec),indent=2))
