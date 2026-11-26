#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <vector>

using namespace std;

bool apart(int D, int a, int b) {
    if (a==0) return true;
    long long diff=b-a;
    return D>=16LL*a*a && 9LL*D*diff*diff>=16LL*a*a*b*b;
}

int main(int argc, char** argv) {
    const int limit=argc>1?atoi(argv[1]):10000000;
    if (limit < 3 || limit > 10000000) {
        cerr<<"limit must be between 3 and 10000000 inclusive\n";
        return 2;
    }
    const int cutoff=80;
    vector<unsigned char> count(limit+1);
    vector<short> last(limit+1);
    for (int a=1; a<=cutoff; ++a) {
        for(int b=0;b<=a;++b){
            const int g=gcd(a,b);
            for(int c=a,D=4*a*c-b*b; D<=limit; ++c,D+=4*a) {
                if(count[D]>=4 || last[D]==a || !apart(D,last[D],a)) continue;
                if(gcd(c,g)!=1) continue;
                ++count[D]; last[D]=a;
            }
        }
    }
    int small_degree=0, unresolved=0, passes=0, tested=0;
    for(int D=3;D<=limit;++D) {
        if (D%4>0 && D%4!=3) continue;
        ++tested;
        if(count[D]>=4){++passes;continue;}
        int h=0, n=0, la=0;
        vector<int> av;
        for (int a=1;3*a*a<=D;++a){
            bool ok=false;
            for(int b=D%2;b<=a;b+=2){
                int sum=D+b*b;
                if(sum%(4*a)!=0)continue;
                int c=sum/(4*a);
                if(c<a || gcd(gcd(a,b),c)!=1)continue;
                h += b==0 || b==a || a==c ? 1 : 2;
                ok=true;
            }
            if(ok){
                av.push_back(a);
                if(apart(D,la,a)){++n; la=a;}
            }
            if(n>=4)break;
        }
        if(n>=4){++passes;continue;}
        if(h<4){++small_degree;continue;}
        cout<<D<<' '<<h;
        for(int a:av) cout<<' '<<a;
        cout<<'\n';
        ++unresolved;
    }
    cerr<<"tested "<<tested<<" passes "<<passes<<" h<4 "<<small_degree<<" pending "<<unresolved<<'\n';
}
