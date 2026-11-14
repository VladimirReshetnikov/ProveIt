#include <array>
#include <chrono>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
#include <algorithm>

struct Row { int w,d,z; };
int n;
Row t[260][2];
int offsets[260];
bool marker=false;
std::vector<std::array<unsigned char,160>> samples[260][2];

bool check(int old, int bit, const std::array<unsigned char,160>& input,
           int drop, int keep, int off, int cb, Row replacement, int limit) {
    int q=keep, h=80+(old==drop?off:0);
    auto a=input;
    if(marker && old==drop) a[80+off/2]^=1;
    auto oldrow=t[old][bit];
    int wantq=oldrow.z==drop?keep:oldrow.z;
    int wanth=80+oldrow.d+(oldrow.z==drop?off:0);
    auto expected=input;
    expected[80]=oldrow.w;
    if(marker && oldrow.z==drop) expected[80+oldrow.d+off/2]^=1;
    int mismatch=0;
    for(int k=0;k<160;k++)mismatch+=a[k]!=expected[k];
    for(int step=0;step<limit;step++) {
        if(q==n || h<0 || h>=160) return false;
        Row r;
        if(q==keep && a[h]==cb) r=replacement;
        else {
            r=t[q][a[h]];
            if(r.z==drop) { r.z=keep; r.d+=off; if(marker)r.w^=1; }
        }
        int wantbit=expected[h];
        mismatch -= a[h]!=wantbit;
        a[h]=r.w;
        mismatch += a[h]!=wantbit;
        h+=r.d; q=r.z;
        if(q==wantq && h==wanth && mismatch==0) return true;
    }
    return false;
}

int main(int argc,char**argv) {
    std::ifstream in(argv[1]); std::ofstream out(argv[2]);
    int limit=argc>3?std::stoi(argv[3]):31;
    int first=argc>4?std::stoi(argv[4]):1;
    int last=argc>5?std::stoi(argv[5]):1000;
    marker=argc>6 && std::stoi(argv[6]);
    in>>n;
    for(int i=0;i<n;i++) {
        int q;in>>q;
        for(int b=0;b<2;b++) in>>t[q][b].w>>t[q][b].d>>t[q][b].z;
        in>>offsets[q];
    }
    for(int i=0;i<2*n;i++) {
        int q,b,count;in>>q>>b>>count;
        for(int j=0;j<count;j++) {
            std::string s;in>>s;std::array<unsigned char,160>a;
            for(int k=0;k<160;k++)a[k]=s[k]-'0';
            samples[q][b].push_back(a);
        }
    }
    long long tested=0,accepted=0;
    auto start=std::chrono::steady_clock::now();
    for(int drop=first;drop<n && drop<last;drop++) {
        int off=offsets[drop];if(!off)continue;
        for(int keep=0;keep<n;keep++) {
            if(keep==drop)continue;
            for(int cb=0;cb<2;cb++)for(int z=0;z<=n;z++) {
                if(z==drop)continue;
                for(int dir: {-1,1})for(int w=0;w<2;w++) {
                    tested++; Row replacement{w,dir,z};
                    bool ok=true;
                    // Check the retained state's modified row first.
                    if(!check(keep,cb,samples[keep][cb][0],drop,keep,off,cb,replacement,limit))continue;
                    for(int old: {drop,keep}) {
                        for(int b=0;b<2 && ok;b++) {
                            for(const auto&a:samples[old][b]) {
                                if(!check(old,b,a,drop,keep,off,cb,replacement,limit)) {ok=false;break;}
                            }
                        }
                        if(!ok)break;
                    }
                    if(ok) {
                        accepted++;
                        out<<drop<<' '<<keep<<' '<<off<<' '<<cb<<' '<<w<<' '<<dir<<' '<<z<<'\n';
                        out.flush();
                        std::cout<<"SCREEN PASS "<<drop<<' '<<keep<<' '<<off<<' '<<cb<<' '<<w<<' '<<dir<<' '<<z<<std::endl;
                    }
                }
            }
        }
        if(drop%10==0)std::cout<<"PROGRESS "<<drop<<" candidates "<<tested<<std::endl;
    }
    std::cout<<"DONE tested "<<tested<<" screen_pass "<<accepted<<" seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<std::endl;
}
