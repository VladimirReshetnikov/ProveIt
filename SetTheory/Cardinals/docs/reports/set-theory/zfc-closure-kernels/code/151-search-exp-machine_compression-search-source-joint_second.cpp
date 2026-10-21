#include <bits/stdc++.h>
using namespace std;struct A{int w,d,z;};struct C{int q,m;vector<tuple<int,int,int>>path;};struct Test{C*c;vector<uint64_t>goals;bool oh;int q,h,bit;};const int R=7,F=97;A O[303][2],N[303][2];vector<int>Q;vector<C>cs[303];int kp,dr,sh;map<int,vector<Test>>cache;
uint64_t key(int q,int h,int m){return(uint64_t(q)<<21)|(uint64_t(h+16)<<15)|m;}
vector<Test>&get(int q){if(!cache.count(q)){vector<Test>v;for(auto&c:cs[q]){int h=q==dr?sh:0;Test t{&c,{},false,q==dr?kp:q,h,(c.m>>(h+R))&1};for(auto[x,y,m]:c.path){t.oh|=x==254;t.goals.push_back(key(x==dr?kp:x,y+(x==dr?sh:0),m));}sort(t.goals.begin(),t.goals.end());v.push_back(move(t));}cache[q]=move(v);}return cache[q];}
int run(Test&t,int defer=-1,vector<pair<int,int>>*trace=nullptr){int q=t.q,h=t.h,m=t.c->m;uint64_t seen[F];int sn=0;for(int tick=0;tick<F;tick++){if(q==254||h< -R||h>R)return 0;auto v=key(q,h,m);for(int j=0;j<sn;j++)if(seen[j]==v)return 0;seen[sn++]=v;int b=(m>>(h+R))&1;if(trace&&find(trace->begin(),trace->end(),make_pair(q,b))==trace->end())trace->push_back({q,b});if(q==kp&&b==defer)return 2;auto a=N[q][b];m=(m&~(1<<(h+R)))|(a.w<<(h+R));h+=a.d;q=a.z;if(q==254)return t.oh;if(binary_search(t.goals.begin(),t.goals.end(),key(q,h,m)))return 1;}return 0;}

int main(int argc,char**argv){ifstream f(argv[1]);int n;f>>n;for(int i=0;i<n;i++){int q;f>>q;Q.push_back(q);for(int b=0;b<2;b++)f>>O[q][b].w>>O[q][b].d>>O[q][b].z;}int nc;f>>nc;for(int i=0;i<nc;i++){int q,m;f>>q>>m;C c{q,m,{}};int st=q,h=0,t=m;for(int j=0;j<F;j++){if(st==254||h< -R||h>R)break;auto a=O[st][(t>>(h+R))&1];t=(t&~(1<<(h+R)))|(a.w<<(h+R));h+=a.d;st=a.z;c.path.emplace_back(st,h,t);}cs[q].push_back(move(c));}for(int q:Q)if(cs[q].size()>1)swap(cs[q][1],cs[q].back());
long long tried=0,firstpass=0,partial=0,hits=0;int specs=0;auto begin=chrono::steady_clock::now();sh=0;ifstream specsfile(argv[2]);string line;
while(getline(specsfile,line)){istringstream ss(line);string tag;ss>>tag;if(tag!="PARTIAL")continue;A k0,k1,h1;int hq,hb;ss>>kp>>dr>>k0.w>>k0.d>>k0.z>>k1.w>>k1.d>>k1.z>>hq>>hb>>h1.w>>h1.d>>h1.z;specs++;cache.clear();for(int q:Q)for(int b:{0,1}){N[q][b]=O[q][b];if(N[q][b].z==dr)N[q][b].z=kp;}N[kp][0]=k0;N[kp][1]=k1;N[hq][hb]=h1;
vector<Test*>tests;for(int q:{dr,kp,hq})for(auto&t:get(q))tests.push_back(&t);Test*bad0=nullptr;for(auto*t:tests)if(!run(*t)){bad0=t;break;}if(!bad0){cerr<<"ALREADY_PASS "<<specs<<endl;continue;}vector<pair<int,int>>trace;run(*bad0,-1,&trace);auto targets=Q;targets.erase(find(targets.begin(),targets.end(),dr));targets.push_back(254);
for(auto[p,b]:trace){if(p==kp||p==dr||(p==hq&&b==hb))continue;A saved=N[p][b];vector<Test*>bad={bad0};
for(int w:{0,1})for(int d:{-1,1})for(int z:targets){tried++;N[p][b]={w,d,z};if(!run(*bad0))continue;firstpass++;bool pass=true;for(Test*t:bad)if(t!=bad0&&!run(*t)){pass=false;break;}if(!pass)continue;for(Test*t:tests)if(!run(*t)){pass=false;if(bad.size()<128&&find(bad.begin(),bad.end(),t)==bad.end())bad.push_back(t);break;}if(!pass)continue;partial++;
for(auto&t:get(p)){if(((t.c->m>>R)&1)!=b)continue;if(!run(t)){pass=false;if(bad.size()<128&&find(bad.begin(),bad.end(),&t)==bad.end())bad.push_back(&t);break;}}if(!pass)continue;
hits++;cout<<"HIT spec "<<specs<<" "<<kp<<" "<<dr<<" helper1 "<<hq<<" "<<hb<<" helper2 "<<p<<" "<<b<<" "<<w<<" "<<d<<" "<<z<<endl;ofstream out(string(argv[3])+"/joint-second-"+to_string(specs)+"-"+to_string(hits)+".tm");out<<"#! start 0\n";for(int q:Q)if(q!=dr)for(int bit:{0,1}){auto a=N[q][bit];out<<q<<" "<<bit<<" "<<a.w<<" "<<(a.d==1?'R':'L')<<" "<<a.z<<"\n";}
}
N[p][b]=saved;
}
cerr<<"SPEC "<<specs<<" "<<kp<<" "<<dr<<" tried "<<tried<<" first "<<firstpass<<" partial "<<partial<<" hits "<<hits<<" time "<<chrono::duration<double>(chrono::steady_clock::now()-begin).count()<<endl;
}
cerr<<"DONE "<<specs<<" "<<tried<<" "<<firstpass<<" "<<partial<<" "<<hits<<endl;
}
