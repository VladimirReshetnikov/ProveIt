#include <bits/stdc++.h>
using namespace std;struct A{int w,d,z;};struct C{int q,m;vector<tuple<int,int,int>>path;};A O[303][2];vector<int>Q;vector<C>cs[303];vector<int>in[303];const int R=7,F=97;
uint64_t key(int q,int h,int m){return (uint64_t(q)<<21)|(uint64_t(h+16)<<15)|m;}
int main(int argc,char**argv){int mode=argc>2?atoi(argv[2]):0;ifstream f(argv[1]);int n;f>>n;for(int i=0;i<n;i++){int q;f>>q;Q.push_back(q);for(int b=0;b<2;b++)f>>O[q][b].w>>O[q][b].d>>O[q][b].z;}for(int q:Q)for(int b=0;b<2;b++)if(O[q][b].z!=254)in[O[q][b].z].push_back(O[q][b].d);
 int nc;f>>nc;for(int i=0;i<nc;i++){int q,m;f>>q>>m;C c{q,m,{}};int s=q,h=0,t=m;for(int j=0;j<F;j++){if(s==254||h< -R||h>R)break;A a=O[s][(t>>(h+R))&1];t=(t&~(1<<(h+R)))|(a.w<<(h+R));h+=a.d;s=a.z;c.path.emplace_back(s,h,t);}cs[q].push_back(c);}
 long long total=0,hits=0,pairs=0;auto begin=chrono::steady_clock::now();
 for(int dr:Q){if(dr==0)continue;int shift=0;if(mode){if(in[dr].empty()||*min_element(in[dr].begin(),in[dr].end())!=*max_element(in[dr].begin(),in[dr].end()))continue;shift=-2*in[dr][0];}
 for(int kp:Q){if(kp==dr)continue;pairs++;
 struct Test{int m,h;bool oh;vector<uint64_t>goals;};vector<Test>tests[2];
 for(int oq:{dr,kp})for(auto&c:cs[oq]){Test t{c.m,oq==dr?shift:0,false,{}};for(auto[q,h,m]:c.path){t.oh|=q==254;t.goals.push_back(key(q==dr?kp:q,h+(q==dr?shift:0),m));}sort(t.goals.begin(),t.goals.end());int b=(t.m>>(t.h+R))&1;tests[b].push_back(move(t));}
 vector<A>ok[2];
 for(int b=0;b<2;b++){
 if(b&&ok[0].empty())break;
 if(tests[b].empty()){A a=O[kp][b];if(a.z==dr){a.z=kp;a.d+=shift;}ok[b].push_back(a);continue;}
 for(int w=0;w<2;w++)for(int d:{-1,1})for(int z:Q){if(z==dr)continue;A alt{w,d,z};total++;bool pass=true;
 for(auto&t:tests[b]){int q=kp,h=t.h,m=t.m;bool joined=false;uint64_t seen[F];int sn=0;
 for(int tick=0;tick<F;tick++){if(q==254||h< -R||h>R)break;auto k=key(q,h,m);bool repeat=false;for(int j=0;j<sn;j++)if(seen[j]==k){repeat=true;break;}if(repeat)break;seen[sn++]=k;int bit=(m>>(h+R))&1;A a;if(q==kp){if(bit!=b)break;a=alt;}else{a=O[q][bit];if(a.z==dr){a.z=kp;a.d+=shift;}}m=(m&~(1<<(h+R)))|(a.w<<(h+R));h+=a.d;q=a.z;if(q==254){joined=t.oh;break;}if(binary_search(t.goals.begin(),t.goals.end(),key(q,h,m))){joined=true;break;}}
 if(!joined){pass=false;break;}}
 if(pass)ok[b].push_back(alt);
 }
 }
 if(!ok[0].empty()&&!ok[1].empty())for(auto a:ok[0])for(auto b:ok[1]){hits++;cout<<"HIT "<<kp<<" "<<dr<<" "<<shift<<" "<<a.w<<" "<<a.d<<" "<<a.z<<" "<<b.w<<" "<<b.d<<" "<<b.z<<endl;}
 }
 cerr<<"drop "<<dr<<" pairs "<<pairs<<" specs "<<total<<" hits "<<hits<<" time "<<chrono::duration<double>(chrono::steady_clock::now()-begin).count()<<endl;
 }
 cerr<<"DONE "<<pairs<<" "<<total<<" "<<hits<<endl;
}
