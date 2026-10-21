#include <bits/stdc++.h>
using namespace std;struct A{int w,d,z;};A T[303][2];vector<int>Q;bitset<32768>I[303];int phy[9]={6,2,0,4,3,7,8,5,1}; const int N=4096,C=1024;
bool clean(int q,int h,array<int,N>&a){if(q!=84||!a[h-1])return false;for(int i=0;i<h-1;i++)if(a[i])return false;int f=h+52;while(f<N&&!a[f])f++;if(f>=N||f<h+64)return false;int last=N-1;while(last>=0&&!a[last])last--;int p=f+1,n=0;while(p<last){if(a[p]||!a[p+1])return false;p++;while(p<N&&a[p])p++;n++;}return p==last+1&&n>=10;}
int main(int argc,char**argv){ifstream f(argv[1]);int n;f>>n;for(int i=0;i<n;i++){int q;f>>q;Q.push_back(q);for(int b=0;b<2;b++)f>>T[q][b].w>>T[q][b].d>>T[q][b].z;}int cnt;f>>cnt;vector<pair<string,int>>sites;vector<vector<int>> masks;for(int i=0;i<cnt;i++){string p;int arg,n;f>>p>>arg>>n;sites.emplace_back(p,arg);vector<int>v(n);for(int&x:v)f>>x;masks.push_back(v);}long long steps=0,cases=0;auto begin=chrono::steady_clock::now();
 for(int idx=0;idx<=cnt;idx++){for(int profile=0;profile<(idx==cnt?1:2*masks[idx].size());profile++){
 array<int,N>a{};int q=84,h=C;
 if(idx==cnt)q=0;
 else {auto[pc,arg]=sites[idx];int regs[9];for(int j=0;j<9;j++)regs[j]=((masks[idx][profile/2]>>j)&1)*(1+profile%2);int gap=80;int p=C+64+gap;a[C-1]=a[p]=1;for(int j=0;j<(int)pc.size();j++)a[C+j]=pc[j]-'0';int v[9];for(int j=0;j<9;j++)v[phy[j]]=regs[j];p++;for(int j=0;j<9;j++){p++;for(int k=0;k<=v[j];k++)a[p++]=1;}int spares=130;for(int j=0;j<spares;j++){int val=1;p++;for(int k=0;k<=val;k++)a[p++]=1;}}
 int m=0;for(int j=-7;j<=7;j++)m|=a[h+j]<<(j+7);int limit=idx==cnt?312909:20000;bool end=false;
 for(int tick=0;tick<=limit;tick++){I[q].set(m);if(tick&&(idx==cnt?tick==limit:clean(q,h,a)||q==254)){end=true;break;}if(q==254||h<8||h>N-9){cerr<<"BADBOUND"<<endl;return 2;}auto x=T[q][a[h]];a[h]=x.w;m=(m&~(1<<7))|(x.w<<7);h+=x.d;q=x.z;steps++;if(x.d==1)m=(m>>1)|(a[h+7]<<14);else m=((m<<1)&32767)|a[h-7];}
 if(!end){cerr<<"NOEND "<<idx<<" "<<profile<<endl;return 3;}cases++;
 }if(idx%500==0)cerr<<"SITE "<<idx<<" cases "<<cases<<" steps "<<steps<<endl;}
 cout<<Q.size()<<'\n';for(int q:Q)cout<<q<<' '<<T[q][0].w<<' '<<T[q][0].d<<' '<<T[q][0].z<<' '<<T[q][1].w<<' '<<T[q][1].d<<' '<<T[q][1].z<<'\n';int total=0;for(int q:Q)total+=I[q].count();cout<<total<<'\n';for(int q:Q)for(int m=0;m<32768;m++)if(I[q][m])cout<<q<<' '<<m<<'\n';cerr<<"DONE cases "<<cases<<" steps "<<steps<<" contexts "<<total<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-begin).count()<<endl;
}
