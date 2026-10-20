// Relaxed-spare discovery only, arbitrary clean spare tail and gap>=64.
// Discovery only: bounded complete-tape instruction examples, not a proof.
#include <bits/stdc++.h>
using namespace std;
constexpr int W=768,O=256;
struct Row{int w,d,z;};Row T[1024][2],N[1024][2];vector<int>qs;
struct Sample{int id,mode,q,h,gq,gh,fuel; bitset<W> tape,goal;};
vector<Sample> pre[1024];vector<Sample> frames;bool ex[1024];set<int> nondec;
int keep,drop; long long checks=0,ticks=0;
int mp(int q){return q==drop?keep:q;}
bool relaxed_match(const bitset<W>& tape,int h,const Sample& c){
 if(h<1||h+64>=W||!tape[h-1])return false;
 for(int j=0;j<h-1;++j)if(tape[j])return false;
 for(int j=0;j<52;++j)if(tape[h+j]!=c.goal[c.gh+j])return false;
 auto values=[](const bitset<W>& t,int h){vector<int> out;int p=h+52;while(p<W&&!t[p])++p;if(p<h+64||p==W)return out;++p;while(p<W){int end=W-1;while(end>=p&&!t[end])--end;if(end<p)break;if(t[p]||p+1>=W||!t[p+1]){out.clear();return out;}int st=++p;while(p<W&&t[p])++p;out.push_back(p-st-1);}return out;};
 auto a=values(tape,h),b=values(c.goal,c.gh);
 if(a.size()<10||b.size()<10)return false;
 for(int i=0;i<9;i++)if(a[i]!=b[i])return false;
 return true;
}
bool run(const Sample& c){++checks;auto tape=c.tape;int q=mp(c.q),h=c.h;for(int n=0;n<4*c.fuel+2000;++n){if(n&&q==mp(c.gq)&&(q==254||relaxed_match(tape,h,c)))return true;if(q==254||h<0||h>=W)return false;auto a=N[q][tape[h]];tape[h]=a.w;h+=a.d;q=mp(a.z);++ticks;}return false;}
int main(int ac,char**av){ifstream tf(av[1]);string line;while(getline(tf,line)){if(line.empty()||line[0]=='#')continue;istringstream ss(line);int q,b,w,z;char d;ss>>q>>b>>w>>d>>z;T[q][b]=N[q][b]={w,d=='R'?1:-1,z};ex[q]=1;}for(int q=0;q<1024;q++)if(ex[q])qs.push_back(q);
 for(int q:{0,1,2,3,4,5,6,9,10,14,15,16,17,21,22,23,24,25,32,33,34,35,36,39,40,41,45,48,49,50,51,54,55,56,60,61,64,66,74,75,82,94,97,113,137,144,156,161,198})nondec.insert(q);
 ifstream ff(av[2]);set<tuple<int,int,int>>seen;int id,mode,gq,gh,n,x;
 while(ff>>id>>mode>>gq>>gh>>n){Sample c;c.id=id;c.mode=mode;c.q=84;c.h=O;c.gq=gq;c.gh=O+gh;while(n--){ff>>x;c.tape[O+x]=1;}ff>>n;while(n--){ff>>x;c.goal[O+x]=1;}
 int q=84,h=O,k=0;auto tape=c.tape;vector<Sample>newones;
 for(;k<10000;k++){if(k&&q==gq&&(q==254||(h==c.gh&&tape==c.goal)))break;if(q==254||h<6||h>=W-6)throw runtime_error("baseline bad");int pattern=0;for(int j=-5;j<=5;j++)pattern|=int(tape[h+j])<<(j+5);
 if(seen.insert({q,pattern,mode}).second){Sample t=c;t.q=q;t.h=h;t.tape=tape;t.fuel=k;newones.push_back(t);}
 auto a=T[q][tape[h]];tape[h]=a.w;h+=a.d;q=a.z;}
 if(k==10000)throw runtime_error("baseline timeout");c.fuel=k;frames.push_back(c);for(auto t:newones){t.fuel=k-t.fuel;pre[t.q].push_back(t);}
 }
 cerr<<"SAMPLES "<<seen.size()<<" frames "<<frames.size()<<endl;
 for(int q:qs){sort(pre[q].begin(),pre[q].end(),[](auto&a,auto&b){return a.fuel<b.fuel;});cerr<<"STATE "<<q<<" samples "<<pre[q].size()<<endl;}
 long long candidates=0,pairs=0;auto begin=chrono::steady_clock::now();
 for(int p:qs)for(int q:qs)if(p<q&&(nondec.count(p)||nondec.count(q))){keep=p;drop=q;++pairs;for(int a=0;a<2;a++)for(int b=0;b<2;b++){
 N[p][0]=T[a?q:p][0];N[p][1]=T[b?q:p][1]; bool good=true;for(int s:{p,q}){for(auto&c:pre[s]){if(!run(c)){good=false;break;}}if(!good)break;}
 if(good){cout<<"MERGE "<<p<<" "<<q<<" branches "<<a<<" "<<b<<endl;candidates++;}}
 N[p][0]=T[p][0];N[p][1]=T[p][1];if(pairs%1000==0)cerr<<"PAIRS "<<pairs<<" hits "<<candidates<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-begin).count()<<endl;}
 cerr<<"DONE pairs "<<pairs<<" candidates "<<candidates<<" checks "<<checks<<" ticks "<<ticks<<endl;
}
