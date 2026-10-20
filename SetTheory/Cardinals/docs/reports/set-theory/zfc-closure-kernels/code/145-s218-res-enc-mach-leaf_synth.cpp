#include <bits/stdc++.h>
using namespace std;
struct Row{int w,d,q;};struct Tape{array<uint64_t,64> b{};bool get(int h)const{h+=512;return (b[h>>6]>>(h&63))&1;}void put(int h,int w){h+=512;uint64_t m=1ull<<(h&63);if(w)b[h>>6]|=m;else b[h>>6]&=~m;}bool operator==(Tape const&o)const{return b==o.b;}};
struct Case{string pc,op;int arg;Tape in,out;int outhead;bool halt;};
Row T[512][2];Row M[2];vector<int>Q;vector<Case>cases;int PHY[]={6,2,0,4,3,7,8,5,1};
Tape frame(string pc,vector<int> r, vector<int>sp,int gap){Tape t;t.put(-1,1);t.put(64+gap,1);for(int i=0;i<(int)pc.size();i++)t.put(i,pc[i]-'0');vector<int>v(9);for(int i=0;i<9;i++)v[PHY[i]]=r[i];for(int x:sp)v.push_back(x);int p=65+gap;for(int x:v){p++;for(int j=0;j<x+1;j++)t.put(p++,1);}return t;}
pair<string,int> inc(string pc){for(int i=(int)pc.size()-1;i>=0;i--){if(pc[i]=='0'){pc[i]='1';return {pc,0};}pc[i]='0';}return {pc,1};}
string strip(string pc,char bit,int n){for(int i=(int)pc.size()-1;i>=0;i--)if(pc[i]==bit&&--n==0)return pc.substr(0,i);return "";}
Case makecase(string pc,string op,int arg,int val=0,int bg=0,int spare=1,int gap=0){vector<int>r(9,bg),sp{spare,1};r[arg<0?0:arg]=val;Case c;c.pc=pc;c.op=op;c.arg=arg;c.in=frame(pc,r,sp,gap);int shift=0;c.halt=op=="CH";
if(op=="CI"){r[arg]++;sp.push_back(1);tie(pc,shift)=inc(pc);}else if(op=="CD"&&r[arg]){r[arg]--;gap++;tie(pc,shift)=inc(pc);}else if(op=="CD"||op=="CB")tie(pc,shift)=inc(strip(pc,'0',op=="CD"?1:arg));else if(op=="CC")pc=strip(pc,'1',arg);
c.out=frame(pc,r,sp,gap+shift);if(shift){Tape u;for(int i=-1;i<1000;i++)if(c.out.get(i))u.put(i-shift,1);c.out=u;}c.outhead=-shift;return c;}
bool dispatch(Tape const&t,int h){if(!t.get(h-1))return false;for(int i=-256;i<h-1;i++)if(t.get(i))return false;int p=h+52;while(p<1500&&!t.get(p))p++;if(p<h+64||p>=1500)return false;p++;int blocks=0;while(p<1500){if(t.get(p))return false;if(!t.get(p+1)){for(int j=p+2;j<1500;j++)if(t.get(j))return false;break;}p++;while(p<1500&&t.get(p))p++;blocks++;}return blocks>=10;}

bool leafcheck(Row action,Case const&c){Tape t=c.in;int h=c.pc.size()-1;t.put(h,action.w);h+=action.d;int q=action.q;
for(int tick=0;tick<30000;tick++){
 if(q==254)return c.halt;if(q==84&&dispatch(t,h))return !c.halt&&h==c.outhead&&t==c.out;
 if(h< -255||h>=1500||q<0||q>=512)return false;Row r=T[q][t.get(h)];t.put(h,r.w);h+=r.d;q=r.q;
}return false;}
int main(int argc,char**argv){ifstream tf(argv[1]);string line;while(getline(tf,line)){if(line.empty()||line[0]=='#')continue;istringstream s(line);int q,v,w,z;char d;s>>q>>v>>w>>d>>z;T[q][v]={w,d=='R'?1:-1,z};if(v==0)Q.push_back(q);}Q.push_back(254);
ifstream in(argv[2]);ofstream out(argv[3]);int id,bit,force,w,d,z,n;
while(in>>id>>bit>>force>>w>>d>>z>>n){vector<Case>c;string pc,op;int arg;for(int k=0;k<n;k++){in>>pc>>op>>arg;for(auto a:vector<array<int,3>>{{0,1,0},{1,1,0},{3,2,3},{2,0,1}})c.push_back(makecase(pc,op,arg,a[0],a[0],a[1],a[2]));}
 auto good=[&](Row a){for(auto const&v:c)if(!leafcheck(a,v))return false;return true;};Row answer{w,d,z};bool ok=good(answer);
 if(!ok&&!force){for(int target:Q){Row a{bit,1,target};if(good(a)){answer=a;ok=true;break;}}}
 if(!ok&&!force){for(int ww=0;ww<2&&!ok;ww++)for(int dd:{-1,1}){for(int target:Q){Row a{ww,dd,target};if(good(a)){answer=a;ok=true;break;}}if(ok)break;}}
 out<<id<<" "<<ok<<" "<<answer.w<<" "<<answer.d<<" "<<answer.q<<"\n";
}
}
