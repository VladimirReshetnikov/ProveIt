#include <bits/stdc++.h>
using namespace std;struct A{int w,d,z;};A T[1200][2];bool present[1200];int off=128;
bitset<512>parse(string s){bitset<512>t;if(s=="x")return t;istringstream ss(s);string z;while(getline(ss,z,',')){int h=stoi(z)+off;t[h]=1;}return t;}
bool clean(int h,const bitset<512>&t){if(h<1||h+64>=512||!t[h-1])return false;for(int i=0;i<h-1;i++)if(t[i])return false;int header=h+52;while(header<512&&!t[header])header++;if(header>=512||header<h+64)return false;int last=511;while(last>=0&&!t[last])last--;int p=header+1,n=0;while(p<last){if(t[p]||!t[p+1])return false;p++;while(p<512&&t[p])p++;n++;}return p==last+1&&n>=10;}
int main(int argc,char**argv){ifstream in(argv[1]);string line;while(getline(in,line)){if(line.empty()||line[0]=='#')continue;istringstream s(line);int q,b,w,z;char d;s>>q>>b>>w>>d>>z;T[q][b]={w,d=='R'?1:-1,z};present[q]=true;}
ifstream ci(argv[2]);set<string>seen;ofstream out(argv[3]);int cases=0,hits=0;
while(getline(ci,line)){istringstream s(line);int idx,pos,halt,dh;string x,y;s>>idx>>pos>>halt>>dh>>x>>y;auto tape=parse(x);int q=84,h=off;
for(int tick=0;tick<100000;tick++){
if(tick&&((q==84&&clean(h,tape))||q==254))break;
if(q==13||q==82){ostringstream ks;ks<<q<<" "<<tape[h]<<" ";for(int i=0;i<512;i++)if(tape[i])ks<<(i-h)<<",";auto key=ks.str();if(seen.insert(key).second){out<<key<<"\n";hits++;}}
if(h<0||h>=512||!present[q]){cerr<<"BAD "<<cases<<"\n";return 2;}auto a=T[q][tape[h]];tape[h]=a.w;h+=a.d;q=a.z;
}cases++;
}cerr<<"cases "<<cases<<" unique contexts "<<hits<<"\n";return 0;}

