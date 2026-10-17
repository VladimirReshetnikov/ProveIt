#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
#include <unordered_map>
#include <sstream>
struct Row{int w,d,q;};
int main(int argc,char**argv){
 const std::string file=argc>1?argv[1]:"candidate252_tail_oldlabels.tm";
 const long limit=argc>2?std::stol(argv[2]):100000000;
 std::array<std::array<Row,2>,255>T{};std::array<bool,255>present{};
 std::ifstream in(file);std::string line;
 while(std::getline(in,line)){if(line.empty()||line[0]=='#')continue;int q,b,w,p;char d;sscanf(line.c_str(),"%d %d %d %c %d",&q,&b,&w,&d,&p);T[q][b]={w,d=='R'?1:-1,p};present[q]=true;}
 struct Node{int c[2]={-1,-1};bool leaf=false;};std::vector<Node>trie(1);
 std::ifstream pin("path_strings.txt");std::string p;
 while(pin>>p){int i=0;for(char b:p){int j=trie[i].c[b-'0'];if(j<0){j=trie.size();trie[i].c[b-'0']=j;trie.emplace_back();}i=j;}trie[i].leaf=true;}
 std::unordered_map<std::string,long>ref;std::ifstream refs("rm_prefix100k.txt");long rn;std::string rp,rr;while(refs>>rn>>rp>>rr)ref.emplace(rp+":"+rr,rn);
 const int C=1000000;std::vector<unsigned char>tape(2*C,0);
 for(int start:{0,7,20,42,83,95,97,112}){
  std::fill(tape.begin(),tape.end(),0);int h=C,q=start,lo=C,hi=C-1;long n=0;int maxgap=-1;long canonical=0;
  for(;n<limit;n++){
   if(q==96&&tape[h-1]&&lo>=h-1){int i=0,j=h;while(!trie[i].leaf){i=trie[i].c[tape[j++]];if(i<0){std::cerr<<"trie";return 2;}}
    int header=j;while(header<=hi&&!tape[header])header++;
    if(header<=hi){int k=header+1;std::vector<int>regs;bool good=true;while(k<=hi){if(tape[k]){good=false;break;}k++;int a=k;while(tape[k])k++;if(k==a){good=false;break;}regs.push_back(k-a-1);}if(good&&regs.size()>=9){int gap=header-h;if(gap>maxgap){maxgap=gap;std::cout<<"GAP "<<start<<" "<<n<<" "<<h-C<<" "<<maxgap<<" regs";for(int z=0;z<9;z++)std::cout<<" "<<regs[z];std::cout<<" ext "<<regs.size()-9<<std::endl;}if(gap>=34){canonical++;std::string pc;for(int z=h;z<j;z++)pc+=char('0'+tape[z]);while(!pc.empty()&&pc.back()=='0')pc.pop_back();if(pc.empty())pc="-";std::string key=pc+":";for(int z=0;z<9;z++){if(z)key+=",";key+=std::to_string(regs[z]);}auto match=ref.find(key);if(match!=ref.end())std::cout<<"MATCH "<<start<<" TM "<<n<<" RM "<<match->second<<" gap "<<gap<<" head "<<h-C<<" regs "<<key<<std::endl;if(canonical<=20){std::cout<<"FRAME "<<start<<" "<<n<<" gap "<<gap<<" head "<<h-C<<" pc ";for(int z=h;z<j;z++)std::cout<<int(tape[z]);std::cout<<" regs ";for(int z=0;z<9;z++)std::cout<<regs[z]<<",";std::cout<<std::endl;}}}}}
   if(!present[q])break;Row r=T[q][tape[h]];if(r.w){tape[h]=1;if(hi<lo){hi=lo=h;}else{if(h<lo)lo=h;if(h>hi)hi=h;}}else if(tape[h]){tape[h]=0;if(h==lo){while(lo<=hi&&!tape[lo])lo++;}if(h==hi){while(hi>=lo&&!tape[hi])hi--;}}h+=r.d;q=r.q;if(h<C-100000||h>C+100000)break;
  }
  std::cout<<"END "<<start<<" "<<n<<" "<<q<<" "<<h-C<<" maxgap "<<maxgap<<" canonical "<<canonical<<std::endl;
 }
}
