#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
#include <chrono>
int main(int argc,char**argv){
 if(argc!=4){std::cerr<<"input output-prefix mode(012 or parity)\n";return 2;}
 auto begin=std::chrono::steady_clock::now();bool parity=std::string(argv[3])=="parity";std::ifstream in(argv[1]);int n;in>>n;std::vector<std::array<int,4>> g(n);for(auto &r:g)for(auto &x:r)in>>x;
 constexpr int C=19683;std::array<int,9> p{1,3,9,27,81,243,729,2187,6561};std::vector<uint8_t> seen(size_t(n)*C,0);std::vector<uint32_t> queue;queue.reserve(size_t(n)*C/4);int seed=(parity?1:2)*(p[0]+p[4]);seen[seed]=1;queue.push_back(seed);uint64_t edges=0;
 auto add=[&](int site,int mask){uint32_t id=uint32_t(site*C+mask);++edges;if(!seen[id]){seen[id]=1;queue.push_back(id);}};
 for(size_t at=0;at<queue.size();++at){uint32_t id=queue[at];int i=id/C,m=id%C;auto [op,a,z,pos]=g[i];if(op==3)continue;if(op==2){add(z,m);continue;}int old=(m/p[a])%3;
  if(op==0){int nc=parity?(old==1?2:1):std::min(2,old+1);add(z,m+(nc-old)*p[a]);}
  else if(old==0)add(z,m);
  else if(parity){if(old==1){add(pos,m-p[a]);add(pos,m+p[a]);}else add(pos,m-p[a]);}
  else if(old==1)add(pos,m-p[a]);
  else {add(pos,m-p[a]);add(pos,m);}
  if(at && at%5000000==0)std::cout<<"PROGRESS "<<at<<" queued "<<queue.size()<<std::endl;
 }
 std::string stem=argv[2];std::ofstream out(stem+".bin",std::ios::binary);out.write(reinterpret_cast<char*>(seen.data()),seen.size());out.close();std::ofstream rows(stem+".rows.tsv");std::array<int,9> masks{};std::array<int,9> digits{};std::vector<std::array<uint8_t,9>> ds(C);for(int m=0;m<C;++m)for(int r=0;r<9;++r)ds[m][r]=(m/p[r])%3;
 std::vector<uint16_t> reps(size_t(n)*512,65535);std::array<int,C> support{};for(int m=0;m<C;++m)for(int r=0;r<9;++r)if(ds[m][r])support[m]|=1<<r;for(int i=0;i<n;++i){masks.fill(0);int count=0;for(int m=0;m<C;++m)if(seen[size_t(i)*C+m]){++count;auto &rep=reps[size_t(i)*512+support[m]];if(rep==65535)rep=m;for(int r=0;r<9;++r)masks[r]|=1<<ds[m][r];}rows<<i<<'\t'<<count;for(int x:masks)rows<<'\t'<<x;rows<<'\n';}
 std::ofstream repout(stem+".representatives.uint16",std::ios::binary);repout.write(reinterpret_cast<char*>(reps.data()),reps.size()*sizeof(uint16_t));repout.close();double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-begin).count();std::ofstream receipt(stem+".json");receipt<<"{\"mode\":\""<<(parity?"zero-positiveodd-positiveeven":"zero-one-atleasttwo")<<"\",\"source_sites\":"<<n<<",\"abstract_states_per_site\":"<<C<<",\"reachable_configurations\":"<<queue.size()<<",\"closure_edges\":"<<edges<<",\"seed_mask\":"<<seed<<",\"seconds\":"<<seconds<<"}\n";std::cout<<"DONE "<<queue.size()<<" edges "<<edges<<" seconds "<<seconds<<std::endl;
}
