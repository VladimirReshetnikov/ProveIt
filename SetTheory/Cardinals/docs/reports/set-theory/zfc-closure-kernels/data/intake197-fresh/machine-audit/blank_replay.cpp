// Independent literal blank-tape replay. C++17, no external libraries.
// Usage: blank_replay table.tm number_of_steps halt_label
// The fixed tape buffer is checked on every step; leaving it aborts.
#include <array>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
struct Action { int write=-1, direction=0, next=-1; };
int main(int argc, char** argv) {
    if (argc != 4) return 2;
    const long long count = std::stoll(argv[2]);
    const int halt = std::stoi(argv[3]);
    std::array<std::array<Action,2>,512> table;
    std::array<bool,512> working{};
    std::ifstream source(argv[1]);
    if (!source) return 3;
    std::string line;
    int row_count=0;
    while (std::getline(source,line)) {
        if (line.empty() || line[0]=='#') continue;
        std::istringstream row(line);
        int q,b,w,z; char d; std::string extra;
        if (!(row>>q>>b>>w>>d>>z) || (row>>extra)) return 4;
        if(q<0 || q>=512 || z<0 || z>=512 || b<0 || b>1 || w<0 || w>1 || (d!='L' && d!='R')) return 5;
        if(table[q][b].write!=-1) return 6;
        table[q][b]={w,d=='L'?-1:1,z}; working[q]=true; ++row_count;
    }
    int state_count=0;
    for (int q=0; q<512; ++q) if(working[q]) {
        ++state_count;
        for(int b=0;b<2;++b) {
            const auto& a=table[q][b];
            if(a.write<0 || (a.next!=halt && !working[a.next])) return 7;
        }
    }
    if(state_count!=216 || row_count!=432 || working[halt]) return 8;
    constexpr int centre=10000;
    std::vector<unsigned char> tape(2*centre+1,0);
    int q=0,h=0,low=0,high=0;
    for(long long tick=0;tick<count;++tick) {
        if(q==halt || !working[q] || h < -centre || h > centre) return 9;
        const Action a=table[q][tape[centre+h]];
        tape[centre+h]=a.write;
        h+=a.direction;q=a.next;
        if(h<low)low=h;
        if(h>high)high=h;
    }
    std::cout<<"{\"steps\":"<<count<<",\"state\":"<<q<<",\"head\":"<<h
             <<",\"head_min\":"<<low<<",\"head_max\":"<<high<<",\"one_cells\":[";
    bool first=true;
    for(int i=0;i<(int)tape.size();++i) if(tape[i]) {
        if(!first)std::cout<<',';
        first=false;std::cout<<(i-centre);
    }
    std::cout<<"]}\n";
    return 0;
}
