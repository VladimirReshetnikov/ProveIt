// Literal, bounded simulation of the KNOWN runtime-only 252-state quotient.
// This executable neither proves nonhalting nor proves a valid initialization.
// Arguments: original 254-state table, legal PC words, maximum moves, minimum gap.
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_set>
#include <vector>

struct Action { int write = 0, move = 0, target = 0; bool present = false; };

int main(int argc, char** argv) {
    try {
        if (argc != 5) throw std::runtime_error("Usage: bootstrap_extension TABLE PC_WORDS LIMIT MIN_GAP");
        const uint64_t limit = std::stoull(argv[3]);
        const int minimum_gap = std::stoi(argv[4]);
        if (minimum_gap < 34) throw std::runtime_error("MIN_GAP must be at least 34");
        std::ifstream input(argv[1]);
        if (!input) throw std::runtime_error("Cannot read table");
        std::array<std::array<Action, 2>, 254> table{};
        std::string line;
        int rows = 0;
        while (std::getline(input, line)) {
            if (line.empty() || line[0] == '#') continue;
            int q, read, write, target; char move;
            std::istringstream row(line);
            if (!(row >> q >> read >> write >> move >> target) || q < 0 || q >= 254 ||
                read < 0 || read > 1 || write < 0 || write > 1 || target < 0 || target > 254 ||
                (move != 'L' && move != 'R') || table[q][read].present)
                throw std::runtime_error("Malformed table");
            table[q][read] = {write, move == 'R' ? 1 : -1, target, true};
            ++rows;
        }
        if (rows != 508) throw std::runtime_error("Expected exactly 508 original rows");
        std::ifstream pc_input(argv[2]);
        if (!pc_input) throw std::runtime_error("Cannot read legal PC words");
        std::unordered_set<uint64_t> pc_words;
        uint64_t pc;
        while (pc_input >> pc) pc_words.insert(pc);
        if (pc_words.size() != 6460) throw std::runtime_error("Expected 6460 legal PC words");
        table[3][0] = {0, -1, 48, true};
        for (int q : {5, 8}) for (auto& action : table[q]) action.present = false;
        for (int q = 0; q < 254; ++q) for (const auto& action : table[q])
            if (action.present && (action.target == 5 || action.target == 8))
                throw std::runtime_error("Deleted state still targeted");

        // A finite array is safe for this bounded run because every move is
        // bounds-checked; an exhausted array terminates with an error.
        constexpr int origin = 1000000, size = 5000000;
        std::vector<unsigned char> tape(size, 0);
        int head = origin, low = size, high = -1, ones = 0, state = 64;
        uint64_t dispatch_visits = 0, syntactic_frames = 0, frames = 0;
        for (uint64_t steps = 0; ; ++steps) {
            if (state == 96) {
                ++dispatch_visits;
                if (tape[head - 1] && low == head - 1) {
                    int header = head + 34;
                    while (header <= high && !tape[header]) ++header;
                    if (header <= high && header - head >= minimum_gap) {
                        int cursor = header + 1;
                        std::vector<int> registers;
                        while (cursor < high && !tape[cursor] && tape[cursor + 1]) {
                            ++cursor;
                            int length = 0;
                            while (cursor <= high && tape[cursor]) { ++length; ++cursor; }
                            registers.push_back(length - 1);
                        }
                        if (registers.size() >= 9 && cursor > high) {
                            ++syntactic_frames;
                            uint64_t pc_word = 0;
                            for (int i = 0; i < 34; ++i) pc_word = 2 * pc_word + tape[head + i];
                            if (!pc_words.count(pc_word)) goto no_frame;
                            ++frames;
                            std::cout << "{\"outcome\":\"frame\",\"moves\":" << steps
                                      << ",\"state_old_label\":96,\"head\":" << head - origin
                                      << ",\"gap\":" << header - head << ",\"registers_physical_order\":[";
                            for (size_t i = 0; i < registers.size(); ++i) {
                                if (i) std::cout << ',';
                                std::cout << registers[i];
                            }
                            std::cout << "],\"pc_cells_34\":\"";
                            for (int i = 0; i < 34; ++i) std::cout << int(tape[head + i]);
                            std::cout << "\"}\n";
                            return 0;
                        }
                    }
                }
            }
            no_frame:
            if (state == 254 || steps == limit) {
                std::cout << "{\"outcome\":\"" << (state == 254 ? "halt" : "bounded_limit")
                          << "\",\"moves\":" << steps << ",\"minimum_frame_gap\":" << minimum_gap
                          << ",\"state_old_label\":" << state << ",\"head\":" << head - origin
                          << ",\"ones\":" << ones << ",\"leftmost_one\":" << low - origin
                          << ",\"rightmost_one\":" << high - origin
                          << ",\"dispatch_visits\":" << dispatch_visits
                          << ",\"syntactic_frames\":" << syntactic_frames
                          << ",\"legal_pc_frames\":" << frames << "}\n";
                return 0;
            }
            const Action action = table.at(state).at(tape[head]);
            if (!action.present) throw std::runtime_error("Entered a deleted/missing state");
            if (action.write != tape[head]) {
                tape[head] = action.write;
                ones += action.write ? 1 : -1;
                if (action.write) {
                    if (head < low) low = head;
                    if (head > high) high = head;
                } else {
                    if (head == low) while (low <= high && !tape[low]) ++low;
                    if (head == high) while (high >= low && !tape[high]) --high;
                    if (!ones) { low = size; high = -1; }
                }
            }
            state = action.target;
            head += action.move;
            if (head < 1 || head >= size - 1) throw std::runtime_error("Tape bounds exhausted");
            if ((steps + 1) % 100000000 == 0)
                std::cerr << "Completed " << steps + 1 << " moves; state " << state
                          << "; ones " << ones << "; one-support " << low - origin << ':' << high - origin << '\n';
        }
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 2;
    }
}
