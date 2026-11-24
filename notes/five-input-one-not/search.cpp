// A live set consists of exactly the wires needed by some later gate or the output.
// Signed mode represents a pair {f, !f} by the truth table that is false at zero.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>

using Table = std::uint32_t;
struct Wire { Table value; int index; };
struct Gate { char op; int a, b; };
using Wires = std::vector<Wire>;

class Search {
public:
    Table target;
    bool signed_mode;
    int input_count;
    std::vector<Gate> path;

    bool visit(const Wires& wires, int left) {
        for (Wire w : wires) if (w.value == target) return true;
        if (left == 0 || int(wires.size()) > left + 1) return false;
        // Every required positive/negative pair must still be distinguishable.
        // A monotone suffix also needs a wire oriented from 1 to 0 on each pair.
        for (Table positive = target; positive; positive &= positive - 1) {
            unsigned x = __builtin_ctz(positive);
            Table indistinguishable = ~target;
            for (Wire w : wires) {
                if ((w.value >> x) & 1) indistinguishable &= w.value;
                else if (signed_mode) indistinguishable &= ~w.value;
                if (!indistinguishable) break;
            }
            if (indistinguishable) return false;
        }
        for (std::size_t i = 0; i < wires.size(); ++i) {
            for (std::size_t j = i + 1; j < wires.size(); ++j) {
                const Wire a = wires[i], b = wires[j];
                const std::array<Table, 4> values = {a.value & b.value, a.value | b.value,
                                                      a.value & ~b.value, ~a.value & b.value};
                for (int k = 0; k < (signed_mode ? 4 : 2); ++k) {
                    const Table v = values[k];
                    if (v == 0 || std::any_of(wires.begin(), wires.end(),
                                              [v](Wire w) { return w.value == v; })) continue;
                    const int index = input_count + int(path.size());
                    path.push_back({"AOLR"[k], a.index, b.index});
                    if (v == target) return true;
                    if (left > 1) {
                        for (unsigned keep = 0; keep < 4; ++keep) {
                            if (int(wires.size()) - 1 + __builtin_popcount(keep) > left) continue;
                            Wires next;
                            next.reserve(wires.size() + 1);
                            for (std::size_t n = 0; n < wires.size(); ++n) {
                                if (n == i && !(keep & 1)) continue;
                                if (n == j && !(keep & 2)) continue;
                                next.push_back(wires[n]);
                            }
                            next.push_back({v, index});
                            if (visit(next, left - 1)) return true;
                        }
                    }
                    path.pop_back();
                }
            }
        }
        return false;
    }
};

int main(int argc, char** argv) {
    if (argc != 4 && argc != 5) return 2;
    const std::string mode = argv[3];
    if (mode != "signed" && mode != "monotone") return 2;
    const int n = argc == 5 ? std::stoi(argv[4]) : 5;
    if (n < 1 || n > 5) return 2;
    Search search{static_cast<Table>(std::stoul(argv[1], nullptr, 16)), mode == "signed", n, {}};
    Wires inputs;
    for (int i = 0; i < n; ++i) {
        Table v = 0;
        for (int x = 0; x < 32; ++x) v |= Table((x >> i) & 1) << x;
        inputs.push_back({v, i});
    }
    // The search starts with all designated inputs live. Check this precondition.
    for (int i = 0; i < n; ++i) {
        if (((search.target ^ (search.target >> (1 << i))) & ~inputs[i].value) == 0) return 2;
    }
    const int budget = std::stoi(argv[2]);
    if (budget < 0 || (search.target & 1)) return 2;
    if (search.visit(inputs, budget)) {
        std::cout << "SAT";
        for (Gate g : search.path) std::cout << " " << g.op << "," << g.a << "," << g.b;
    } else {
        std::cout << "UNSAT";
    }
    std::cout << "\n";
}
