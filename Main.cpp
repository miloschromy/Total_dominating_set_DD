/* For now it is just exact dd with dangling nodes haning around.need to update :
* 1. layer cleaning process - noneperspective nodes, dominated by other nodes can be thrown away, for now they are just dangling around
* 2. clear nonperspective nodes recursively - some nodes cant be extended to full dominating set, so we can delete them from representation
* 3. restricted dd can be easy - just find the comparator to compare the whole layer - sum of state, best path to node and some estimate to finish (avg of inedges?? or worstedge?? or edge+inedgevertex weight??)
* 4. merging will be harder, we can do same as 1. however not include best_path_to_vertex, or to add more relaxation make a state by min, for all parts
*/

#include<iostream>
#include<fstream>
#include<string>
#include<vector>
#include<map>
#include<set>
#include<numeric>
#include <algorithm>

#include <chrono> 
#include <filesystem>

using namespace std;
namespace fs = std::filesystem;

typedef pair<size_t, size_t> Edge_t;
typedef int Weight_t;
constexpr Weight_t INIIT_EDGE_WEIGHT = -1;
constexpr Weight_t DEFAULT_BEST_PATH = -1;

struct Graph_t {
	vector<vector<size_t>> adjacency_matrix;
	vector<Weight_t> vertex_weight;
	map<Edge_t, Weight_t> edge_weight;
  void add_oriented_edge(const size_t& source, const size_t& target, const Weight_t& weight=1) {
    adjacency_matrix[source].push_back(target);
    edge_weight[make_pair(source, target)] = weight;
  }
  void add_unoriented_edge(const size_t& source, const size_t& target, const Weight_t& weight=1) {
    add_oriented_edge(source, target, weight);
    add_oriented_edge(target, source, weight);
  }
  size_t vertex_count() {
    return adjacency_matrix.size();
  }
};

/// <summary>
///Structure for maintaining state of DP. 
/// </summary>
/// <typeparam name="T">Boolean for unweighted variant, int/float for weighted variant</typeparam>
struct State_t {
	vector<Weight_t> weights_vector;
  State_t() {
    weights_vector.clear();
  }
  State_t(const size_t& vertex_count) {
    weights_vector = vector<Weight_t>(vertex_count, INIIT_EDGE_WEIGHT);
  }
  State_t(const State_t& init_state) {
    weights_vector = init_state.weights_vector;
  }
};


/// <summary>
/// Decision node which hase two decisions decisionvariable = 0,1 and list of parrents (0 a 1)
/// </summary>
struct DecisionNode_t {
  Weight_t best_path;
	State_t node_state;
	vector<size_t> decisions;
	vector<vector<size_t>> parents;
	size_t decision_variable;
  DecisionNode_t() { node_state = State_t(); decisions.resize(2); parents = { {},{} }; best_path = DEFAULT_BEST_PATH; };
  DecisionNode_t(const size_t& vertex_count, const size_t& dvar, const Weight_t& bpath) {
    node_state = State_t(vertex_count);
    parents = { {},{} };
    decision_variable = dvar;
    best_path = bpath;
  }
  DecisionNode_t(const size_t& vertex_count, const size_t& dvar): DecisionNode_t(vertex_count, dvar, DEFAULT_BEST_PATH) {}
  DecisionNode_t(const size_t& vertex_count) : DecisionNode_t(vertex_count, DEFAULT_BEST_PATH){}
  DecisionNode_t(const DecisionNode_t& dnode) {
    parents.resize(dnode.parents.size());
    for (size_t i = 0; i < dnode.parents.size(); ++i) {
      parents[i] = dnode.parents[i];
    }
    decision_variable = dnode.decision_variable;
    node_state = dnode.node_state;
    decisions = dnode.decisions;
    best_path = dnode.best_path;
  }
  DecisionNode_t(const State_t& init_state, const size_t& dvar, const Weight_t& bpath) {
    node_state = init_state;
    parents = { {},{} };
    decision_variable = dvar;
    best_path = bpath;
  }
  DecisionNode_t(const State_t& init_state, const size_t& dvar):DecisionNode_t(init_state, dvar, DEFAULT_BEST_PATH) {}
  DecisionNode_t(const State_t& init_state) : DecisionNode_t(init_state, DEFAULT_BEST_PATH) {}
};
int cmp_soft(const State_t& lhs, const State_t& rhs) {
  for (size_t i = 0; i < lhs.weights_vector.size(); ++i) {
    if (lhs.weights_vector[i] < rhs.weights_vector[i]) return -1;
    if (lhs.weights_vector[i] > rhs.weights_vector[i]) return 1;
  }
  return 0;
}
int cmp_hard(const State_t& lhs, const State_t& rhs) {
  int state = 0;
  for (size_t i = 0; i < lhs.weights_vector.size(); ++i) {
    if (lhs.weights_vector[i] != INIIT_EDGE_WEIGHT && (lhs.weights_vector[i] < rhs.weights_vector[i] || rhs.weights_vector[i] == INIIT_EDGE_WEIGHT)) {
      if (state > 0) { return 0; }
      state = -1;
    }
    if (rhs.weights_vector[i] != INIIT_EDGE_WEIGHT && (lhs.weights_vector[i] > rhs.weights_vector[i] || lhs.weights_vector[i] == INIIT_EDGE_WEIGHT)) {
      if (state < 0) { return 0; }
      state = 1;
    }
    
  }
  return state;
}
inline bool operator==(const State_t& lhs, const State_t& rhs) { return cmp_soft(lhs, rhs) == 0; }
inline bool operator!=(const State_t& lhs, const State_t& rhs) { return cmp_soft(lhs, rhs) != 0; }
inline bool operator< (const State_t& lhs, const State_t& rhs) { return cmp_soft(lhs, rhs) < 0; }
inline bool operator> (const State_t& lhs, const State_t& rhs) { return cmp_soft(lhs, rhs) > 0; }
inline bool operator<=(const State_t& lhs, const State_t& rhs) { return cmp_soft(lhs, rhs) <= 0; }
inline bool operator>=(const State_t& lhs, const State_t& rhs) { return cmp_soft(lhs, rhs) >= 0; }

/// <summary>
/// update the neigbours of dominating vertex in the state
/// </summary>
/// <param name="input_graph"></param>
/// <param name="state_to_update"></param>
/// <param name="dominating_vertex"></param>
void state_change_by_domination(Graph_t& input_graph, State_t& state_to_update, const size_t& dominating_vertex) {
  for (size_t& vertex_id : input_graph.adjacency_matrix[dominating_vertex]){
    Weight_t new_edge_weight = input_graph.edge_weight[make_pair(dominating_vertex, vertex_id)];
    if (state_to_update.weights_vector[vertex_id] > new_edge_weight || state_to_update.weights_vector[vertex_id] == INIIT_EDGE_WEIGHT) { //domination is better than it was before
      state_to_update.weights_vector[vertex_id] = new_edge_weight;
      }
  }
}


/// <summary>
/// insert a new node to a new layer
/// </summary>
/// <param name="input_graph">input graph</param>
/// <param name="new_layer_hash">has table of new layer to save the cache</param>
/// <param name="DD_new_layer">new layer in representation, to insert new node and update parents</param>
/// <param name="source_decision_node">decision node for which we are making decision</param>
/// <param name="decision">decision value</param>
/// <param name="parent_index">index of the parent to add to parents[decision]</param>
/// <param name="descendat_variable_id">next decision variable id according to order of OBDD</param>
/// <param name="possible_to_dominate">Check if node creation makes sense as it is not neccessary to use</param>
/// <returns></returns>
size_t insert_new_node(Graph_t& input_graph, map<State_t, size_t>& new_layer_hash, vector<DecisionNode_t>& DD_new_layer, const DecisionNode_t& source_decision_node, 
                        const size_t& decision, const size_t& parent_index, const size_t& descendat_variable_id, 
                        const vector<size_t>& possible_to_dominate) {
  size_t decision_variable_id = source_decision_node.decision_variable;
  Weight_t cheapest_path_to_parent = source_decision_node.best_path;
  State_t new_state(source_decision_node.node_state);

  pair< map<State_t, size_t>::const_iterator, bool> new_layer_inserter; //find inserter interior
  if (decision) state_change_by_domination(input_graph, new_state, decision_variable_id); //update state if decision x_i=1

  for (size_t vertex_check = 0; vertex_check < possible_to_dominate.size(); ++vertex_check) {
    if (!possible_to_dominate[vertex_check] && new_state.weights_vector[vertex_check] == INIIT_EDGE_WEIGHT) return -1; //we cant use it for cover
  }
    
  new_layer_inserter = new_layer_hash.insert(make_pair(new_state, DD_new_layer.size())); //if inserted, it will point to new layer end vertex, which we will add
  if (new_layer_inserter.second == true) { //was not inserted did not exist, need to bye inserted
    DD_new_layer.push_back(DecisionNode_t(new_state, descendat_variable_id, cheapest_path_to_parent + (decision!=0)*input_graph.vertex_weight[decision_variable_id])); //insert new node, dont fill parents, just variable number
  }
  DD_new_layer[new_layer_inserter.first->second].parents[decision].push_back(parent_index); // add parent for the node together with its decision edge
  if (DD_new_layer[new_layer_inserter.first->second].best_path > cheapest_path_to_parent + (decision != 0) * input_graph.vertex_weight[decision_variable_id]) {
    DD_new_layer[new_layer_inserter.first->second].best_path = cheapest_path_to_parent + (decision != 0) * input_graph.vertex_weight[decision_variable_id];
  }
  return new_layer_inserter.first->second;
}


/// <summary>
/// Marks vertices to ignore in this layer as they are dominated later
/// </summary>
/// <param name="exact_DD">exact dd which we want to clean up</param>
/// <param name="is_dominated">incidence vecor of to be ignoered nodes</param>
void find_dead_end_nodes(const vector<vector<DecisionNode_t>>& exact_DD, vector<bool>& is_dominated) {
  is_dominated.clear();
  is_dominated.resize(exact_DD.back().size(), 0);
  for (size_t i = 0; i < exact_DD.back().size()-1; ++i) {
    for (size_t j = i + 1; j < exact_DD.back().size(); ++j) {
      if (!is_dominated[j]) {
        int compare_res = cmp_hard(exact_DD.back()[i].node_state, exact_DD.back()[j].node_state);
        is_dominated[j] = exact_DD.back()[i].best_path < exact_DD.back()[j].best_path && compare_res == -1;
        is_dominated[i] = exact_DD.back()[i].best_path > exact_DD.back()[j].best_path && compare_res == 1;
      }
    }
  }
}

/// <summary>
/// creates an exact decision diagram for a total weighted set problem
/// </summary>
/// <returns>best dominating set value</returns>
Weight_t create_exact_dd(Graph_t& input_graph, vector<size_t>& variables_order) {
  vector<size_t> possible_to_dominate(input_graph.vertex_count());
  for (const pair<Edge_t, Weight_t>& dedge : input_graph.edge_weight) { //for unoriented vertices is enough to check adjacency_matrix[i].size(), for dvariant we dont have input degree
    ++possible_to_dominate[dedge.first.second];
  }
  vector<bool> DDnode_is_dominated({ 0 }); //incidence whether we should ignore a node of exact dd

  variables_order.push_back(-1); // terminal node is in the last layer, we dont care about the value
	vector<vector<DecisionNode_t>> exact_DD;
  exact_DD.push_back({ DecisionNode_t(input_graph.adjacency_matrix.size(), variables_order[0], 0)}); //root with clean state as nothing is covered yet
  // each layer
  for (size_t variable_order_index = 0; variable_order_index < variables_order.size()-1; ++variable_order_index) {//layer by layer
    for (const size_t& neigbour : input_graph.adjacency_matrix[variables_order[variable_order_index]]) {
      --possible_to_dominate[neigbour];
    }
    map<State_t, size_t> new_layer; //decision node and its index in the new layer
    exact_DD.push_back({});
    for (size_t processed_node_index=0; processed_node_index < exact_DD[variable_order_index].size(); ++processed_node_index){ //process each node on current layer
      if (DDnode_is_dominated[processed_node_index]) { continue; }
      exact_DD[variable_order_index][processed_node_index].decisions.resize(2);
      for (size_t new_decision = 0; new_decision < 2; ++new_decision) { //each decision for current node 
        exact_DD[variable_order_index][processed_node_index].decisions[new_decision] =                          //connect decision to the right node returned from this complicated function
          insert_new_node(input_graph, new_layer, exact_DD[variable_order_index + 1], exact_DD[variable_order_index][processed_node_index], 
            new_decision, processed_node_index, variables_order[variable_order_index + 1], possible_to_dominate);
      }
    }
    find_dead_end_nodes(exact_DD, DDnode_is_dominated);

  }

 
  auto best_element = min_element(exact_DD.back().begin(), exact_DD.back().end(), [](const DecisionNode_t& lhs, const DecisionNode_t& rhs) {
     return (accumulate(lhs.node_state.weights_vector.end(), lhs.node_state.weights_vector.end(), 0) + lhs.best_path) < 
            (accumulate(rhs.node_state.weights_vector.end(), rhs.node_state.weights_vector.end(), 0) + rhs.best_path);});
  return best_element->best_path;
  
};


bool read_input_graph(Graph_t& graph_to_be_dominated, ifstream& input_stream) {
  graph_to_be_dominated.adjacency_matrix.clear();
  if (!input_stream.good()) {
    cerr << "Data loading error.\n";
    return 0;
  }
  size_t vertex_count, edges_count, source, target;
  Weight_t weight=1;
  bool weighted;
  input_stream >> vertex_count >> edges_count >> weighted;
  for (size_t i=0; i < vertex_count; ++i) {
    if (weighted) {
      input_stream >> weight;
    }
    graph_to_be_dominated.vertex_weight.push_back(weight);
    graph_to_be_dominated.adjacency_matrix.push_back({});
  }
  for (size_t i=0; i < edges_count; ++i) {
    input_stream >> source >> target;
    if (weighted) {
      input_stream >> weight;
    }
    graph_to_be_dominated.add_unoriented_edge(source, target, weight);
  }
  return 1;
}


struct Restriction_t {
  size_t max_level_width;
  size_t best_known_result;
  size_t mode; //0 exact, 1 restrict, 2 relax
  Restriction_t(const size_t& mw, const size_t& bkr, const size_t& m = 0) { max_level_width = mw; best_known_result = bkr; mode = m; }
  /*bool comparator_for_layer(const set<DecisionNode_t>& curr_layer, const size_t& x, const size_t& y) {
    return  curr_layer[x].shortest_path < curr_layer[y].shortest_path;
  }*/
};

int main(int argc, char* argv[]){
  string path = "input";
  ofstream results_stream(".\\output\\results.csv");
  results_stream << "n, max_width, result, time\n";
  for (const auto& entry : fs::directory_iterator(path)) {
    cout << entry.path() << endl;
    results_stream << entry.path() << endl;

    //load data
    Graph_t input_graph;
    vector<size_t> variables_order;
    ifstream input_stream(entry.path());
    if (!read_input_graph(input_graph, input_stream)) {
      cerr << "Something went wrong." << endl;
    }
    input_stream.close();
    for (size_t i = 0; i < input_graph.adjacency_matrix.size(); ++i) {
      variables_order.push_back(i);
    }
    Restriction_t restrictions(1000, 0, 1);

    for (int i = 1; i <= 1; i *= 10) {
      //max width restrictions
      restrictions.max_level_width = i;

      auto start = chrono::high_resolution_clock::now();
      Weight_t result = create_exact_dd(input_graph, variables_order);
      auto duration = chrono::duration_cast<chrono::seconds>(chrono::high_resolution_clock::now() - start);
      cout << result << " in " << duration.count() << endl;
      results_stream << duration.count() << endl;
    }
  }


	return 0;
}