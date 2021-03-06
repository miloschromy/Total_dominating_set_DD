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
#include <cassert>

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

typedef vector<vector<DecisionNode_t>> DecisionDiagram_t;

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
size_t DD_insert_new_node(Graph_t& input_graph, map<State_t, size_t>& new_layer_hash, vector<DecisionNode_t>& DD_new_layer, const DecisionNode_t& source_decision_node, 
                        const size_t& decision, const size_t& parent_index, const size_t& descendat_variable_id, 
                        const vector<size_t>& possible_to_dominate) {
  size_t decision_variable_id = source_decision_node.decision_variable;
  Weight_t cheapest_path_to_parent = source_decision_node.best_path;
  if (decision) cheapest_path_to_parent += input_graph.vertex_weight[decision_variable_id];
  State_t new_state(source_decision_node.node_state);

  pair< map<State_t, size_t>::const_iterator, bool> new_layer_inserter; //find inserter interior
  if (decision) state_change_by_domination(input_graph, new_state, decision_variable_id); //update state if decision x_i=1

  for (size_t vertex_check = 0; vertex_check < possible_to_dominate.size(); ++vertex_check) {
    if (!possible_to_dominate[vertex_check] && new_state.weights_vector[vertex_check] == INIIT_EDGE_WEIGHT) return -1; //we cant use it for cover
  }
    
  new_layer_inserter = new_layer_hash.insert(make_pair(new_state, DD_new_layer.size())); //if inserted, it will point to new layer end vertex, which we will add
  if (new_layer_inserter.second == true) { //was not inserted did not exist, need to bye inserted
    DD_new_layer.push_back(DecisionNode_t(new_state, descendat_variable_id, cheapest_path_to_parent)); //insert new node, dont fill parents, just variable number
  }
  DD_new_layer[new_layer_inserter.first->second].parents[decision].push_back(parent_index); // add parent for the node together with its decision edge
  if (DD_new_layer[new_layer_inserter.first->second].best_path > cheapest_path_to_parent) {
    DD_new_layer[new_layer_inserter.first->second].best_path = cheapest_path_to_parent;
  }
  return new_layer_inserter.first->second;
}


/// <summary>
/// Marks vertices to ignore in this layer as they are dominated later
/// </summary>
/// <param name="exact_DD">exact dd which we want to clean up</param>
/// <param name="is_dominated">incidence vecor of to be ignoered nodes</param>
void find_dead_end_nodes(const DecisionDiagram_t& exact_DD, vector<bool>& is_dominated, vector<size_t>& list_of_dominated) {
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
  list_of_dominated.clear();
  for (size_t i = 0; i < is_dominated.size(); ++i) {
    if (is_dominated[i]) list_of_dominated.push_back(i);
  }
}



/// <summary>
/// Swap two nodes and all connections on layer
/// </summary>
/// <param name="Decision_diagram"></param>
/// <param name="layer">Layer of swaping nodes</param>
/// <param name="node1">First node to swap on specified layer</param>
/// <param name="node2">Second node to swap on specified layer</param>
void DD_swap_nodes(DecisionDiagram_t& Decision_diagram, const size_t& layer, const size_t& node1, const size_t& node2) {
  if (node1 == node2) return;
//flip pointers from parents and descendants node2 <-> node1 for each decision 0,1
for (size_t decision_val = 0; decision_val < 2; ++decision_val) {
  for (size_t& parent : Decision_diagram[layer][node1].parents[decision_val]) { //for each parent of node1 with parent[decision_val]=node1 redirect it to node2
    assert(Decision_diagram[layer - 1][parent].decisions[decision_val] == node1);
    Decision_diagram[layer - 1][parent].decisions[decision_val] = node2;
  }
  for (size_t& parent : Decision_diagram[layer][node2].parents[decision_val]) { //for each parent of node 2 do the same as above
    assert(Decision_diagram[layer - 1][parent].decisions[decision_val] == node2);
    Decision_diagram[layer - 1][parent].decisions[decision_val] = node1;
  }
  if (Decision_diagram[layer][node1].decisions.size() > decision_val && Decision_diagram[layer][node1].decisions[decision_val] != -1) { //we have already instanciated the decision an it is not null
    replace(Decision_diagram[layer + 1][Decision_diagram[layer][node1].decisions[decision_val]].parents[decision_val].begin(), Decision_diagram[layer + 1][Decision_diagram[layer][node1].decisions[decision_val]].parents[decision_val].end(),
      node1, node2);
  }
  if (Decision_diagram[layer][node2].decisions.size() > decision_val && Decision_diagram[layer][node2].decisions[decision_val] != -1) { //we have already instanciated the decision an it is not null
    replace(Decision_diagram[layer + 1][Decision_diagram[layer][node2].decisions[decision_val]].parents[decision_val].begin(), Decision_diagram[layer + 1][Decision_diagram[layer][node2].decisions[decision_val]].parents[decision_val].end(),
      node2, node1);
  }
}
//flip descendants
//flip content of nodes
//swap states
Decision_diagram[layer][node1].node_state.weights_vector.swap(Decision_diagram[layer][node2].node_state.weights_vector);
//swap parents
Decision_diagram[layer][node1].parents[0].swap(Decision_diagram[layer][node2].parents[0]);
Decision_diagram[layer][node1].parents[1].swap(Decision_diagram[layer][node2].parents[1]);
//Decisions_swap
Decision_diagram[layer][node1].decisions.swap(Decision_diagram[layer][node2].decisions);
//best_path swap
swap(Decision_diagram[layer][node1].best_path, Decision_diagram[layer][node2].best_path);
swap(Decision_diagram[layer][node1].decision_variable, Decision_diagram[layer][node2].decision_variable);

}

/// <summary>
/// Removes a node on specified layer by swaping it with the last node of layer and removing it
/// </summary>
/// <param name="Decision_diagram">dd node for swap</param>
/// <param name="layer_id">layer id where, node_id should be deleted</param>
/// <param name="node_id">id of node on layer_id</param>
void DD_remove_one_node(DecisionDiagram_t& Decision_diagram, const size_t& layer_id, const size_t& node_id) {
  //first clear all refernces to node which we want to delete
  for (size_t decision_val = 0; decision_val < 2; ++decision_val) {
    //clear parent decisions
    for (auto parent : Decision_diagram[layer_id][node_id].parents[decision_val]) {
      Decision_diagram[layer_id - 1][parent].decisions[decision_val] = -1;
    }
    Decision_diagram[layer_id][node_id].parents[decision_val].clear();
    //clear descendant parents pointers
    if (Decision_diagram[layer_id][node_id].decisions.size() > decision_val  //we have created the decision for descendatn
      && Decision_diagram[layer_id][node_id].decisions[decision_val] != -1){ //the decision is not null
      auto element = find(Decision_diagram[layer_id + 1][Decision_diagram[layer_id][node_id].decisions[decision_val]].parents[decision_val].begin(), 
              Decision_diagram[layer_id + 1][Decision_diagram[layer_id][node_id].decisions[decision_val]].parents[decision_val].end(), node_id);
      *element = Decision_diagram[layer_id + 1][Decision_diagram[layer_id][node_id].decisions[decision_val]].parents[decision_val].back();
      Decision_diagram[layer_id + 1][Decision_diagram[layer_id][node_id].decisions[decision_val]].parents[decision_val].pop_back();
      Decision_diagram[layer_id][node_id].decisions[decision_val] = -1;
    }

  }
  DD_swap_nodes(Decision_diagram, layer_id, node_id, Decision_diagram[layer_id].size() - 1); //swap node to delete and last vertex
  Decision_diagram[layer_id].pop_back(); //remove lasta vertexa
}


/// <summary>
/// Merge all nodes from vector nodes_to_merge on layer_id (last layer). We expect that nodes are on the last layer as we do nothing with the decisions. We take the min
/// </summary>
/// <param name="Decision_diagram">Input diagram.</param>
/// <param name="layer_id">Layer containing vertices to merge.</param>
/// <param name="nodes_to_merge">Vector of vertices to merge.</param>
void DD_merge_nodes(DecisionDiagram_t& Decision_diagram, const size_t& layer_id, vector<size_t>& nodes_to_merge) {
  //merge state => what the fuck that does even mean? for now i take the min of all
  for (size_t i = 0; i < Decision_diagram[layer_id][nodes_to_merge[0]].node_state.weights_vector.size(); ++i) { //node[0] is new node
    size_t min_id = *min_element(nodes_to_merge.begin(), nodes_to_merge.end(), [&Decision_diagram, &layer_id, &i](size_t& node1, size_t& node2) {
      if (Decision_diagram[layer_id][node1].node_state.weights_vector[i] == INIIT_EDGE_WEIGHT) return false;
      if (Decision_diagram[layer_id][node2].node_state.weights_vector[i] == INIIT_EDGE_WEIGHT) return true;
      return Decision_diagram[layer_id][node1].node_state.weights_vector[i] < Decision_diagram[layer_id][node2].node_state.weights_vector[i];
      }); //find the minimal value for each state
    Decision_diagram[layer_id][nodes_to_merge[0]].node_state.weights_vector[i] = Decision_diagram[layer_id][min_id].node_state.weights_vector[i]; //this magik assign to i. variable lowest value, but does not take in account the -1 problem, os have to reimplement that part
  }
  for (size_t decision_val = 0; decision_val < 2; ++decision_val) { //merge parents by decision in set and then assign it to the vertex
    set<size_t> collect_parents;
    for (auto x : nodes_to_merge) {
      collect_parents.insert(Decision_diagram[layer_id][x].parents[decision_val].begin(), Decision_diagram[layer_id][x].parents[decision_val].end());
    }
    Decision_diagram[layer_id][nodes_to_merge[0]].parents[decision_val].assign(collect_parents.begin(), collect_parents.end()); //assign parents to the first node, which we chosed to be merged
    for (auto parent : collect_parents) { //set decisions for parents to right node
      Decision_diagram[layer_id - 1][parent].decisions[decision_val] = nodes_to_merge[0];
    }
  }
  //finally we remove all vertices which we do not want, we have to do it from the back as we change the order of nodes during the process
  for (int rwalker = nodes_to_merge.size() - 1; rwalker > 0; --rwalker) {
    DD_remove_one_node(Decision_diagram, layer_id, nodes_to_merge[rwalker]);
  }
}

void DD_refine_node(Graph_t& input_graph, DecisionDiagram_t& Decision_diagram, const size_t& layer_id, const size_t& node_id) {
  //copy content of old node to new node
  DecisionNode_t node_to_refine(Decision_diagram[layer_id][node_id]);
  //remove it from the decision diagram
  DD_remove_one_node(Decision_diagram, layer_id, node_id);

  //----------------this has to be changed, it will just fill the inputdeg for each vertex------
  //-----------------===================================================================--------------
  vector<size_t> possible_to_dominate(input_graph.vertex_count(), 0);
  for (const pair<Edge_t, Weight_t>& dedge : input_graph.edge_weight) { //for unoriented vertices is enough to check adjacency_matrix[i].size(), for dvariant we dont have input degree
    ++possible_to_dominate[dedge.first.second];
  }
  //split the decision
  //create a db for layer, maybe we should keep that db or change the adress of nodes
  map<State_t, size_t> layer_hash;
  for (size_t layer_it = 0; layer_it <= Decision_diagram[layer_id].size() - 1; ++layer_it) { //hash current layer
    layer_hash.insert(make_pair(Decision_diagram[layer_id][layer_it].node_state, layer_it));
  }
  for (size_t decision_val = 0; decision_val < 2; ++decision_val) { //we will create new nodes for each parent[decision] = refined_node
    size_t decision_index = node_to_refine.decisions.size() > decision_val ? node_to_refine.decisions[decision_val] : -1; //get the decision val (-1 if the decision does not exist)
    for (auto parent : node_to_refine.parents[decision_val]) {
      size_t new_node_index = //associate decision with new decision on layer_id, set up the parent and decision connections right
        DD_insert_new_node(input_graph, layer_hash, Decision_diagram[layer_id], Decision_diagram[layer_id - 1][parent], 
          decision_val, parent, node_to_refine.decision_variable, possible_to_dominate);
      Decision_diagram[layer_id - 1][parent].decisions[decision_val] = new_node_index;
      if (new_node_index != -1) { //we have created the node
        Decision_diagram[layer_id][new_node_index].decisions.resize(2); //reserve the decision size for new node
        Decision_diagram[layer_id][new_node_index].decisions[decision_val] = decision_index; //set up decision to layer_id+1
        if (decision_index != -1) { //if it is not false node, so decision exists and it is valid
          Decision_diagram[layer_id + 1][decision_index].parents[decision_val].push_back(new_node_index); //set a new decision for the parent
        }
      }
    }
  }
  //choose nodes to merge if we want to


}

/// <summary>
/// clears the last layer of currently build DD
/// </summary>
/// <param name="Decision_diagram">Decision diagram</param>
/// <param name="marked_to_delete">list of nodes marked to delete in ascending order</param>
void clear_last_constructed_layer(DecisionDiagram_t& Decision_diagram, vector<size_t>& marked_to_delete) {
  for (int rwalker = marked_to_delete.size() - 1; rwalker >= 0; --rwalker) {
    DD_remove_one_node(Decision_diagram, Decision_diagram.size()-1, marked_to_delete[rwalker]);
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
  vector<size_t> DDnodes_dominated_list;

  variables_order.push_back(-1); // terminal node is in the last layer, we dont care about the value
  DecisionDiagram_t exact_DD;
  exact_DD.push_back({ DecisionNode_t(input_graph.adjacency_matrix.size(), variables_order[0], 0)}); //root with clean state as nothing is covered yet
  // each layer
  for (size_t variable_order_index = 0; variable_order_index < variables_order.size()-1; ++variable_order_index) {//layer by layer
    cerr << "<<<<<---------Layer " << variable_order_index << "-------";
    for (const size_t& neigbour : input_graph.adjacency_matrix[variables_order[variable_order_index]]) {
      --possible_to_dominate[neigbour];
    }
    map<State_t, size_t> new_layer; //decision node and its index in the new layer
    exact_DD.push_back({});
    DDnodes_dominated_list.clear();
    for (size_t processed_node_index=0; processed_node_index < exact_DD[variable_order_index].size(); ++processed_node_index){ //process each node on current layer
      //if (DDnode_is_dominated[processed_node_index]) { continue; } we dont have to check this as we delete all such nodes
      exact_DD[variable_order_index][processed_node_index].decisions.resize(2);
      for (size_t new_decision = 0; new_decision < 2; ++new_decision) { //each decision for current node 
        exact_DD[variable_order_index][processed_node_index].decisions[new_decision] =                          //connect decision to the right node returned from this complicated function
          DD_insert_new_node(input_graph, new_layer, exact_DD[variable_order_index + 1], exact_DD[variable_order_index][processed_node_index], 
            new_decision, processed_node_index, variables_order[variable_order_index + 1], possible_to_dominate);
      }
    }
    find_dead_end_nodes(exact_DD, DDnode_is_dominated, DDnodes_dominated_list); //we will find nodes which we dont want to expand and hence can be deleted
    clear_last_constructed_layer(exact_DD, DDnodes_dominated_list); // clear last layer
    cerr << exact_DD.back().size() << " nodes----->>>>>>>>\n";
  }

  
  auto best_element = min_element(exact_DD.back().begin(), exact_DD.back().end(), [](const DecisionNode_t& lhs, const DecisionNode_t& rhs) {
    bool lhsbad = any_of(lhs.node_state.weights_vector.begin(), lhs.node_state.weights_vector.end(), [](const size_t i) { return i == -1; }),
         rhsbad = any_of(rhs.node_state.weights_vector.begin(), rhs.node_state.weights_vector.end(), [](const size_t i) { return i == -1; });
    if (lhsbad && !rhsbad) return false;
    if (!lhsbad && rhsbad) return true;
     return (accumulate(lhs.node_state.weights_vector.begin(), lhs.node_state.weights_vector.end(), 0) + lhs.best_path) < 
            (accumulate(rhs.node_state.weights_vector.begin(), rhs.node_state.weights_vector.end(), 0) + rhs.best_path);});
  cout << "<<<<< Best path value: " << best_element->best_path << "-----State: ";
  for (auto w : best_element->node_state.weights_vector) cout << w << ", ";
  cout << accumulate(best_element->node_state.weights_vector.begin(), best_element->node_state.weights_vector.end(), 0) << "----->>>>>>\n";
  return best_element->best_path + accumulate(best_element->node_state.weights_vector.begin(), best_element->node_state.weights_vector.end(), 0);
  
};

/// <summary>
/// Reads graph in special format. first line specifies number of vertices, number of edges, and 0/1 for trigger the weighted variant. Then vertex_count lines with the weights of nodes and then edge_count lines containing edge in format source target weight
///  Unweighted variant expects just a first line and then list of edges.
/// </summary>
/// <param name="graph_to_be_dominated">The input graph for Domination problem.</param>
/// <param name="input_stream">Strem with input graph.</param>
/// <returns>1 if the Graph is loaded properly/0 Otherwise</returns>
bool read_input_graph(Graph_t& graph_to_be_dominated, ifstream& input_stream) {
  graph_to_be_dominated.adjacency_matrix.clear();
  if (!input_stream.good()) {
    cerr << "Data loading error.\n";
    return 0;
  }
  size_t vertex_count, edges_count, source, target, dumpster_dive;
  Weight_t weight=1;
  input_stream >> vertex_count >> edges_count >> weight >> dumpster_dive;
  for (size_t i=0; i < vertex_count; ++i) {
    input_stream >> dumpster_dive >> weight;
    graph_to_be_dominated.vertex_weight.push_back(weight);
    graph_to_be_dominated.adjacency_matrix.push_back({});
  }
  for (size_t i=0; i < edges_count; ++i) {
    input_stream >> dumpster_dive >> source >> target >> weight;
    graph_to_be_dominated.add_unoriented_edge(source, target, weight);
  }
  return 1;
}

/// <summary>
/// Structure to manage the restrictions/relaxations 
/// </summary>
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