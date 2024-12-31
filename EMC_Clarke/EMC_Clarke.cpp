#include <algorithm>
#include <cstdio>
#include <fstream>
#include <iostream>
#include <iterator>
#include <map>
#include <queue>
#include <set>
#include <sstream>
#include <stack>
#include <string>
#include <unordered_map>
#include <vector>

using namespace std;

int V, E;   // V for num of vertex, E for num for edges;
int props;  // props for num of props;
vector<int> fairset;
vector<int> set_Q;
int num_fairset;     // fairset中元素个数；
vector<int> v[105];  //存储边信息； 通过v[pre].push_back(suc)存储;
vector<int> father[105];       // 存储前驱节点；
stack<int> stk;                //存储强连通分量；
vector<vector<int>> scc;       //将栈换成vector存储强连通分量；
vector<vector<string>> state;  //存储状态的属性值；
int DFN[105], LOW[105];        // tarjan算法使用
int index_tarjan;              // tarjan算法使用
bool vis[105];                 // tarjan算法使用
vector<vector<int>>
graph;  // graph is used to store label status of every state

// expression is the original CTL formula
string origin_expression;
// expressions are the subformulas
vector<string> sub_expressions;
// subformula_index is the index for generated subformulas
map<string, vector<int>> subformula_index;
// SCC shows whether the state is labelled with Q
vector<set<int>> subformula_level;
// highest level of formula
int highest_level = 1;

class ExpressionParser {
public:
    static string preprocess(string expression) {
        return convert(rmspace(expression));
    };

private:
    static string rmspace(string expre) {
        int pos;
        pos = expre.find(" ");
        while (pos != -1) {
            expre.replace(pos, string(" ").length(), "");
            pos = expre.find(" ");
        }
        return expre;
    }

private:
    static string convert(string expre) {
        string inner = "";
        if (expre.substr(0, 3) == "NOT") {
            inner = expre.substr(4, expre.length() - 5);
            return expre.substr(0, 3) + "(" + convert(inner) + ")";
        }
        if (expre.substr(0, 3) == "AND") {
            string s = expre.substr(3, expre.length() - 2);
            vector<string> ss = getSubExpression(s);
            return expre.substr(0, 3) + "(" + convert(ss[0]) + ")" + "(" +
                convert(ss[1]) + ")";
        }
        if (expre.substr(0, 3) == "IMP") {
            string s = expre.substr(3, expre.length() - 2);
            vector<string> ss = getSubExpression(s);
            return "OR(NOT(" + convert(ss[0]) + "))" + "(" + convert(ss[1]) +
                ")";
        }
        string prefix = expre.substr(0, 2);
        if (prefix == "AF") {
            inner = expre.substr(3, expre.length() - 4);
            return "AU(TURE)(" + convert(inner) + ")";
        }
        else if (prefix == "EF") {
            inner = expre.substr(3, expre.length() - 4);
            return "EU(TRUE)(" + convert(inner) + ")";
        }
        else if (prefix == "AG") {
            inner = expre.substr(3, expre.length() - 4);
            return "NOT(EU(TRUE)(NOT(" + convert(inner) + ")))";
        }
        else if (prefix == "EG") {
            inner = expre.substr(3, expre.length() - 4);
            return "NOT(AU(TRUE)(NOT(" + convert(inner) + ")))";
        }
        else if (prefix == "EX" || prefix == "AX") {
            inner = expre.substr(3, expre.length() - 4);
            return prefix + "(" + convert(inner) + ")";
        }
        else if (prefix == "EU" || prefix == "AU" || prefix == "OR") {
            string s = expre.substr(2, expre.length() - 2);
            vector<string> ss = getSubExpression(s);
            return prefix + "(" + convert(ss[0]) + ")" + "(" + convert(ss[1]) +
                ")";
        }
        else {
            return expre;
        }
    }

private:
    static int indexOf(vector<string>& ss, string& s) {
        int i;
        for (i = 0; i < ss.size(); i++) {
            if (ss[i] == s) return i;
        }
        return -1;
    }

public:
    static void compute_subformula_number(
        vector<string>& expressions,
        map<string, vector<int>>& subformula_number, string& expression) {
        if (expression.substr(0, 3) == "NOT") {
            string s = expression.substr(4, expression.length() - 5);
            int number = indexOf(expressions, s);
            vector<int> a;
            a.push_back(number);
            subformula_number[expression] = a;
            compute_subformula_number(expressions, subformula_number, s);
        }
        else if (expression.substr(0, 2) == "AX" ||
            expression.substr(0, 2) == "EX") {
            string s = expression.substr(3, expression.length() - 4);
            int number = indexOf(expressions, s);
            vector<int> a;
            a.push_back(number);
            subformula_number[expression] = a;
            compute_subformula_number(expressions, subformula_number, s);
        }
        else if (expression.substr(0, 3) == "AND") {
            string s = expression.substr(3, expression.length() - 3);
            vector<string> ss = getSubExpression(s);
            int index1 = indexOf(expressions, ss[0]);
            int index2 = indexOf(expressions, ss[1]);
            vector<int> a;
            a.push_back(index1);
            a.push_back(index2);
            subformula_number[expression] = a;
            //            cout<<ss.get(0)<<endl;
            //            cout<<ss.get(1)<<endl;
            compute_subformula_number(expressions, subformula_number, ss[0]);
            compute_subformula_number(expressions, subformula_number, ss[1]);
        }
        else if (expression.substr(0, 2) == "OR" ||
            expression.substr(0, 2) == "AU" ||
            expression.substr(0, 2) == "EU") {
            string s = expression.substr(2, expression.length() - 2);
            vector<string> ss = getSubExpression(s);
            int index1 = indexOf(expressions, ss[0]);
            int index2 = indexOf(expressions, ss[1]);
            vector<int> a;
            a.push_back(index1);
            a.push_back(index2);
            subformula_number[expression] = a;
            //            cout<<ss.get(0)<<endl;
            //            cout<<ss.get(1)<<endl;
            compute_subformula_number(expressions, subformula_number, ss[0]);
            compute_subformula_number(expressions, subformula_number, ss[1]);
        }
        else {
            vector<int> a;
            a.push_back(-1);
            subformula_number[expression] = a;
        }
    }

public:
    static void parseExpression(vector<string>& expressions, string& expression,
        int current_level) {
        expressions.push_back(expression);
        subformula_level.resize(current_level);
        int current_index = expressions.size() - 1;
        if (expression.substr(0, 3) == "NOT") {
            string s = expression.substr(4, expression.length() - 5);
            highest_level = current_level + 1;
            parseExpression(expressions, s, highest_level);
        }
        else if (expression.substr(0, 2) == "AX" ||
            expression.substr(0, 2) == "EX") {
            string s = expression.substr(3, expression.length() - 4);
            highest_level = current_level + 1;
            parseExpression(expressions, s, highest_level);
        }
        else if (expression.substr(0, 3) == "AND") {
            string s = expression.substr(3, expression.length() - 3);
            vector<string> ss = getSubExpression(s);
            highest_level = current_level + 1;
            parseExpression(expressions, ss[0], highest_level);
            parseExpression(expressions, ss[1], highest_level);
        }
        else if (expression.substr(0, 2) == "OR" ||
            expression.substr(0, 2) == "AU" ||
            expression.substr(0, 2) == "EU") {
            string s = expression.substr(2, expression.length() - 2);
            vector<string> ss = getSubExpression(s);
            highest_level = current_level + 1;
            parseExpression(expressions, ss[0], highest_level);
            parseExpression(expressions, ss[1], highest_level);
        }
        else {
            subformula_level[0].insert(current_index);
            return;
        }
        subformula_level[highest_level - current_level].insert(current_index);
    }

public:
    static vector<string> getSubExpression(string& s) {
        int index = 0;
        int cnt = 0;
        // cnt++;
        // index++;
        while (index < s.length()) {
            if (s[index] == '(') {
                cnt++;
            }
            else if (s[index] == ')') {
                cnt--;
            }
            if (cnt == 0) {
                break;
            }
            index++;
        }
        vector<string> result;
        result.push_back(s.substr(1, index - 1));  // from 1 to index-1
        result.push_back(s.substr(
            index + 2,
            s.length() - index - 3));  // from index+2 to s.length()-1-1

        return result;
    }

public:
    void f(string& expression, vector<string>& expressions,
        map<string, vector<int>>& subformula_index) {
        expression = preprocess(expression);
        cout << expression << endl;
        parseExpression(expressions, expression, highest_level);
        compute_subformula_number(expressions, subformula_index, expression);
        cout << "expressions:" << endl;
        int i = 0;
        for (i = 0; i < expressions.size(); i++) {
            cout << expressions[i] << ":" << i << endl;
        }

        map<string, vector<int>>::iterator iter;
        cout << "subformula_index: " << endl;
        for (iter = subformula_index.begin(); iter != subformula_index.end();
            iter++) {
            cout << iter->first << " : ";
            int i = 0;
            vector<int> t = iter->second;
            for (i = 0; i < t.size(); i++) {
                cout << t[i] << "  ";
            }
            cout << endl;
        }
    }
};

/******************读入输入文件************************************************/
void file_input() {
    ifstream myfile("D:\\VisualStudio_Workspace\\EMC_Clarke\\EMC_Clarke\\TestModel6.txt");  //读入输入文件;
    // string temp,temp1;
    bool flag = true;
    // int num_v, num_e;
    if (!myfile.is_open()) {
        cout << "未能成功打开文件" << endl;
    }
    while (!myfile.eof())  // 若未到文件结束一直循环
    {
        if (flag) {
            flag = false;
            myfile >> V >> E;
        }
        //*********************循环读入边******************************/
        for (int i = 0; i < E; i++) {
            int pre, suc;  // pre for 前驱节点predecessor，suc for
                           // 后继节点successor；
            myfile >> pre >> suc;
            v[pre].push_back(suc);
            father[suc].push_back(pre);
        }
        /**************************************************************/

        //*********************读入 fair_set ***************************/
        myfile >> num_fairset;
        int tmp;
        for (int i = 0; i < num_fairset; ++i) {
            myfile >> tmp;
            fairset.push_back(tmp);
        }
        /*************************************************************/

        /********** Read CTL formula ****************/
        myfile >> origin_expression;

        /**********************读取状态信息，使用二维vector
         * 存储；***************************/
        myfile >> props;
        string lineStr;
        // vector<vector<string>> strArray;
        // int num_state = 0;
        while (getline(myfile, lineStr)) {
            // 打印整行字符串
            // cout << lineStr << endl;
            // 存成二维表结构
            stringstream ss(lineStr);
            string str;
            vector<string> lineArray;
            // 按照逗号分隔
            while (getline(ss, str, ',')) lineArray.push_back(str);
            state.push_back(lineArray);
            // num_state++;
        }

        for (int j = 1; j < state.size(); j++) {
            cout << "This is properties of state" << j - 1 << ": " << endl;
            for (int k = 0; k < state[j].size(); k++) {
                cout << state[j][k] << " ";
            }
            cout << endl;
        }

    }
    myfile.close();
}
/*********************************************************************************************************/

//*****************************计算强连通分量（用栈存储）*************************************************/
void TarJan(int u) {
    // int index;
    DFN[u] = LOW[u] = ++index_tarjan;
    stk.push(u);
    vis[u] = true;
    for (int w : v[u]) {
        if (!DFN[w]) {
            TarJan(w);
            LOW[u] = min(LOW[u], LOW[w]);
        }
        else if (vis[w])
            LOW[u] = min(LOW[u], DFN[w]);
    }

    if (DFN[u] == LOW[u]) {
        int s;
        vector<int> tmp;
        do {
            s = stk.top();
            if (!stk.empty()) tmp.push_back(s);
            stk.pop();
            // cout << s << " ";
            vis[s] = false;
        } while (u != s);
        scc.push_back(tmp);  //求强连通分量，转换为vector;
        tmp.clear();
        // cout << endl;
    }
}
//************************************打印出scc;******************************************************/
void Tarjan_Scc() {
    cout << "Here is SCC:" << endl;
    for (int i = 0; i < V; ++i) {
        if (!DFN[i]) {
            TarJan(i);
        }
    }
    for (int j = 0; j < scc.size(); j++) {
        for (int k = 0; k < scc[j].size(); k++) {
            cout << scc[j][k] << " ";
        }
        cout << endl;
    }
}

// **************************************比较scc中是否含有子集包含f中的所有状态,并返回
vector<int> scc_flag(vector<int>& fairset, vector<vector<int>>& scc) {
    vector<int> res;
    for (int i = 0; i < scc.size(); i++) {
        int flag = 0;
        unordered_map<int, int> mp;
        int nums = 0;
        for (int j = 0; j < scc[i].size(); j++) {
            if (mp.find(scc[i][j]) == mp.end())
                mp[scc[i][j]] = 1;
            else
                continue;
        }
        for (int k = 0; k < fairset.size(); k++) {
            if (mp.find(fairset[k]) == mp.end()) {
                flag = 1;
                break;
            }
            else
                continue;
        }
        //如果该行能够包含f中的所有状态，那么就把下标存入res中；
        if (flag == 0) return scc[i];
    }

    return res;
}

//****************************查找节点的前驱；用于标记Q;***************************************************/
vector<int> Find_Fathers(
    vector<int>& v1) {  // v1是scc_flag函数的返回的数组结果；
    queue<int> qe;
    unordered_map<int, int> mp;
    for (int i = 0; i < v1.size(); i++) {
        int now = v1[i];
        // vector<int> now_fa = father[now];
        qe.push(v1[i]);
        mp[v1[i]] = 1;
    }
    while (!qe.empty()) {
        int now = qe.front();
        vector<int> now_fa = father[now];
        qe.pop();
        for (int m : now_fa) {
            if (mp.find(m) != mp.end())
                continue;
            else {
                v1.push_back(m);
                mp[m] = 1;
            }
        }
    }
    return v1;
}

// s1 is the subformula vector, s2 is a formula, findstr will return the s1's
// index of s2
int findstr(vector<string> s1, string s2) {
    for (int i = 0; i < s1.size(); i++) {
        if (s1[i] == s2) {
            return i;
        }
        else {
            continue;
        }
    }
    return -1;
}

// check 'A | B' for S0, S0 is state, 'A | B' is label
void add_label(int s, int label) { graph[s][label] = 1; }

// check 'A | B' for S0, S0 is state, 'A | B' is label
bool labelled(int s, int label) {
    if (graph[s][label] == 1) {
        return true;
    }
    else {
        return false;
    }
}

// NOT p, prop_1 is p, fi is 'NOT p'
void NOT(int prop_1, int fi) {
    for (int& n : set_Q) {
        if (!labelled(n, prop_1)) {
            add_label(n, fi);
        }
    }
}

// AX p, prop_1 is p, fi is 'AX p'
void AX(int prop_1, int fi) {
    for (int& n : set_Q) {
        for (int son : v[n]) {
            if (!labelled(son, prop_1)) {
                break;
            }
            add_label(n, fi);
        }
    }
}

// EX p, prop_1 is p, fi is 'EX p'
void EX(int prop_1, int fi) {
    for (int& n : set_Q) {
        for (int son : v[n]) {
            if (labelled(son, prop_1)) {
                add_label(n, fi);
                break;
            }
        }
    }
}

// p | q, prop_1 is p, prop_2 is q, fi is 'p | q'
void OR(int prop_1, int prop_2, int fi) {
    for (int& n : set_Q) {
        if (labelled(n, prop_1) || labelled(n, prop_2)) {
            add_label(n, fi);
        }
    }
}

// p & q, prop_1 is p, prop_2 is q, fi is 'p & q'
void AND(int prop_1, int prop_2, int fi) {
    for (int& n : set_Q) {
        if (labelled(n, prop_1) && labelled(n, prop_2)) {
            add_label(n, fi);
        }
    }
}

// A (p U q), n is current state, prop_1 is p, prop_2 is q, fi is 'A (p U q),
// visited from AU
bool DFS_AU(int n, int prop_1, int prop_2, int fi, map<int, bool> visited) {
    if (visited[n]) {
        return labelled(n, fi);
    }
    visited[n] = true;
    if (labelled(n, prop_2)) {
        add_label(n, fi);
        return true;
    }
    else if (!labelled(n, prop_1)) {
        return false;
    }
    for (int n1 : v[n]) {
        if (!DFS_AU(n1, prop_1, prop_2, fi, visited)) {
            return false;
        }
    }
    add_label(n, fi);
    return true;
}

// use findEUSet to find a set could be labelled with E (p U q), prop_1 is p, fi
// is 'E (p U q)'
set<int> findEUSet(int prop_1, int fi) {
    set<int> EUSet;
    for (int& n : set_Q) {
        if (labelled(n, prop_1)) {
            for (int son : v[n]) {
                if (labelled(son, fi)) {
                    EUSet.insert(n);
                    break;
                }
            }
        }
    }
    return EUSet;
}

// E (p U q), prop_1 is p, prop_2 is q, fi is 'E (p U q)'
void EU(int prop_1, int prop_2, int fi) {
    set<int> EUSet1, EUSet2;
    for (int& n : set_Q) {
        if (labelled(n, prop_2)) {
            add_label(n, fi);
        }
    }
    EUSet1 = findEUSet(prop_1, fi);
    while (EUSet1 != EUSet2) {
        EUSet2 = EUSet1;
        for (int i : EUSet1) {
            add_label(i, fi);
        }
        EUSet1 = findEUSet(prop_1, fi);
    }
}

// A (p U q), prop_1 is p, prop_2 is q, fi is 'A (p U q)'
void AU(int prop_1, int prop_2, int fi) {
    map<int, bool> visited;
    for (int& n : set_Q) {
        visited.insert(map<int, bool>::value_type(n, false));
    }
    for (int& n : set_Q) {
        if (!visited[n]) {
            DFS_AU(n, prop_1, prop_2, fi, visited);
        }
    }
}

// For atom props, use ATOM to label them, including 'TRUE'
void ATOM(int fi) {
    string s = sub_expressions[fi];
    if (s == "TRUE") {
        for (int& i : set_Q) {
            graph[i][fi] = 1;
        }
        return;
    }
    for (int& i : set_Q) {
        auto it = find(state[i + 1].begin(), state[i + 1].end(), s);
        if (it == state[i + 1].end()) {//加了判断；之前直接读的话，在mfvc编译器里，会因为读取到end而报错
            graph[i][fi] = 0;
        }
        else if (*it == s) {
            graph[i][fi] = 1;
        }
        else {
            graph[i][fi] = 0;
        }
    }
}

void opToFunc(int fi) {
    string s = sub_expressions[fi];
    auto iter = subformula_index.find(s);
    vector<int> t = iter->second;
    if (s.substr(0, 3) == "NOT") {
        NOT(t[0], fi);
    }
    else if (s.substr(0, 2) == "AX") {
        AX(t[0], fi);
    }
    else if (s.substr(0, 2) == "EX") {
        EX(t[0], fi);
    }
    else if (s.substr(0, 3) == "AND") {
        AND(t[0], t[1], fi);
    }
    else if (s.substr(0, 2) == "OR") {
        OR(t[0], t[1], fi);
    }
    else if (s.substr(0, 2) == "AU") {
        AU(t[0], t[1], fi);
    }
    else if (s.substr(0, 2) == "EU") {
        EU(t[0], t[1], fi);
    }
    else {
        ATOM(fi);
    }
}

void label_graph(vector<vector<int>> n, int fi) {
    for (auto level : subformula_level) {
        for (int subfi : level) {
            opToFunc(subfi);
        }
    }
}

void finish_check(vector<vector<int>> n, vector<int> q_label, int flag) {
    bool result = true;
    if (flag == 0) {
        for (int i = 0; i < V; i++) {
            if (n[i][0] == 1) {
                continue;
            }
            else {
                result = false;
                cout << i << " ";
            }
        }
    }
    else {
        for (int& it : q_label) {
            if (n[it][0] == 1) {
                continue;
            }
            else {
                result = false;
                cout << it << " ";
            }
        }
    }
    cout << endl;
    cout << (result ? "The CTL formula is TRUE" : "The CTL formula is FALSE")
        << endl;
}

int main() {
    file_input();
    Tarjan_Scc();
    vector<int> fair_scc = scc_flag(fairset, scc);
    // set_Q stores all states with Q labelled

    // cout << "I am here after call the fair_scc" << endl;
    if (!fair_scc.empty()) {
        cout << "This is fair&scc:" << endl;
        for (int i = 0; i < fair_scc.size(); i++) {
            cout << fair_scc[i] << " ";
        }
        cout << endl;
        set_Q = Find_Fathers(fair_scc);
        cout << "This is set_Q:" << endl;
        for (int i = 0; i < set_Q.size(); i++) {
            cout << set_Q[i] << " ";
        }
        cout << endl;
    }
    else
        cout << "无需要标号Q的状态!" << endl;

    if (num_fairset == 0) {
        set_Q.clear();
        for (int i = 0; i < V; i++) {
            set_Q.push_back(i);
        }
    }

    ExpressionParser ep;
    ep.f(origin_expression, sub_expressions, subformula_index);

    // resize label graph according to the num of states and sub-formulas
    graph.resize(V);
    for (int i = 0; i < V; i++) graph[i].resize(sub_expressions.size());

    // start to label state in graph with the very first CTL formula
    label_graph(graph, 0);

    // print CTL check status
    finish_check(graph, set_Q, num_fairset);

    return 0;
}
