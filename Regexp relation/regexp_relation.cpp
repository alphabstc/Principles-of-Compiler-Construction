#include <stdio.h>
#include <string.h>
#include <vector>
#include <stack>
#include <map>
#include <set>
#include <utility>
#include <algorithm>
#define EPSILON 26
#define ACTION_SHIFT 0
#define ACTION_REDUCE 1
#define ACTION_ACCEPT 2
#define ACTION_ERROR -1
#define GOTO_ERROR -1
#define LESS_THAN -1
#define MORE_THAN 1
#define EQUAL 0
#define INCOMPARABLE 2
using namespace std;
/*
productions G(S):
(0) S->D
(1) D->D|F
(2) D->F
(3) F->FG
(4) F->G
(5) G->G*
(6) G->G?
(7) G->G+
(8) G->H
(9) H->(D)
(10) H->id 

FIRST(H)={id,(}
FIRST(G)={id,(}
FIRST(F)={id,(}
FIRST(D)={id,(}
FIRST(S)={id,(}
FOLLOW(S)={$}
FOLLOW(D)={$,|,)}
FOLLOW(F)={$,|,),id,(}
FOLLOW(G)={$,|,),id,(,*,?,+}
FOLLOW(H)={$,|,),id,(,*,?,+}

SLR(1)												
	ACTION								GOTO			
	$	|	*	?	+	(	)	id	D	F	G	H
0						s5		s6	1	2	3	4
1	acc	s7										
2	r2	r2				s5	r2	s6			8	4
3	r4	r4	s9	s10	s11	r4	r4	r4				
4	r8	r8	r8	r8	r8	r8	r8	r8				
5						s5		s6	12	2	3	4
6	r10	r10	r10	r10	r10	r10	r10	r10				
7						s5		s6		13	3	4
8	r3	r3	s9	s10	s11	r3	r3	r3				
9	r5	r5	r5	r5	r5	r5	r5	r5				
10	r6	r6	r6	r6	r6	r6	r6	r6				
11	r7	r7	r7	r7	r7	r7	r7	r7				
12		s7					s14					
13	r1	r1				s5	r1	s6			8	4
14	r9	r9	r9	r9	r9	r9	r9	r9				

*/ 
const char productions_left[] = {'S', 'D', 'D', 'F', 'F', 'G', 'G', 'G', 'G', 'H', 'H'};
const int productions_right_length[] = {1, 3, 1, 2, 1, 2, 2, 2, 1, 3, 1};
int T;
char regexp1[1100000], regexp2[1100000];
inline bool isLetter(const char c){
	return c == 'E' || (c >= 'a' && c <= 'z');
}
inline bool isTerminal(const char c){
	return isLetter(c) || c == 0 || c == '|' || c == '*' || c == '?' || c == '+' || c == '(' || c == ')';
}
struct struct_dfa{
private:
	int num, start;
	vector<int> tr[26];
	vector<bool> acc;
public:
	void init(){
		for(int c = 0; c < 26; ++c){
			tr[c].clear();		
		}
		acc.clear();
		start = -1;
		num = 0;		
	}
	struct_dfa(){
		init();
	}
	int makeNewNode(){
		for(int c = 0; c < 26; ++c){
			tr[c].push_back(-1);	
		} 
		acc.push_back(false); 
		return num++;
	}	
	vector<int> allNextStates(vector<int> &v, int s)const{
		vector<int> t;
		for(int c = 0; c < 26; ++c){
			t.push_back(v[tr[c][s]]);
		}
		return t;
	}
	inline void makeNewTransition(int st, int en, int ch){
		tr[ch][st] = en;
	}	
	inline void setStart(int st){
		start = st;
	}	
	inline void setAccept(const vector<bool> & v){
		acc = v;
	}
	inline int getNodesNum(){
		return num;
	}
	void print()const{
		printf("-----------------------------------------\n");
		printf("nodes number: %d\n", num);
		printf("start from: %d\n", start);
		printf("accept states:");
		for(int i = 0; i < num; ++i) if (acc[i]) printf(" %d", i);
		putchar('\n');
		for(int i = 0; i < num; ++i)
			for(int c = 0; c < 26; ++c)
				if (tr[c][i] != -1) printf("%d %c: %d\n", i, c + 'a', tr[c][i]); 
	}
	int relation(const struct_dfa &d)const{
		set<pair<int, int>> se;
		vector<pair<int, int>> v;
		v.push_back(pair<int, int>(start, d.start));
		se.insert(v[0]);
		pair<int, int> pa;
		unsigned int he = 0;
		while (he < v.size()){
			for(int c = 0; c < 26; ++c){
				pa.first = tr[c][v[he].first];
				pa.second = d.tr[c][v[he].second];
				if (pa.first != -1 && pa.second != -1){
					if (se.find(pa) == se.end()){
						v.push_back(pa);
						se.insert(pa);
					}
				}
			}
			++he;
		}
		bool flag1 = 0, flag2 = 0;
		for(const pair<int, int> &pa : v){
			if (acc[pa.first] && !d.acc[pa.second]){
				flag1 = 1;
			}
			if (!acc[pa.first] && d.acc[pa.second]){
				flag2 = 1;
			}		
			if (flag1 && flag2)
				return INCOMPARABLE;	
		}
		if (flag1) return MORE_THAN;
		if (flag2) return LESS_THAN;
		return EQUAL;
	}
	void minimize(){
//		print();
		vector<vector<int> > G;
		G.push_back(vector<int>());
		G.push_back(vector<int>());
		vector<int> v;
		for(int i = 0; i < num; ++i)
			if (acc[i]){
				v.push_back(1);
				G[1].push_back(i);
			}else{
				v.push_back(0);
				G[0].push_back(i);
			}
		acc.clear();
		acc.push_back(false);
		acc.push_back(true);
		while (1){
			vector<int> nv = v;
			bool nochanged = 1;
			int tot = G.size();
			for(int i = 0; i < tot; ++i) if (G[i].size()){
				map<vector<int>, int> ms;
				vector<int> te = G[i];
				G[i].clear();
				ms[allNextStates(v, te[0])] = i;
				G[i].push_back(te[0]);
				for(unsigned int j = 1; j < te.size(); ++j){
					int &x = te[j];
					vector<int> nextS = allNextStates(v, x);
					if (!ms.count(nextS)){
						ms[nextS] = G.size();
						G.push_back(vector<int>());
						acc.push_back(acc[i]);
						nochanged = 0;
					}
					int bel = ms[nextS];
					G[bel].push_back(x);
					nv[x] = bel;
				}
			}
			if (nochanged) break;
			v = nv;
		}
		num = G.size();
		start = v[start];
		vector<int> _tr;
		for(int i = 0; i < num; ++i) _tr.push_back(-1);		
		for(int c = 0; c < 26; ++c){
			for(unsigned int i = 0; i < tr[c].size(); ++i){
				_tr[v[i]] = v[tr[c][i]];
			}
			tr[c] = _tr;
		}
	}
}dfa1, dfa2;
struct struct_nfa{
private:
	int num, start;
	vector<vector<int> > tr[27];
	vector<bool> acc;
public:
	void init(){
		for(int c = 0; c < 27; ++c){
			for(unsigned int i = 0; i < tr[c].size(); ++i){
				tr[c][i].clear();
			}
			tr[c].clear();
		}
		acc.clear();
		start = -1;
		num = 0;		
	}
	struct_nfa(){
		init();
	}
	vector<int> move(const vector<int> &fr, const int ch)const{
		vector<int> v;
		for(int x : fr){
			for(int y : tr[ch][x]){
				v.push_back(y);
			}
		}
		return v;
	}
	vector<int> E_closure(const vector<int> &st)const{
		bool *vis = new bool[num]();
		vector<int> v;
		v = st;
		for(int x : v){
			vis[x] = 1;
		}
		unsigned int he = 0;
		while (he < v.size()){
			for(int y : tr[EPSILON][v[he]]) if (!vis[y]){
				vis[y] = 1;
				v.push_back(y);
			}
			++he;
		}
		delete []vis; 
		sort(v.begin(), v.end());
		return v;
	}	
	void nfa2dfa(struct_dfa &dfa)const{
		dfa.init();
		map<vector<int>, int> ms;
		vector<int> v;
		v.push_back(start);	
		v = E_closure(v);
		ms[v] = dfa.makeNewNode();
		vector<vector<int> > items;
		items.push_back(v);
		int he = 0;	
		while (he < dfa.getNodesNum()){
			for(int c = 0; c < 26; c++){
				v = E_closure(move(items[he], c));	
				if (!ms.count(v)){
					ms[v] = dfa.makeNewNode();
					items.push_back(v);
				}
				dfa.makeNewTransition(he, ms[v], c);
			}
			++he;
		}		
		dfa.setStart(0);
		vector<bool> dfaacc;
		for(unsigned int i = 0; i < items.size(); ++i){
			bool flag = false;
			for(int j = 0; j < num; ++j) if (acc[j]){
				auto it = lower_bound(items[i].begin(), items[i].end(), j);
				if (it != items[i].end()){
					flag = true;
					break;
				}
			} 
			dfaacc.push_back(flag);
		}
		dfa.setAccept(dfaacc);
	}		
	int makeNewNode(){
		for(int c = 0; c < 27; ++c){
			tr[c].push_back(vector<int>());	
		} 
		acc.push_back(false); 
		return num++;
	}
	inline void makeNewTransition(int st, int en, int ch){
		tr[ch][st].push_back(en);
	}
	inline void setStart(int st){
		start = st;
	}
	inline void setAccept(int en){
		for(int i = 0; i < num; ++i)
			acc[i] = false;
		acc[en] = true;
	}
};
int query_action(const int state, const char symbol, int &id){
	if (state == 0 || state == 5 || state == 7){
		if (symbol == '('){
			id = 5;
			return ACTION_SHIFT;
		}
		if (isLetter(symbol)){
			id = 6;
			return ACTION_SHIFT;
		}
	}
	if (state == 1){
		if (symbol == 0){
			id = 0;
			return ACTION_ACCEPT;
		}
		if (symbol == '|'){
			id = 7;
			return ACTION_SHIFT;
		}
	}
	if (state == 2){
		if (symbol == 0 || symbol == '|' || symbol == ')'){
			id = 2;
			return ACTION_REDUCE;
		}
		if (symbol == '('){
			id = 5;
			return ACTION_SHIFT;
		}
		if (isLetter(symbol)){
			id = 6;
			return ACTION_SHIFT;
		}
	}
	if (state == 3){
		if (symbol == 0 || symbol == '|' || symbol == '(' || symbol == ')' || isLetter(symbol)){
			id = 4;
			return ACTION_REDUCE;
		}		
		if (symbol == '*'){
			id = 9;
			return ACTION_SHIFT;
		}
		if (symbol == '?'){
			id = 10;
			return ACTION_SHIFT;
		}
		if (symbol == '+'){
			id = 11;
			return ACTION_SHIFT;
		}		
	}
	if (state == 4){
		if (isTerminal(symbol)){
			id = 8;
			return ACTION_REDUCE;
		}
	}
	if (state == 6){
		if (isTerminal(symbol)){
			id = 10;
			return ACTION_REDUCE;
		}			
	}
	if (state == 8){
		if (symbol == 0 || symbol == '|' || symbol == '(' || symbol == ')' || isLetter(symbol)){
			id = 3;
			return ACTION_REDUCE;
		}		
		if (symbol == '*'){
			id = 9;
			return ACTION_SHIFT;
		}
		if (symbol == '?'){
			id = 10;
			return ACTION_SHIFT;
		}
		if (symbol == '+'){
			id = 11;
			return ACTION_SHIFT;
		}		
	}
	if (state == 9){
		if (isTerminal(symbol)){
			id = 5;
			return ACTION_REDUCE;
		}				
	}
	if (state == 10){
		if (isTerminal(symbol)){
			id = 6;
			return ACTION_REDUCE;
		}			
	}
	if (state == 11){
		if (isTerminal(symbol)){
			id = 7;
			return ACTION_REDUCE;
		}			
	}
	if (state == 12){
		if (symbol == '|'){
			id = 7;
			return ACTION_SHIFT;
		}
		if (symbol == ')'){
			id = 14;
			return ACTION_SHIFT;
		}
	}
	if (state == 13){
		if (symbol == 0 || symbol == '|' || symbol == ')'){
			id = 1;
			return ACTION_REDUCE;
		}
		if (symbol == '('){
			id = 5;
			return ACTION_SHIFT;
		}
		if (isLetter(symbol)){
			id = 6;
			return ACTION_SHIFT;
		}		
	}
	if (state == 14){
		if (isTerminal(symbol)){
			id = 9;
			return ACTION_REDUCE;
		}			
	}
	return ACTION_ERROR; 
}
int query_goto(int state, char symbol){
	if (state == 0){
		switch(symbol){
			case 'D': return 1;
			case 'F': return 2;
			case 'G': return 3;
			case 'H': return 4;
			default: return GOTO_ERROR;
		}
	}
	if (state == 2 || state == 13){
		switch(symbol){
			case 'G': return 8;
			case 'H': return 4;
			default: return GOTO_ERROR;
		}
	}
	if (state == 5){
		switch(symbol){
			case 'D': return 12;
			case 'F': return 2;
			case 'G': return 3;
			case 'H': return 4;
			default: return GOTO_ERROR;
		}		
	}
	if (state == 7){
		switch(symbol){
			case 'F': return 13;
			case 'G': return 3;
			case 'H': return 4;
			default: return GOTO_ERROR;
		}				
	}
	return GOTO_ERROR;
}
void semantic_rules(const int id, struct_nfa &nfa, stack<pair<int, int> > &attributes, stack<char> &symbols){
	if (id == 1){
		pair<int, int> pa2 = attributes.top();
		attributes.pop();
		attributes.pop();
		pair<int, int> pa1 = attributes.top();
		attributes.pop();
		int st = nfa.makeNewNode();
		int en = nfa.makeNewNode();
		nfa.makeNewTransition(st, pa1.first, EPSILON);
		nfa.makeNewTransition(st, pa2.first, EPSILON);
		nfa.makeNewTransition(pa1.second, en, EPSILON);
		nfa.makeNewTransition(pa2.second, en, EPSILON);
		attributes.push(pair<int, int>(st, en));
	}else if (id == 3){
		pair<int, int> pa2 = attributes.top();
		attributes.pop();
		pair<int, int> pa1 = attributes.top();
		attributes.pop();
		nfa.makeNewTransition(pa1.second, pa2.first, EPSILON);
		attributes.push(pair<int, int>(pa1.first, pa2.second));
	}else if (id == 5){
		attributes.pop();
		pair<int, int> pa = attributes.top();
		attributes.pop();	
		int st = nfa.makeNewNode();
		int en = nfa.makeNewNode();
		nfa.makeNewTransition(st, pa.first, EPSILON);
		nfa.makeNewTransition(pa.second, en, EPSILON);
		nfa.makeNewTransition(pa.second, pa.first, EPSILON);
		nfa.makeNewTransition(st, en, EPSILON);
		attributes.push(pair<int, int>(st, en));
	}else if (id == 6){
		attributes.pop();
		pair<int, int> pa = attributes.top();
		attributes.pop();		
		nfa.makeNewTransition(pa.first, pa.second, EPSILON);
		attributes.push(pa);
	}else if (id == 7){
		attributes.pop();
		pair<int, int> pa = attributes.top();
		attributes.pop();		
		int st = nfa.makeNewNode();
		int en = nfa.makeNewNode();
		nfa.makeNewTransition(st, pa.first, EPSILON);
		nfa.makeNewTransition(pa.second, en, EPSILON);
		nfa.makeNewTransition(pa.second, pa.first, EPSILON);
		attributes.push(pair<int, int>(st, en));
	}else if (id == 9){
		attributes.pop();
		pair<int, int> pa = attributes.top();
		attributes.pop();
		attributes.pop();
		attributes.push(pa);
	}else if (id == 10){
		attributes.pop();
		int st = nfa.makeNewNode();
		int en = nfa.makeNewNode();
		char ch = symbols.top();
		nfa.makeNewTransition(st, en, ch == 'E' ? EPSILON : ch - 'a');
		attributes.push(pair<int, int>(st, en));
	};
}
bool regexp2dfa(const char* reg, struct_dfa &dfa){
	struct_nfa nfa;
	stack<int> states;
	states.push(0);
	stack<char> symbols;
	stack<pair<int, int> > attributes;
	int now = 0;
	while (1){
		int sta = states.top();
		int id;
		int action = query_action(sta, reg[now], id);
		if (action == ACTION_SHIFT){
			states.push(id);
			symbols.push(reg[now++]);
			attributes.push(pair<int, int>());
		}else if (action == ACTION_REDUCE){
			semantic_rules(id, nfa, attributes, symbols); 
			for(int i = 0; i < productions_right_length[id]; ++i){
				states.pop();
				symbols.pop();
			}
			sta = states.top();
			sta = query_goto(sta, productions_left[id]);
			if (sta == GOTO_ERROR){
				printf("regexp2dfa(%s): SYNTAX ERROR!\n", reg);
				return 1;
			}
			states.push(sta);
			symbols.push(productions_left[id]);
		}else if (action == ACTION_ACCEPT){ 
			break;
		}else{
			printf("regexp2dfa(%s): SYNTAX ERROR!\n", reg);
			return 1;
		}
	}
	pair<int, int> pa = attributes.top();
	nfa.setStart(pa.first);
	nfa.setAccept(pa.second);
	nfa.nfa2dfa(dfa);
	dfa.minimize(); 
	return 0;
}
int main(){
	scanf("%d", &T);
	while (T--){
		scanf("%s%s", regexp1, regexp2);
		if (!regexp2dfa(regexp1, dfa1)&&!regexp2dfa(regexp2, dfa2)){
//			dfa1.print();
//			dfa2.print();
			int re = dfa1.relation(dfa2);
			switch(re){
				case INCOMPARABLE: printf("!\n");break;
				case EQUAL: printf("=\n");break;
				case LESS_THAN: printf("<\n");break;
				case MORE_THAN: printf(">\n");break;
			}
		}
	}
	return 0;
}
