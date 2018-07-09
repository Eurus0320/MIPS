#include <memory>
#include <fstream>
#include <cstdio>
#include <iostream>
#include <string>
#include <cstring>
#include <vector>
#include <map>
using namespace std;

const int MAXN = 1e6 + 5;
const int MAXL = 505;

int reg[34];
int heap_top = 0, ins_top = 0;
char mem[MAXN];
map<string, int> text_label, data_label;

const string REG_STR[] = {"$0", "$1", "$2", "$3", "$4", "$5", "$6", "$7", "$8", "$9", "$10", "$11", "$12", "$13", "$14", "$15", "$16", "$17", "$18", "$19", "$20", "$21", "$22", "$23", "$24", "$25", "$26", "$27", "$28", "$29", "$30", "$31", "$lo", "$hi"};
const string REG_NUM[] = {"$zero", "$at", "$v0", "$v1", "$a0", "$a1", "$a2", "$a3", "$t0", "$t1", "$t2", "$t3", "$t4", "$t5", "$t6", "$t7", "$s0", "$s1", "$s2", "$s3", "$s4", "$s5", "$s6", "$s7", "$t8", "$t9", "$k0", "$k1", "$gp", "$sp", "$fp", "$ra", "$lo", "$hi"};

int string_to_int(string str) {
	int num = 0;
	int l = str.length(), i = 0;
	bool flag = false;
	while (i < l && (str[i] < '0' || str[i] > '9')) flag = str[i] == '-', ++i;
	while (i < l && (str[i] >= '0'  && str[i] <= '9'))
		num *= 10, num += str[i++] - '0';
	if (flag) num = -num;
	return num;
}

int string_to_reg(string str) {
	if (str.empty()) return -1;
	if (str.back() == ',') str.pop_back();
	for (int i = 0; i < 34; ++i)
        if (str == REG_STR[i] || str == REG_NUM[i]) return i;
	return -1;
}
int power(int n) {
	int result = 1;
	while (n--) result <<= 1;
	return result;
}
string get_phrase(char *str, int &i, int l) {
	string result = "";
	while (i < l && str[i] != ' ') result += str[i++];
	return result;
}
string get_str(char *str, int &i, int l) {
	string result = "";
	while (i < l) {
		result += str[i++];
		if (result.back() == '\\') {
			char ch = str[i++], real = '\0';
			switch (ch) {
			case 'n': real = '\n'; break;
			case 'r': real = '\r'; break;
			case 't': real = '\t'; break;
			case '\\': real = '\\'; break;
			case '\'': real = '\''; break;
			case '\"': real = '\"'; break;
			case '0': real = '\0'; break;
			}
			result.back() = real;
		}
	}
	return result;
}
void shut_down(int val);


class instruction {
public:
	vector<int> reg_to_read, reg_to_write;
	int type_of_jump;
	bool write_to_mem;

	instruction() : type_of_jump(0), write_to_mem(false) {
		reg_to_read.clear();
		reg_to_write.clear();
	}

	virtual void ID() {}
	virtual void EX() {}
	virtual void MEM() {}
	virtual void WB() {}
	virtual ~instruction() {}
};
vector<instruction*> ins_vec;
instruction *plat[5];

class calculation : public instruction {
public:
	int rdest, rsrc1, rsrc2;
	int num1, num2, result;

	calculation(const string &_rdest, const string &_rsrc1, const string &_rsrc2) : instruction() {
		rdest = string_to_reg(_rdest);
		reg_to_write.push_back(rdest);
		rsrc1 = string_to_reg(_rsrc1);
		rsrc2 = string_to_reg(_rsrc2);
		if (rsrc1 == -1) num1 = string_to_int(_rsrc1);
		else reg_to_read.push_back(rsrc1);
		if (rsrc2 == -1) num2 = string_to_int(_rsrc2);
		else reg_to_read.push_back(rsrc2);
	}
	virtual instruction* copy() { return new calculation(*this); }
	virtual void ID() {
		if (rsrc1 != -1) num1 = reg[rsrc1];
		if (rsrc2 != -1) num2 = reg[rsrc2];
	}
	virtual void WB() { reg[rdest] = result; }
};
class add : public calculation { // & addu, addiu
public:
	bool unsign;

	add(const string &_num1, const string &_num2, const string &_num3, bool _unsign) : calculation(_num1, _num2, _num3), unsign(_unsign) {}
	virtual instruction* copy() { return new add(*this); }
	virtual void EX() { result = num1 + num2; }
};
class sub : public calculation { // & subu
public:
	bool unsign;

	sub(const string &_num1, const string &_num2, const string &_num3, bool _unsign) : calculation(_num1, _num2, _num3), unsign(_unsign) {}
	virtual instruction* copy() { return new sub(*this); }
	virtual void EX() { result = num1 - num2; }
};
class mul : public calculation {
public:
	int para;
	bool unsign;
	long long llres;

	mul(const string &_num1, const string &_num2, const string &_num3, bool _unsign) : calculation(_num1, _num2, _num3), para(_num3 == "" ? 2 : 3), unsign(_unsign) {
		if (para == 2) {
			reg_to_write.push_back(32);
			reg_to_write.push_back(33);
		}
	}
	virtual instruction* copy() { return new mul(*this); }
	virtual void ID() {
		if (para == 2) {
			num2 = num1;
			num1 = reg[rdest];
			if (rsrc1 != -1) num2 = reg[rsrc1];
		}
		else {
			if (rsrc1 != -1) num1 = reg[rsrc1];
			if (rsrc2 != -1) num2 = reg[rsrc2];
		}
	}
	virtual void EX() { // confusing...
		if (unsign) llres = (unsigned long long)1 * (unsigned int)(num1) * (unsigned int)(num2);
		else llres = 1LL * num1 * num2;
	}
	virtual void WB() {
		if (para == 3) reg[rdest] = llres;
		else {
			reg[32] = llres; // lo
			reg[33] = (llres >> 32); // hi
		}
	}
};
class Div : public calculation { // & __divu
public:
	int para, q, r;
	bool unsign;

	Div(const string &_num1, const string &_num2, const string &_num3, bool _unsign) : calculation(_num1, _num2, _num3), para(_num3 == "" ? 2 : 3), unsign(_unsign) {
		if (para == 2) {
			reg_to_write.push_back(32);
			reg_to_write.push_back(33);
		}
	}
	virtual instruction* copy() { return new Div(*this); }
	virtual void ID() {
		if (para == 2) {
			num2 = num1;
			num1 = reg[rdest];
			if (rsrc1 != -1) num2 = reg[rsrc1];
		}
		else {
			if (rsrc1 != -1) num1 = reg[rsrc1];
			if (rsrc2 != -1) num2 = reg[rsrc2];
		}
	}
	virtual void EX() {
		if (unsign) q = (unsigned int)(num1) / (unsigned int)(num2);
		else q = num1 / num2;
		if (unsign) r = (unsigned int)(num1) % (unsigned int)(num2);
		else r = num1 % num2;
	}
	virtual void WB() {
		if (para == 3) reg[rdest] = q;
		else {
			reg[32] = q;
			reg[33] = r;
		}
	}
};
class Xor : public calculation { // & __xoru
public:
	bool unsign;

	Xor(const string &_num1, const string &_num2, const string &_num3, bool _unsign) : calculation(_num1, _num2, _num3), unsign(_unsign) {}
	virtual instruction* copy() { return new Xor(*this); }
	virtual void EX() { result = num1 ^ num2; }
};
class neg : public calculation { // & negu
public:
	bool unsign;

	neg(const string &_num1, const string &_num2, bool _unsign) : calculation(_num1, _num2, ""), unsign(_unsign) {}
	virtual instruction* copy() { return new neg(*this); }
	virtual void EX() { result = -num1; }
};
class rem : public calculation { // & remu
public:
	bool unsign;

	rem(const string &_num1, const string &_num2, const string &_num3, bool _unsign) : calculation(_num1, _num2, _num3), unsign(_unsign) {}
	virtual instruction* copy() { return new rem(*this); }
	virtual void EX() {
		if (unsign) result = (unsigned int)num1 % (unsigned int)num2;
		else result = num1 % num2;
	}
};
class seq : public calculation {
public:
	seq(const string &_num1, const string &_num2, const string &_num3) : calculation(_num1, _num2, _num3) {}
	virtual instruction* copy() { return new seq(*this); }
	virtual void EX() { result = num1 == num2; }
};
class sge : public calculation {
public:
	sge(const string &_num1, const string &_num2, const string &_num3) : calculation(_num1, _num2, _num3) {}
	virtual instruction* copy() { return new sge(*this); }
	virtual void EX() { result = num1 >= num2; }
};
class sgt : public calculation {
public:
	sgt(const string &_num1, const string &_num2, const string &_num3) : calculation(_num1, _num2, _num3) {}
	virtual instruction* copy() { return new sgt(*this); }
	virtual void EX() { result = num1 > num2; }
};
class sle : public calculation {
public:
	sle(const string &_num1, const string &_num2, const string &_num3) : calculation(_num1, _num2, _num3) {}
	virtual instruction* copy() { return new sle(*this); }
	virtual void EX() { result = num1 <= num2; }
};
class slt : public calculation {
public:
	slt(const string &_num1, const string &_num2, const string &_num3) : calculation(_num1, _num2, _num3) {}
	virtual instruction* copy() { return new slt(*this); }
	virtual void EX() { result = num1 < num2; }
};
class sne : public calculation {
public:
	sne(const string &_num1, const string &_num2, const string &_num3) : calculation(_num1, _num2, _num3) {}
	virtual instruction* copy() { return new sne(*this); }
	virtual void EX() { result = num1 != num2; }
};

class jump : public instruction { // b, j, jr
public:
	int rsrc, pos;

	jump(const string &label) : instruction(), rsrc(-1), pos(-1) {
		if (text_label.find(label) != text_label.end()) pos = text_label[label];
		else rsrc = string_to_reg(label), reg_to_read.push_back(rsrc);
		type_of_jump = 1;
	}
	virtual instruction* copy() { return new jump(*this); }
	virtual void ID() { if (rsrc != -1) pos = reg[rsrc]; }
	virtual void WB() {
		ins_top = pos;
	}
};
class jal : public instruction { // jal, jalr
public:
	int rsrc, pos;

	jal(const string &label) : instruction(), rsrc(-1), pos(-1) {
		if (text_label.find(label) != text_label.end()) pos = text_label[label];
		else rsrc = string_to_reg(label), reg_to_read.push_back(rsrc);
		type_of_jump = 1;
		reg_to_write.push_back(31);
	}
	virtual instruction* copy() { return new jal(*this); }
	virtual void ID() { if (rsrc != -1) pos = reg[rsrc]; }
	virtual void WB() {
		reg[31] = ins_top;
		ins_top = pos;
	}
};
class branch : public instruction {
public:
	int rsrc1, rsrc2;
	int num1, num2;
	int pos;
	bool judge;

	branch(const string &_rsrc1, const string &_rsrc2, const string &label) : instruction(), judge(false) {
		rsrc1 = string_to_reg(_rsrc1);
		rsrc2 = string_to_reg(_rsrc2);
		if (rsrc1 == -1) num1 = string_to_int(_rsrc1);
		else reg_to_read.push_back(rsrc1);
		if (rsrc2 == -1) num2 = string_to_int(_rsrc2);
		else reg_to_read.push_back(rsrc2);
		pos = text_label[label];
		type_of_jump = 2;
	}
	virtual instruction* copy() { return new branch(*this); }
	virtual void ID() {
		if (rsrc1 != -1) num1 = reg[rsrc1];
		if (rsrc2 != -1) num2 = reg[rsrc2];
	}
	virtual void WB() { if (judge) ins_top = pos; }
};
class beq : public branch {
public:
	beq(const string &_num1, const string  &_num2, const string &_num3) : branch(_num1, _num2, _num3) {}
	virtual instruction* copy() { return new beq(*this); }
	virtual void EX() { judge = num1 == num2; }
};
class bne : public branch {
public:
	bne(const string &_num1, const string  &_num2, const string &_num3) : branch(_num1, _num2, _num3) {}
	virtual instruction* copy() { return new bne(*this); }
	virtual void EX() { judge = num1 != num2; }
};
class bge : public branch {
public:
	bge(const string &_num1, const string  &_num2, const string &_num3) : branch(_num1, _num2, _num3) {}
	virtual instruction* copy() { return new bge(*this); }
	virtual void EX() { judge = num1 >= num2; }
};
class ble : public branch {
public:
	ble(const string &_num1, const string  &_num2, const string &_num3) : branch(_num1, _num2, _num3) {}
	virtual instruction* copy() { return new ble(*this); }
	virtual void EX() { judge = num1 <= num2; }
};
class bgt : public branch {
public:
	bgt(const string &_num1, const string  &_num2, const string &_num3) : branch(_num1, _num2, _num3) {}
	virtual instruction* copy() { return new bgt(*this); }
	virtual void EX() { judge = num1 > num2; }
};
class blt : public branch {
public:
	blt(const string &_num1, const string  &_num2, const string &_num3) : branch(_num1, _num2, _num3) {}
	virtual instruction* copy() { return new blt(*this); }
	virtual void EX() { judge = num1 < num2; }
};

class loading : public instruction {
public:
	int rdest, rsrc;
	string address;
	int val, pos, offset;

	loading(const string &_rdest, const string &_address) :
		instruction(), rsrc(-1), address(_address), val(0), pos(-1), offset(0) {
		rdest = string_to_reg(_rdest);
		reg_to_write.push_back(rdest);
		if (data_label.find(address) != data_label.end()) {
			pos = data_label[address];
			return;
		}
		int i = address.find('(');
		int j = address.find(')');
		offset = string_to_int(address.substr(0, i));
		rsrc = string_to_reg(address.substr(i + 1, j - i - 1));
		reg_to_read.push_back(rsrc);
	}
	virtual instruction* copy() { return new loading(*this); }
	virtual void ID() { if (rsrc != -1) pos = reg[rsrc]; }
	virtual void EX() { pos += offset; }
	virtual void WB() { reg[rdest] = val; }
};
class la : public loading {
public:
	la(const string &_num1, const string &_num2) : loading(_num1, _num2) {}
	virtual instruction* copy() { return new la(*this); }
	virtual void WB() { reg[rdest] = pos; }
};
class lb : public loading {
public:
	lb(const string &_num1, const string &_num2) : loading(_num1, _num2) {}
	virtual instruction* copy() { return new lb(*this); }
	virtual void MEM() { memcpy(&val, mem + pos, 1); }
};
class lh : public loading {
public:
	lh(const string &_num1, const string &_num2) : loading(_num1, _num2) {}
	virtual instruction* copy() { return new lh(*this); }
	virtual void MEM() { memcpy(&val, mem + pos, 2); }
};
class lw : public loading {
public:
	lw(const string &_num1, const string &_num2) : loading(_num1, _num2) {}
	virtual instruction* copy() { return new lw(*this); }
	virtual void MEM() { memcpy(&val, mem + pos, 4); }
};

class storing : public instruction {
public:
	int rdest, rsrc;
	string address;
	int val, pos, offset;

	storing(const string &_rdest, const string &_address) :
		instruction(), rsrc(-1), address(_address), val(0), pos(-1), offset(0) {
		write_to_mem = true;
		rdest = string_to_reg(_rdest);
		reg_to_read.push_back(rdest);
		if (data_label.find(address) != data_label.end()) {
			pos = data_label[address];
			return;
		}
		int i = address.find('(');
		int j = address.find(')');
		offset = string_to_int(address.substr(0, i));
		rsrc = string_to_reg(address.substr(i + 1, j - i - 1));
		reg_to_read.push_back(rsrc);
	}
	virtual instruction* copy() { return new storing(*this); }
	virtual void ID() {
		val = reg[rdest];
		if (rsrc != -1) pos = reg[rsrc];
	}
	virtual void EX() { pos += offset; }
};
class sb : public storing {
public:
	sb(const string &_num1, const string &_num2) : storing(_num1, _num2) {}
	virtual instruction* copy() { return new sb(*this); }
	virtual void MEM() { memcpy(mem + pos, &val, 1); }
};
class sh : public storing {
public:
	sh(const string &_num1, const string &_num2) : storing(_num1, _num2) {}
	virtual instruction* copy() { return new sh(*this); }
	virtual void MEM() { memcpy(mem + pos, &val, 2); }
};
class sw : public storing {
public:
	sw(const string &_num1, const string &_num2) : storing(_num1, _num2) {}
	virtual instruction* copy() { return new sw(*this); }
	virtual void MEM() { memcpy(mem + pos, &val, 4); }
};

class assignment : public instruction {
public:
	int rdest, rsrc, imm;

	assignment(const string &_rdest, const string &_rsrc) : instruction() {
		rdest = string_to_reg(_rdest);
		reg_to_write.push_back(rdest);
		rsrc = string_to_reg(_rsrc);
		if (rsrc == -1) imm = string_to_int(_rsrc);
		else reg_to_read.push_back(rsrc);
	}
	virtual instruction* copy() { return new assignment(*this); }
	virtual void ID() { if (rsrc != -1) imm = reg[rsrc]; }
	virtual void WB() { reg[rdest] = imm; }
};
class mfhi : public assignment {
public:
	mfhi(const string &_rdest) : assignment(_rdest, "$hi") {}
};
class mflo : public assignment {
public:
	mflo(const string &_rdest) : assignment(_rdest, "$lo") {}
};


class syscall : public instruction {
public:
	istream &is;
	ostream &os;
	int type, val_a0, val_a1, result;
	string str;

	syscall(istream &_is, ostream &_os) : instruction(), is(_is), os(_os) {
		str = "";
		reg_to_read.push_back(2);
		reg_to_read.push_back(4);
		reg_to_read.push_back(5);
		reg_to_write.push_back(2);
		write_to_mem = true;
	}
	virtual instruction* copy() { return new syscall(*this); }
	virtual void ID() {
		type = reg[2]; // $v0
		switch (type) {
		case 1: case 4: case 9: case 17: val_a0 = reg[4]; break; // $a0
		case 8:
			val_a0 = reg[4]; // $a0
			val_a1 = reg[5]; // $a1
			break;
		}
	}
	virtual void EX() {
		str = "";
		switch (type) {
		case 1: os << val_a0; break;
		case 5: is >> result; break;
		case 8: is >> str; break;
		case 10: shut_down(0); break;
		case 17: shut_down(val_a0); break;
		}
	}
	virtual void MEM() {
		int i;
		switch (type) {
		case 4:
			i = val_a0;
			while (mem[i]) os << mem[i++];
			break;
		case 8:
			int l = str.length();// strlen(str);
			i = 0;
			while (i < l) mem[val_a0 + i] = str[i], ++i;
			break;
		}
	}
	virtual void WB() {
		switch (type) {
		case 5: reg[2] = result; break;
		case 9:
			reg[2] = heap_top;
			heap_top += val_a0;
			break;
		}
	}
};

void shut_down(int val) {
	vector<instruction*>::iterator it = ins_vec.begin();
	while (it != ins_vec.end()) delete *(it++);
	//while (true);
	exit(val);
}

// ============================= interpreter ==================================
class interpreter {
public:
	ifstream &src;
	istream &is;
	ostream &os;

	interpreter(ifstream &_src, istream &_is, ostream &_os) : src(_src), is(_is), os(_os) {
		memset(reg, 0, sizeof reg);
		memset(mem, 0, sizeof mem);
		reg[29] = MAXN - 1;
	} // $sp stack_top
	void interprete() {
		read_in();
		execute_text();
	}
	void read_in() {
		char str[MAXL];
		int ins_cnt = 0;
		vector<string> name_vec, ph1_vec, ph2_vec, ph3_vec;
		bool text_block = false;
		while (src.getline(str, MAXL, '\n')) {
			string tmp = "";
			int i = 0, l = strlen(str);
			while (str[i] == ' ' || str[i] == '\t') ++i;
			if (str[i] == '.') { // .xxx
				++i;
				tmp = get_phrase(str, i, l);
				if (tmp == "align") {
					++i;
					tmp = get_phrase(str, i, l);
					int n = string_to_int(tmp);
					n = power(n);
					heap_top += (n - heap_top  % n) % n;
				}
				else if (tmp == "ascii" || tmp == "asciiz") {
					bool flag = tmp == "asciiz";
					i += 2;
					tmp = get_str(str, i, l - 1);
					for (int i = 0; i < tmp.length(); ++i)
						mem[heap_top++] = tmp[i];
					if (flag) mem[heap_top++] = 0;
				}
				else if (tmp == "byte" || tmp == "half" || tmp == "word") {
					int m = tmp == "byte" ? 1 : (tmp == "half" ? 2 : 4);
					while (true) {
						if (i == l) break;
						++i;
						tmp = get_phrase(str, i, l);
						int n = string_to_int(tmp);
						memcpy(mem + heap_top, &n, m);
						heap_top += m;
					}
				}
				else if (tmp == "space") {
					++i;
					tmp = get_phrase(str, i, l);
					int n = string_to_int(tmp);
					heap_top += n;
				}
				else if (tmp == "data" || tmp == "text") text_block = tmp == "text";
			}
			else if (str[l - 1] == ':') { // label:
				string tmp = get_phrase(str, i, l - 1);
				if (text_block) text_label[tmp] = ins_cnt;
				else data_label[tmp] = heap_top;
			}
			else { // text instruction
				string name = get_phrase(str, i, l); ++i;
				if (name == "") continue;
				++ins_cnt;
				name_vec.push_back(name);
				ph1_vec.push_back(get_phrase(str, i, l)); ++i;
				ph2_vec.push_back(get_phrase(str, i, l)); ++i;
				ph3_vec.push_back(get_phrase(str, i, l)); ++i;
			}
		}
		for (int i = 0; i < ins_cnt; ++i) {
			string name = name_vec[i];
			string _num1 = ph1_vec[i], _num2 = ph2_vec[i], _num3 = ph3_vec[i];
			instruction *ptr = NULL;
			// loading instruction
			if (name == "la") ptr = new la(_num1, _num2);
			if (name == "lb") ptr = new lb(_num1, _num2);
			if (name == "lh") ptr = new lh(_num1, _num2);
			if (name == "lw") ptr = new lw(_num1, _num2);
			// storing instruction
			if (name == "sb") ptr = new sb(_num1, _num2);
			if (name == "sh") ptr = new sh(_num1, _num2);
			if (name == "sw") ptr = new sw(_num1, _num2);
			// assignment instruction
			if (name == "li" || name == "move") ptr = new assignment(_num1, _num2);
			if (name == "mfhi") ptr = new mfhi(_num1);
			if (name == "mflo") ptr = new mflo(_num1);
			// calculation instruction
			if (name == "add") ptr = new add(_num1, _num2, _num3, false);
			if (name == "addu" || name == "addiu") ptr = new add(_num1, _num2, _num3, true);
			if (name == "sub") ptr = new sub(_num1, _num2, _num3, false);
			if (name == "subu") ptr = new sub(_num1, _num2, _num3, true);
			if (name == "mul") ptr = new mul(_num1, _num2, _num3, false);
			if (name == "mulu") ptr = new mul(_num1, _num2, _num3, true);
			if (name == "div") ptr = new Div(_num1, _num2, _num3, false);
			if (name == "divu") ptr = new Div(_num1, _num2, _num3, true);
			if (name == "xor") ptr = new Xor(_num1, _num2, _num3, false);
			if (name == "xoru") ptr = new Xor(_num1, _num2, _num3, true);
			if (name == "neg") ptr = new neg(_num1, _num2, false);
			if (name == "negu") ptr = new neg(_num1, _num2, true);
			if (name == "rem") ptr = new rem(_num1, _num2, _num3, false);
			if (name == "remu") ptr = new rem(_num1, _num2, _num3, true);
			if (name == "seq") ptr = new seq(_num1, _num2, _num3);
			if (name == "sne") ptr = new sne(_num1, _num2, _num3);
			if (name == "sge") ptr = new sge(_num1, _num2, _num3);
			if (name == "sle") ptr = new sle(_num1, _num2, _num3);
			if (name == "sgt") ptr = new sgt(_num1, _num2, _num3);
			if (name == "slt") ptr = new slt(_num1, _num2, _num3);
			// jump instruction
			if (name == "b" || name == "j" || name == "jr") ptr = new jump(_num1);
			if (name == "jal" || name == "jalr") ptr = new jal(_num1);
			if (name == "beq") ptr = new beq(_num1, _num2, _num3);
			if (name == "bne") ptr = new bne(_num1, _num2, _num3);
			if (name == "bge") ptr = new bge(_num1, _num2, _num3);
			if (name == "ble") ptr = new ble(_num1, _num2, _num3);
			if (name == "bgt") ptr = new bgt(_num1, _num2, _num3);
			if (name == "blt") ptr = new blt(_num1, _num2, _num3);
			if (name == "beqz") ptr = new beq(_num1, "0", _num2);
			if (name == "bnez") ptr = new bne(_num1, "0", _num2);
			if (name == "bgez") ptr = new bge(_num1, "0", _num2);
			if (name == "blez") ptr = new ble(_num1, "0", _num2);
			if (name == "bgtz") ptr = new bgt(_num1, "0", _num2);
			if (name == "bltz") ptr = new blt(_num1, "0", _num2);
			// syscall instruction
			if (name == "syscall") ptr = new syscall(is, os);
			if (name == "nop") ptr = new instruction();
			ins_vec.push_back(ptr);
		}
	}
	void execute_text() {
		ins_top = text_label["main"];
		int ins_vec_sz = ins_vec.size();
		int jump_cnt = 0;
		int reg_cnt[34], cnt = 0;
		memset(reg_cnt, 0, sizeof reg_cnt);
		for (int i = 0; i < 5; ++i) plat[i] = NULL;
		vector<int>::iterator it;
		while (true) {
			// write back
			if (plat[4] != NULL) {
				plat[4]->WB();
				jump_cnt -= plat[4]->type_of_jump;
				it = plat[4]->reg_to_write.begin();
				while (it != plat[4]->reg_to_write.end()) --reg_cnt[*(it++)];
				plat[4] = NULL;
				--cnt;
			}
			// memory access
			bool write_to_mem = false;
			if (plat[3] != NULL) {
				plat[3]->MEM();
				write_to_mem = plat[3]->write_to_mem;
			}
			plat[4] = plat[3];
			// EX
			if (plat[2] != NULL) plat[2]->EX();
			plat[3] = plat[2];
			// data prepare
			if (plat[1] != NULL) plat[1]->ID();
			plat[2] = plat[1];
			// instruction fetch
			plat[1] = plat[0];
			plat[0] = NULL;
			if (ins_top >= ins_vec_sz) continue;
			instruction *ptr = ins_vec[ins_top];
			bool reg_conflict = false;
			it = ptr->reg_to_read.begin();
			while (it != ptr->reg_to_read.end())
				if (reg_cnt[*(it++)] > 0) reg_conflict = true;
			if (jump_cnt > 0 || write_to_mem || reg_conflict) ptr = NULL;
			else {
				jump_cnt += ptr->type_of_jump;
				it = ptr->reg_to_write.begin();
				while (it != ptr->reg_to_write.end()) ++reg_cnt[*(it++)];
				++ins_top;
				++cnt;
			}
			plat[0] = ptr;
		}
	}
};

int main(int argc, char *argv[]) {

	ifstream source;
	ifstream input;

	source.open(argv[1]);

	interpreter itp(source, cin, cout);
	itp.interprete();
	shut_down(0);

	return 0;
}
