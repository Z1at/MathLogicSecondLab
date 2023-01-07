#include<algorithm>
#include <iostream>
#include <vector>
#include <regex>
#include <string>
#include <map>
using namespace std;
using ll = long long;

vector<string> split(const string& s, const string& pt){
    vector<string> res;
    string cur;
    for(auto now : s){
        if(cur.size() >= pt.size()){
            if(cur.substr(cur.size() - pt.size()) == pt){
                if(cur == pt){
                    cur = "";
                }
                else{
                    res.push_back(cur.substr(0, cur.size() - pt.size()));
                    cur = "";
                }
            }
        }
        cur += now;
    }

    if(cur.size() >= pt.size()){
        if(cur.substr(cur.size() - pt.size()) == pt){
            if(cur == pt){
                cur = "";
            }
            else{
                res.push_back(cur.substr(0, cur.size() - pt.size()));
                cur = "";
            }
        }
        else{
            res.push_back(cur);
        }
    }
    else{
        res.push_back(cur);
    }
    return res;
}

//Axioms
string firstAx(const string& a, const string& b) {
    return "(" + a + " -> (" + b + " -> " + a + "))";
}
string secondAx(const string& a, const string& b, const string& c) {
    return "((" + a + " -> " + b + ") -> ((" + a + " -> (" + b + " -> " + c + "))" + " -> " + "(" + a + " -> " + c + ")))";
}
string ninthAx(const string& a, const string& b) {
    return "((" + a + " -> " + b + ") -> ((" + a + " -> !" + b + ") -> !" + a + "))";
}
string tenthAx(const string& a, const string& b) {
    return "(" + a + " -> (!" + a + " -> " + b + "))";
}


//FixLine
struct FixLine{
    string newLine;
    string curLine;
    ll curIndex = 0;

    string fixLine(const string& cur){
        this->curLine = cur;
        this->curIndex = 0;
        implication();
        return newLine;
    }
    string implication() {
        newLine = disjunction();
        if (checkOperation("->")) {
            newLine = "(" + newLine + " -> " + implication() + ")";
        }
        return newLine;
    }
    string disjunction() {
        newLine = conjunction();
        while (checkOperation("|")) {
            newLine = "(" + newLine + " | " + conjunction() + ")";
        }
        return newLine;
    }
    string conjunction() {
        newLine = negation();
        while (checkOperation("&")) {
            newLine = "(" + newLine + " & " + negation() + ")";
        }
        return newLine;
    }
    string negation() {
        if (checkOperation("(")){
            newLine = implication();
            checkOperation(")");
            return newLine;
        }
        if (checkOperation("!")) {
            return "!" + negation();
        }
        newLine = "";
        string element = "";
        if (curIndex < curLine.length() - 1) {
            element = curLine.substr(curIndex, 1);
        } else {
            element = curLine.substr(curIndex);
        }

        regex digits("[0-9]+");
        regex letters("[a-zA-z]+");
        while (regex_match(element, digits) || element == "'" || regex_match(element, letters)) {
            newLine += element;
            curIndex++;
            if (curIndex < curLine.length() - 1) {
                element = curLine.substr(curIndex, 1);
            } else {
                element = curLine.substr(curIndex);
            }
        }
        return newLine;
    }
    bool checkOperation(const string& opt) {
        bool f = true;
        for(ll i = 0; i < opt.size(); i++){
            if(curLine[i + curIndex] != opt[i]) f = false;
        }
        if(f){
            curIndex += opt.size();
            return true;
        } else {
            return false;
        }
    }

};


//Proof
struct Proof{
    vector<string> proofsKIV;
    string tenthV;
    map<ll, string> hashProof;
    vector<string> hyps;

    Proof(const vector<string>& KIV, const map<ll, string>& hash, const vector<string>& hyp) {
        this->proofsKIV = KIV;
        this->hashProof = hash;
        this->hyps = hyp;
    }

    string MP(const string& a, const string& result) {
        string dlt = "(" + a + " -> ";
        string newResult;
        bool f = true;
        for(ll i = 0; i < dlt.size(); i++){
            if(result[i] != dlt[i]) f = false;
        }
        if(f){
            newResult = result.substr(a.size() + 5, result.size() - a.size() - 6);
        } else {
            newResult = result;
        }
        return newResult;
    }

    vector<string> specialWrite(const string& str, vector<string> proofs) {
        cout << str << '\n';
        proofs.push_back(str);
        return proofs;
    }

    bool check(const map<ll, string>& mp, const string& value){
        for(auto& now : mp){
            if(now.second == value) return true;
        }
        return false;
    }

    bool isMP(string currentProof, int index) {
        for (int i = 0; i < index; i++) {
            string impl = "(" + proofsKIV[i] + " -> " + currentProof + ")";
            if (check(hashProof, impl)) {
                proof3(proofsKIV[i], currentProof);
                return true;
            }
        }
        return false;
    }

    void setTenthV(const string& tenth) {
        this->tenthV = tenth;
    }

    string getTenthV() {
        return tenthV;
    }

    bool isTenthAx(const string& str) {
        bool f = true;
        string s = "(!!";
        for(ll i = 0; i < s.size(); i++){
            if(str[i] != s[i]) f = false;
        }
        if(f){
            string newLine = str.substr(3, str.length() - 4);
            vector<string> elements = split(newLine, " -> ");
            if (elements.size() % 2 == 0) {
                int lastIndex = elements.size() / 2;
                string left = elements[0];
                string right = elements[lastIndex];
                for (int i = 1; i < lastIndex; i++) {
                    left.append(" -> ").append(elements[i]);
                }
                for (int i = lastIndex + 1; i < elements.size(); i++) {
                    right.append(" -> ").append(elements[i]);
                }
                setTenthV(left);
                return ((left) == (right));
            }
            return false;
        }
        return false;
    }

    void proof() {
        for (int i = 0; i < proofsKIV.size(); i++) {
            string currentProof = proofsKIV[i];
//            cout << '\n' << currentProof << '\n';
            if (count(hyps.begin(), hyps.end(), currentProof)) {
                proof1(currentProof);
            } else if (!isMP(currentProof, i)) {
                if (isTenthAx(currentProof)) {
                    proof2(getTenthV());
                } else {
                    proof1(currentProof);
                }
            }
        }
    }

    void proof1(const string& a) {
        vector<string> proofs;
        proofs = specialWrite(a, proofs);
        string b = "!" + a;
        string current = firstAx(proofs[0], b);
        proofs = specialWrite(current, proofs);
        current = MP(proofs[0], current);
        proofs = specialWrite(current, proofs);
        current = firstAx(b, b);
        proofs = specialWrite(current, proofs);
        current = secondAx(b, "(" + b + " -> " + b + ")", b);
        proofs = specialWrite(current, proofs);
        current = MP(proofs[3], current);
        proofs = specialWrite(current, proofs);
        current = firstAx(b, "(" + b + " -> " + b + ")");
        proofs = specialWrite(current, proofs);
        current = MP(current, proofs[5]);
        proofs = specialWrite(current, proofs);
        current = ninthAx(b, a);
        proofs = specialWrite(current, proofs);
        current = MP(proofs[2], current);
        proofs = specialWrite(current, proofs);
        current = MP(proofs[7], current);
        specialWrite(current, proofs);
    }

    void proof2(const string& a) {
        vector<string> proofs;
        proofs.push_back(a);//0
        //b = !a
        //a = (A&!!A)
        string b = "!" + a;
        string current = firstAx(proofs[0], "!" + b);//1
        proofs = specialWrite(current, proofs);
        string element = "!(!" + b + " -> " + proofs[0] + ")";
        current = firstAx(proofs[1], element);//2
        proofs = specialWrite(current, proofs);
        current = MP(proofs[1], proofs[2]);//3
        proofs = specialWrite(current, proofs);
        current = firstAx(element, proofs[0]);//4
        proofs = specialWrite(current, proofs);
        current = firstAx(element, element);//5
        proofs = specialWrite(current, proofs);
        current = firstAx(element, "(" + element + " -> " + element + ")");//6
        proofs = specialWrite(current, proofs);
        current = secondAx(element, "(" + element + " -> " + element + ")", element);//7
        proofs = specialWrite(current, proofs);
        current = MP(proofs[5], proofs[7]);//8
        proofs = specialWrite(current, proofs);
        current = MP(proofs[6], proofs[8]);//9
        proofs = specialWrite(current, proofs);
        current = ninthAx(proofs[0], element.substr(1));//10
        proofs = specialWrite(current, proofs);
        current = firstAx(proofs[10], element);//11
        proofs = specialWrite(current, proofs);
        current = MP(proofs[10], proofs[11]);//12
        proofs = specialWrite(current, proofs);
        current = secondAx(element, proofs[1], "((" + proofs[0] + " -> " + element + ") -> " + b + ")");//13
        proofs = specialWrite(current, proofs);
        current = MP(proofs[3], proofs[13]);//14
        proofs = specialWrite(current, proofs);
        current = MP(proofs[12], proofs[14]);//15
        proofs = specialWrite(current, proofs);
        current = secondAx(element, "(" + proofs[0] + " -> " + element + ")", b);//16
        proofs = specialWrite(current, proofs);
        current = MP(proofs[4], proofs[16]);//17
        proofs = specialWrite(current, proofs);
        current = MP(proofs[15], proofs[17]);//18
        proofs = specialWrite(current, proofs);
        current = tenthAx(b, proofs[0]);//19
        proofs = specialWrite(current, proofs);
        current = firstAx(proofs[19], element);//20
        proofs = specialWrite(current, proofs);
        current = MP(proofs[19], proofs[20]);//21
        proofs = specialWrite(current, proofs);
        current = secondAx(element, b, element.substr(1));//22
        proofs = specialWrite(current, proofs);
        current = MP(proofs[18], proofs[22]);//23
        proofs = specialWrite(current, proofs);
        current = MP(proofs[21], proofs[23]);//24
        proofs = specialWrite(current, proofs);
        current = ninthAx(element, element.substr(1));//25
        proofs = specialWrite(current, proofs);
        current = MP(proofs[24], proofs[25]);//26
        proofs = specialWrite(current, proofs);
        current = MP(proofs[9], proofs[26]);
        specialWrite(current, proofs);//27
    }

    void proof3(const string& a, const string& b) {
        string impl = "(" + a + " -> " + b + ")";
        string negA = "!" + a;
        string negB = "!" + b;
//        System.out.println(negB);
        vector<string> proofs;
        string current = firstAx(negB, impl);//1
        proofs = specialWrite(current, proofs);
        current = firstAx(negB, a);//2
        proofs = specialWrite(current, proofs);
        current = firstAx(proofs[1], negB);//3
        proofs = specialWrite(current, proofs);
        current = MP(proofs[1], proofs[2]);//4
        proofs = specialWrite(current, proofs);
        current = firstAx(proofs[1], impl);//5
        proofs = specialWrite(current, proofs);
        current = firstAx(proofs[4], negB);//6
        proofs = specialWrite(current, proofs);
        current = MP(proofs[4], proofs[5]);//7
        proofs = specialWrite(current, proofs);
        current = secondAx(negB, proofs[1], "(" + impl + " -> " + proofs[1] + ")");//8
        proofs = specialWrite(current, proofs);
        current = MP(proofs[3], proofs[7]);//9
        proofs = specialWrite(current, proofs);
        current = MP(proofs[6], proofs[8]);//10
        proofs = specialWrite(current, proofs);
        current = secondAx(impl, negB, "(" + a + " -> " + negB + ")");//11
        proofs = specialWrite(current, proofs);
        current = firstAx(proofs[10], negB);//12
        proofs = specialWrite(current, proofs);
        current = MP(proofs[10], proofs[11]);//13
        proofs = specialWrite(current, proofs);
        current = secondAx(negB, "(" + impl + " -> " + negB + ")", "((" + impl + " -> (" + negB + " -> (" + a + " -> " + negB + "))) -> (" + impl + " -> " + "(" + a + " -> " + negB + ")))");//14
        proofs = specialWrite(current, proofs);
        current = MP(proofs[0], proofs[13]);//15
        proofs = specialWrite(current, proofs);
        current = MP(proofs[12], proofs[14]);//16
        proofs = specialWrite(current, proofs);
        current = secondAx(negB, "(" + impl + " -> (" + negB + " -> (" + a + " -> " + negB + ")))", "(" + impl + " -> " + "(" + a + " -> " + negB + "))");//17
        proofs = specialWrite(current, proofs);
        current = MP(proofs[9], proofs[16]);//18
        proofs = specialWrite(current, proofs);
        current = MP(proofs[15], proofs[17]);//19
        proofs = specialWrite(current, proofs);
        current = ninthAx(a, b);//20
        proofs = specialWrite(current, proofs);
        current = firstAx(proofs[19], negB);//21
        proofs = specialWrite(current, proofs);
        current = MP(proofs[19], proofs[20]);//22
        proofs = specialWrite(current, proofs);
        current = secondAx(impl, "(" + a + " -> " + negB + ")", negA);//23
        proofs = specialWrite(current, proofs);
        current = firstAx(proofs[22], negB);//24
        proofs = specialWrite(current, proofs);
        current = MP(proofs[22], proofs[23]);//25
        proofs = specialWrite(current, proofs);
        current = secondAx(negB, "(" + impl + " -> " + "(" + a + " -> " + negB + "))", "((" + impl + " -> " + "((" + a + " -> " + negB + ") -> " + negA + ")) -> (" + impl + " -> " + negA + "))");//26
        proofs = specialWrite(current, proofs);
        current = MP(proofs[18], proofs[25]);//27
        proofs = specialWrite(current, proofs);
        current = MP(proofs[24], proofs[26]);//28
        proofs = specialWrite(current, proofs);
        current = secondAx(negB, "(" + impl + " -> " + "((" + a + " -> " + negB + ") -> " + negA + "))", "((" + a + " -> " + b + ") -> " + negA + ")");//29
        proofs = specialWrite(current, proofs);
        current = MP(proofs[21], proofs[28]);//30
        proofs = specialWrite(current, proofs);
        current = MP(proofs[27], proofs[29]);//31
        proofs = specialWrite(current, proofs);
        current = "!" + negA;//32
        proofs = specialWrite(current, proofs);
        current = firstAx("!" + negA, negB);//33
        proofs = specialWrite(current, proofs);
        current = MP(proofs[31], proofs[32]);//34
        proofs = specialWrite(current, proofs);
        current = firstAx(proofs[31], impl);//35
        proofs = specialWrite(current, proofs);
        current = firstAx(proofs[34], negB);//36
        proofs = specialWrite(current, proofs);
        current = MP(proofs[34], proofs[35]);//37
        proofs = specialWrite(current, proofs);
        current = secondAx(negB, "!" + negA, "(" + impl + " -> !" + negA + ")");//38
        proofs = specialWrite(current, proofs);
        current = MP(proofs[33], proofs[37]);//39
        proofs = specialWrite(current, proofs);
        current = MP(proofs[36], proofs[38]);//40
        proofs = specialWrite(current, proofs);
        current = tenthAx(negA, "!" + impl);//41
        proofs = specialWrite(current, proofs);
        current = firstAx(proofs[40], negB);//42
        proofs = specialWrite(current, proofs);
        current = MP(proofs[40], proofs[41]);//43
        proofs = specialWrite(current, proofs);
        current = firstAx(proofs[40], impl);//44
        proofs = specialWrite(current, proofs);
        current = firstAx(proofs[43], negB);//45
        proofs = specialWrite(current, proofs);
        current = MP(proofs[43], proofs[44]);//46
        proofs = specialWrite(current, proofs);
        current = secondAx(negB, proofs[40], "(" + impl + " -> (" + negA + " -> (!" + negA + " -> !" + impl + ")))");//47
        proofs = specialWrite(current, proofs);
        current = MP(proofs[42], proofs[46]);//48
        proofs = specialWrite(current, proofs);
        current = MP(proofs[45], proofs[47]);//49
        proofs = specialWrite(current, proofs);
        current = secondAx(impl, negA, "(!" + negA + " -> !" + impl + ")");//50
        proofs = specialWrite(current, proofs);
        current = firstAx(proofs[49], negB);//51
        proofs = specialWrite(current, proofs);
        current = MP(proofs[49], proofs[50]);//52
        proofs = specialWrite(current, proofs);
        current = secondAx(negB, "(" + impl + " -> " + negA + ")", "((" + impl + " -> (" + negA + " -> (!" + negA + " -> !" + impl + "))) -> (" + impl + " -> (!" + negA + " -> !" + impl + ")))");//53
        proofs = specialWrite(current, proofs);
        current = MP(proofs[30], proofs[52]);//54
        proofs = specialWrite(current, proofs);
        current = MP(proofs[51], proofs[53]);//55
        proofs = specialWrite(current, proofs);
        current = secondAx(negB, "(" + impl + " -> (" + negA + " -> (!" + negA + " -> !" + impl + ")))", "(" + impl + " -> (!" + negA + " -> !" + impl + "))");//56
        proofs = specialWrite(current, proofs);
        current = MP(proofs[48], proofs[55]);//57
        proofs = specialWrite(current, proofs);
        current = MP(proofs[54], proofs[56]);//58
        proofs = specialWrite(current, proofs);
        current = secondAx(impl, "!" + negA, "!" + impl);//59
        proofs = specialWrite(current, proofs);
        current = firstAx(proofs[58], negB);//60
        proofs = specialWrite(current, proofs);
        current = MP(proofs[58], proofs[59]);//61
        proofs = specialWrite(current, proofs);
        current = secondAx(negB, "(" + impl + " -> !!" + a + ")", "((" + impl + " -> (!" + negA + " -> !" + impl + ")) -> (" + impl + " -> !" + impl + "))");
        proofs = specialWrite(current, proofs);
        current = MP(proofs[39], proofs[61]);//63
        proofs = specialWrite(current, proofs);
        current = MP(proofs[60], proofs[62]);//64
        proofs = specialWrite(current, proofs);
        current = secondAx(negB, "(" + impl + " -> (!" + negA + " -> !" + impl + "))", "(" + impl + " -> !" + impl + ")");//65
        proofs = specialWrite(current, proofs);
        current = MP(proofs[57], proofs[64]);//66
        proofs = specialWrite(current, proofs);
        current = MP(proofs[63], proofs[65]);//67
        proofs = specialWrite(current, proofs);
        current = "!!" + impl;//68
        proofs = specialWrite(current, proofs);
        current = firstAx(proofs[67], negB);//69
        proofs = specialWrite(current, proofs);
        current = MP(proofs[67], proofs[68]);//70
        proofs = specialWrite(current, proofs);
        current = firstAx(proofs[67], impl);//71
        proofs = specialWrite(current, proofs);
        current = firstAx(proofs[70], negB);//72
        proofs = specialWrite(current, proofs);
        current = MP(proofs[70], proofs[71]);//73
        proofs = specialWrite(current, proofs);
        current = secondAx(negB, proofs[67], "(" + impl + " -> " + proofs[67] + ")");//74
        proofs = specialWrite(current, proofs);
        current = MP(proofs[69], proofs[73]);//75
        proofs = specialWrite(current, proofs);
        current = MP(proofs[72], proofs[74]);//76
        proofs = specialWrite(current, proofs);
        current = ninthAx(impl, "!" + impl);//77
        proofs = specialWrite(current, proofs);
        current = firstAx(proofs[76], negB);//78
        proofs = specialWrite(current, proofs);
        current = MP(proofs[76], proofs[77]);//79
        proofs = specialWrite(current, proofs);
        current = secondAx(negB, "(" + impl + " -> " + "!" + impl + ")", "((" + impl + " -> " + proofs[67] + ") -> !" + impl + ")");//80
        proofs = specialWrite(current, proofs);
        current = MP(proofs[66], proofs[79]);//81
        proofs = specialWrite(current, proofs);
        current = MP(proofs[78], proofs[80]);//82
        proofs = specialWrite(current, proofs);
        current = secondAx(negB, "(" + impl + " -> " + proofs[67] + ")", "!" + impl);//83
        proofs = specialWrite(current, proofs);
        current = MP(proofs[75], proofs[82]);//84
        proofs = specialWrite(current, proofs);
        current = MP(proofs[81], proofs[83]);//85
        proofs = specialWrite(current, proofs);
        current = tenthAx("!" + impl, negA);//86
        proofs = specialWrite(current, proofs);
        current = firstAx(proofs[85], negB);//87
        proofs = specialWrite(current, proofs);
        current = MP(proofs[85], proofs[86]);//88
        proofs = specialWrite(current, proofs);
        current = secondAx(negB, "!" + impl, "(" + proofs[67] + " -> " + negA + ")");//89
        proofs = specialWrite(current, proofs);
        current = MP(proofs[84], proofs[88]);//90
        proofs = specialWrite(current, proofs);
        current = MP(proofs[87], proofs[89]);
        proofs = specialWrite(current, proofs);
        current = secondAx(negB, proofs[67], negA);//91
        proofs = specialWrite(current, proofs);
        current = MP(proofs[69], proofs[91]);//92
        proofs = specialWrite(current, proofs);
        current = MP(proofs[90], proofs[92]);//93
        proofs = specialWrite(current, proofs);
        current = ninthAx(negB, negA);//94
        proofs = specialWrite(current, proofs);
        current = MP(proofs[93], proofs[94]);//95
        proofs = specialWrite(current, proofs);
        current = MP(proofs[33], proofs[95]);//96
        specialWrite(current, proofs);
    }
};

std::string ReplaceAll(std::string& str, const std::string& from, const std::string& to) {
    size_t start_pos = 0;
    while((start_pos = str.find(from, start_pos)) != std::string::npos) {
        str.replace(start_pos, from.length(), to);
        start_pos += to.length(); // Handles case where 'to' is a substring of 'from'
    }
    return str;
}

void clearGarbage(string& s){
    ReplaceAll(s, "\t", "");
    ReplaceAll(s, "\n", "");
    ReplaceAll(s, " ", "");
}

bool checkForEmptiness(const string& s){
    if(s.empty() or s == " " or s == "\t" or s == "\n"){
        return true;
    }
    if(s == "|-" or s.find("|-") == string::npos){
        return true;
    }
    return false;
}

int main() {
    struct FixLine fix = *new struct FixLine();
    string usl;
    string taskProof;
    vector<string> hyps;
    vector<string> proofs;
    map<ll, string> mapProofs;
    string line;
    string hypotyses;
    string currentLine;
    getline(cin, usl);

    if(checkForEmptiness(usl)){
        return 1;
    }

    if(usl[0] == '|' and usl[1] == '-'){
        hypotyses = "";
        taskProof = usl.substr(2);
        hyps = {""};
    } else {
        vector<string> str = split(usl, "|-");
        if (str[0][str[0].size() - 1] != ' ') {
            hypotyses = str[0] + " ";
        } else {
            hypotyses = str[0];
        }
        if (str[0].find(", ") != string::npos) {
            hyps = split(str[0], ", ");
        } else {
            hyps = {""};
        }
        if (str.size() != 1) {
            taskProof = str[1];
        } else {
            taskProof = "";
        }

    }
    clearGarbage(taskProof);
//    taskProof = ReplaceAll(taskProof, " ", "");

    getline(cin, line);
    if (line.empty()) {
        return 1;
    }

    currentLine = line;
    clearGarbage(currentLine);
//    currentLine = ReplaceAll(line, "\t", "");
//    currentLine = ReplaceAll(line, "\n", "");
//    currentLine = ReplaceAll(line, " ", "");

//    cout << currentLine << '\n';
//    cout << taskProof << '\n';


    while (currentLine != taskProof) {
        if (!currentLine.empty() && count(proofs.begin(), proofs.end(), currentLine) == 0) {
            proofs.push_back(fix.fixLine(currentLine));
            mapProofs[find(proofs.begin(), proofs.end(), fix.fixLine(currentLine)) - proofs.begin()] = fix.fixLine(currentLine);
        }


        try {
            getline(cin, line);
        } catch(string tmp) {
            break;
        }
//        if (line.empty()) {
//            break;
//        }
        clearGarbage(line);
//        line = ReplaceAll(line, "\t", "");
//        line = ReplaceAll(line, "\n", "");
//        line = ReplaceAll(line, " ", "");
        if (line.empty()) {
            break;
        }

        currentLine = line;
        clearGarbage(currentLine);
//        currentLine = ReplaceAll(line, "\t", "");
//        currentLine = ReplaceAll(line, "\n", "");
//        currentLine = ReplaceAll(line, " ", "");

    }
    if (count(proofs.begin(), proofs.end(), currentLine) == 0 && !currentLine.empty()) {
        proofs.push_back(fix.fixLine(currentLine));
    }


    Proof proof = *new Proof(proofs, mapProofs, hyps);
    if (!taskProof.empty()) {
        cout << (hypotyses + "|- !!" + fix.fixLine(taskProof)) << '\n';
    }
    proof.proof();
}
