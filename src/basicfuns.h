#ifndef BASICFUNS_H_INCLUDED
#define BASICFUNS_H_INCLUDED

using namespace std;  		//needed for string types

//general functions
string lowercase(int i, string str);
string removechar(char ch, string str);
bool isoperator(int i, string s);
bool isnumber (string str);
bool ispartsel (string str);
bool isbinop (string op);
bool islogop (string op);
bool isunop (string op);
bool findchar (char c, string str);
bool isdigit(char c);
bool validcharid(char c);
string reversewords (string str);
string erasecomments (string str);
int erasecommentsfile(string input);
bool isverkeyword (string word);
string getnextidentifier (string str);

string inttostr (int n);
int strtoint(string str);
bool strlfind (string str, string strlist);
bool isverilogid (string str);

string replacesubstr (string str, string strold, string strnew);
string removechar(char ch, string str);
string replacechar (char oldchar, char newchar, string fun);
string translverilogids (string module);

#endif //BASICFUNS_H_INCLUDED