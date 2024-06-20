#include <iostream>
#include <sstream> 	//istringstream
#include <stack>
#include <fstream>
#include <string> //to_string, stoi

#include "basicfuns.h"
#include "translexp.h"
#include "transldecl.h"
#include "translca.h"

using namespace std;


 //translate indivitual sensitivity signal 
 string translsignal (string str){	
	string posedge = "posedge";
	string negedge = "negedge";
	string exp;
	string polarity = "";
	int end= 0;
	
	if (str.find(posedge)!=std::string::npos) {
		end = str.find(posedge) + 7;
		polarity = posedge;
		exp = str.substr(end, str.length());
	}
	else if (str.find(negedge)!=std::string::npos) {
		end = str.find(negedge) + 7;
		polarity = negedge;
		exp = str.substr(end, str.length());
	}
	else {
		exp =  str; 
		polarity = "trgexp";
	}
	
	string sensit = polarity + " " + translexp(exp);
	 
	return sensit;
 }
 
 //translate sensitivity list 
 string translsl (string rhs){
	string lhs;
	string sensl = "";
	int size = rhs.length();
	int last = 0;
	
	//split string by " or " and translate each signal separately and then combine all together
	for (int i = 0; i < size; i++){
		if (rhs[i] == ' ' && rhs[i + 1] == 'o' && rhs[i + 2] == 'r' && rhs[i + 3] == ' ') {
			lhs = rhs.substr(last, i - last);
			i = i + 3;
			last = i;
			sensl = sensl + translsignal(lhs) + ", ";
		}		
	}
	//add the last signal of the list
	sensl = sensl + translsignal(rhs.substr(last, size - last));
	
	return "[" + sensl + "]";
 }
 
 
 //translates procedural statements   
 /*translates statements of the form:
	- _ = _ and _ = #_ _
	- _ <= _ and _ <= #_ _
	- _ = @() _ and _ <= @() _
  TODO: currently statements enclosed in parenthesis are not supported, such as 
   (y = #23 x + z). However, if called from 'transltdpastm' function, it eliminates 
   outside parenthesis
 */
string translpa (string str){	
	
	string lhs, rhs, control;
	string notation = "[=]";
		
	int i = str.find_first_of("=");
	if (str[i-1] == '<') {		
		lhs = str.substr(0, i-1);
		notation = "[=<]";
	} 
	else lhs = str.substr(0, i);
	
	i = i + 1;  //index next to '='
	
	while (str[i] == ' ' && i < str.length())
		i = i + 1;
	
	//CASE _ = #_ _
	if (str[i] == '#') {		
		i = i + 1;		
		//skip spaces after #
		while (str[i] == ' ' && i < str.length())
			i = i + 1;
		
		int startofnum = i;
				
		//skip number after delay
		while (isdigit(str[i]) && i < str.length())
			i = i + 1;
		
		control = "[#] " + str.substr(startofnum, i - startofnum);
		
		rhs = str.substr(i, str.length()-i);
	}
	//CASE _ = @() _
	else if (str[i] == '@') {
		 i = i + 1;
		//skip spaces after @ (if any)
		while (str[i] == ' ' && i < str.length())
			i = i + 1;
		
		//@(_) _ 
		if (str[i] == '('){
			i = i + 1;
			int begin = i;
			
			//move to closing parenthesis
			while (str[i] != ')' && i < str.length())
				i = i + 1;
			
			string sl = str.substr(begin, i - begin);
			control = "[@] (" + translsl(sl) + ")";
			
			rhs = str.substr(i+1, str.length() - i);
		}
	}
	//CASE _ = _
	else {
		control = "[#] -1";
		rhs = str.substr(i, str.length() - i);
	}
		
	lhs = removechar('{', lhs);
	lhs = removechar('}', lhs);	
	
	return reversewords(lhs) + " " + notation + " " + control + " ("+translexp(rhs)+")";	
} 


 //translate triggered/delayed statement (of the form #_ _<= _  or @_ _ = _)
 string transltdstm (string str){  	 
	 //skip spaces
	int i = 0;
	while (str[i] == ' ' && i < str.length())
		i = i + 1;
	
	//case: # 23 x <= y
	if (str[i] == '#') {
		
		//insert [] around # and move to char after #
		str.insert(i, 1, '[');
		i = i + 2;
		str.insert(i, 1, ']');
		i = i + 1;
	
		//skip spaces after #
		while (str[i] == ' ' && i < str.length())
			i = i + 1;
				
		//skip number after delay
		while (isdigit(str[i]) && i < str.length())
			i = i + 1;
		
		//skip spaces after number
		while (str[i] == ' ' && i < str.length())
			i = i + 1;
		
		//separate the assignment part
		string assign = str.substr(i, str.length());
				
		//translate the assignment and place it back into the string
		str.replace(i, assign.length(), translpa(assign));
	}
	
	//case: @(_) _ <= _ 
	//triggered statement (NOTE: simple procedural statements are supported only)
	else if (str[i] == '@'){
		//insert [] around @ and move to char after @
		str.insert(i, 1, '[');
		i = i + 2;
		str.insert(i, 1, ']');
		i = i + 1;
		
		//skip spaces after @ (if any)
		while (str[i] == ' ' && i < str.length())
			i = i + 1;
		
		if (str[i] == '('){
			i = i + 1;
			int begin = i;
			
			//TODO: more than one parenthsis in sensitivity list?
			
			//move to closing parenthesis
			while (str[i] != ')')
				i = i + 1;
			
			string lhs = str.substr(0, i+1); //including ')'
			string rhs = str.substr(i+1, str.length() - i);
			
			string sl = lhs.substr(begin, i - begin);
			
			lhs = lhs.replace(begin, sl.length(), translsl(sl));
			
			str  = lhs + " " + translpa(rhs);
		}
		//case: @identifier _ <= _ 
		else {
			int begin = i;
			while (validcharid(str[i]))
				i = i + 1;
			
			string lhs = str.substr(0, i); 
			string rhs = str.substr(i, str.length() - i);
			
			string sl = lhs.substr(begin, i - begin);
			
			lhs = lhs.replace(begin, sl.length() + 2, "("+translsl(sl)+")");  //enclose in parenthesis
			
			str  = lhs + " " + translpa(rhs);
		}
	}
	
	return str;
 }

 //translate trigerred, delayed and procedural assignments (may be used in body of any block statments, such 
 //as begin..end, if-else, while, and case statements)
 //a statement enclosed in maximum one parenthesis pair is supported (e.g., ((w = #0 x = y)) is not supported)
 // but (w = #0 x = y) or w = #0 x = y is supported
 //(@(ready or posedge x) W = R1)
 string transltdpastm (string str) {
	string tstm = str;
	std::stack<char> paren;
	
	int beginofbody = 0;
	int endofbody = str.length();
	
	//skip initial spaces
	int i = 0;		
	while (str[i] == ' ' && i < str.length())
		i = i + 1;
	
	//to support a pair of outside parenthesis
	//find position of last closing parenthesis - the end of body would be the position just before
	//the last closing parenthesis (if there is any, otherwise, its end of of string)
	if (str[i] == '(') {
		i = i + 1;  	//position just after opening parenthesis
		beginofbody = i; 
			
		int j = i;		
		paren.push('(');
		j = j + 1;   //points to char after '(' and stack is now non-empty 
	
		while (!paren.empty() && j < str.length()){
			if (str[j] == '(')
				paren.push('(');
			if (str[j] == ')')
				paren.pop();
			j = j + 1;
		}	
		endofbody = j - 2; //position before last closing parenthesis
	}
	
	//substring excluding opening/closing parenthesis (if there are any)
	string body = str.substr(beginofbody, endofbody - beginofbody + 1);	
	if (str[i] == '@' || str[i] == '#')
		tstm = transltdstm(body);
	else if (str.find("=")!=std::string::npos)
		tstm = translpa (body);
	
	//replace the body (string between parenthesis, if any)
	tstm = str.replace(beginofbody, body.length(), tstm);
    	
	return tstm;
 }
 
 
 //translate 'begin..end' block (with or without name) of the form
 //begin : aname stm1; stm2; ...stmn end, where stmi is a triggered/delayed or procedural assign statement
 //TODO: nested block statements or if-then-else, while, case statements in the body
 string translblock (string str){
	int i, blockstart, namebegin, endofname;
	int startofend = 0;
	
	string name, body;
	
	//find begin of 'begin' 
	if (str.find("begin")!=std::string::npos) {
		blockstart = str.find("begin");
		i = blockstart + 5; //char after 'begin'
	}
	 
	//skip spaces after 'begin' 
	while (str[i] == ' ' && i < str.length())
		i = i + 1;	
	
	if (str[i] == ':'){
		i = i + 1;	
		//skip spaces after ':'
		while (str[i] == ' ' && i < str.length())
			i = i + 1;	
		namebegin = i;
	
		//go to end of name 
		while (str[i] != ' ' && i < str.length())
			i = i + 1;
	
		name = str.substr(namebegin, i - namebegin);
		endofname = namebegin + name.length();
		name = "[SOME " + name + "]";
		
	}
	else {
		name = "[None]";
		endofname = blockstart + 5; 
	}
		
	if (str.find("end")!=std::string::npos) 
		startofend = str.find("end");
	
	body = str.substr(endofname, startofend - endofname);	
	
	//translate each statement in the body and combine them together with constructor ';;' for sequence. 
	string tbody = "";	
	string tstm;
	int beginofstm = 0;
	for (int j = 0; j < body.length(); j++){
		if (body[j] == ';'){
			tstm = transltdpastm(body.substr(beginofstm, j - beginofstm));
			tstm = "(" + tstm + ")";  //enclosed the translated statement in parenthesis (required by Isabelle parser)
			
			string rest = body.substr(j+1, body.length()-j+1); //next statements
			if (rest.find(";")!=std::string::npos){	//if there is another statement 
				tbody = tbody + tstm + ";;";
				beginofstm = j + 1;
			}
			else tbody = tbody + tstm;
		}
	}
		
	string block = "BEGIN : " + name + "\n" + tbody + "\n" + "END";
	
	return block;	
 }
 
 
 //translates 
 // - begin..end block
 // - triggered/delayed and procedural assign statements
 string translbtdpastm(string str) {
	string tstm;
	if (str.find("begin ")!=std::string::npos && str.find(" end")!=std::string::npos) {
		tstm = translblock (str);
	}
	//translate triggered, delayed, and procedural assign statements
	else if (str.find("=")!=std::string::npos || str.find("@")!=std::string::npos ||
		   str.find("#")!=std::string::npos) {
		str = removechar(';', str);	  //remove ';' at the end of triggered/delayed/procedural assign statement
		tstm = transltdpastm(str); 
	}
	else tstm = str; //ignore all other strings/statements (e.g., $finish, disable)	
		
	return tstm;
 }

 
 //IF _ THEN _ ELSE _
 //body statement can only be begin..end block, delayed/triggered or procedural assignments
 //TODO: nested if-then-else are not supported. NOTE: the stacks and the condition in ifs were initially meant to
 // add support for nested if-then-else 
 string translite (string str){
	std::stack<char> constrs;
	std::stack<string> lastpos;
	int elseend;
	int thenend;
	int ifend;
	
	//by default, the end of string is the end of the 'else' statement. 
	lastpos.push(inttostr(str.length()));
	
	for (int i = str.length(); i >= 0; i--){	

		//push ")" and the position preceded by it. 
		if (str[i] == ')'){
			lastpos.push(")");
			lastpos.push(inttostr(i-1));
		}
		
		//pop up the corresponding ")" and the position preceded by it. 
		if (str[i] == '(')
			if(!lastpos.empty()) {
				lastpos.pop();
				lastpos.pop();
			}
			
		//identify the 'else' keyword, retrieve the end of the 'else' statement, move pointer to non-space char before 'else'
		//replace the 'else' statement with the translated one. 
		if (str[i] == 'e' && str[i-1] == 's' && str[i-2] == 'l' && str[i-3] == 'e' && (str[i-4] == ' ' || str[i-4] == ')') && (str[i+1] == ' ' || str[i+1] == '(')){
			str.replace(i-3, 4, "ELSE");  //thats the notation used 'else' in formal model
			if(!lastpos.empty()) {
				elseend = strtoint(lastpos.top());
				string stm = str.substr(i+1, elseend-i);
				string tstm = " (" + translbtdpastm(stm) + ") "; //add space/parenthesis after/before 'else'
				str.replace(i+1, stm.length(), tstm);
				i = i - 4; //move to space preceded by 'else' keyword 				
				lastpos.push(inttostr(i));//?
				thenend = i; //at space before 'else'
			}			
		}	
		
		//identify the 'then' keyword, and translate statement between 'then' and 'else'.
		//as there can be no closing parenthesis (without its corresponding opening parenthesis), so no need to push/pop integers 
		else if (str[i] == 'n' && str[i-1] == 'e' && str[i-2] == 'h' && str[i-3] == 't' && (str[i-4] == ' ' || str[i-4] == ')') && (str[i+1] == ' ' || str[i+1] == '(')){
			str.replace(i-3, 4, "THEN");  //thats the notation used 'else' in formal model
			string stm = str.substr(i+1, thenend-i);
			string tstm = " (" + translbtdpastm(stm) + ") "; //add space after/before 'then'
			str.replace(i+1, stm.length(), tstm);
			i = i - 4; //move to space preceded by 'then'
			ifend = i;
			} 
			
		//identify the 'if' keyword, and translate statement between 'then' and 'else'.
		//as there can be no closing parenthesis (without its corresponding opening parenthesis), so no need to push/pop integers 
		else if (str[i] == 'f' && str[i-1] == 'i' && (str[i-2] == ' ' || str[i-2] == '(' || i - 1 == 0) && (str[i+1] == ' ' || str[i+1] == '(')){
			str.replace(i-1, 2, "IF");  //that is the notation used 'else' in formal model
			string exp = str.substr(i+1, ifend-i);
			string texp = " " + translexp(exp) + " "; //add space after/before 'then'
			str.replace(i+1, exp.length(), texp);
			i = i - 2; //move to space preceded by 'if'	
			} 
	}
	
  return str;	
 }
 
 //translates 'while' loop statement
 //TODO: simple procedural assignment statement in the body is assumed. 
 //TODO: other loops such as 'forever', 'for', and 'repeat' should be translated to 'while' loop 
 string translwhile (string str){
	std::stack<char> paren;
	int i; 
	int endofwhile;
	int endofbody = str.length();

	if (str.find("while")!=std::string::npos) {
		int loopstart = str.find("while");
		str.replace(loopstart, 5, "WHILE");
		i = loopstart + 5; //char after 'while'
		endofwhile = i;
	}	
	
	//find position of last closing parenthesis - the end of body would be the position of the last
	//closing parenthesis (if there is any, otherwise, its end of of string)
	if (str.find("(")!=std::string::npos)
		if (str.find_first_of("(") < endofwhile){
			int j = str.find_first_of("(");
		
			paren.push('(');
			j = j + 1;   //points to char after '(' and stack is now non-empty 
	
			while (!paren.empty() && j < str.length()){
				if (str[j] == '(')
					paren.push('(');
				if (str[j] == ')')
					paren.pop();
				j = j + 1;
			}	
			endofbody = j - 1; //position just before last closing parenthesis
		}
		
	//go to '('
	while (str[i] != '(' && i < str.length())
			i = i + 1;
	
	if (str[i] == '(') {
		paren.push('(');
		i = i + 1;   //points to char after '(' and stack is now non-empty 
	}
			
    while (!paren.empty() && i < str.length()){
		if (str[i] == '(')
			paren.push('(');
		if (str[i] == ')')
			paren.pop();
		i = i + 1;
	}
	
	//translate statement first
	string body = str.substr(i, endofbody-i);
	str.replace(i, body.length(), translbtdpastm(body));	
		
	str.insert(i, 1, ' ');  //insert space between exp and statement body 
	
	//translate guard expression 
	string guard = str.substr(endofwhile, i - endofwhile);
	str.replace(endofwhile, guard.length(), translexp(guard));
	
	return str;
 }
  
 //translates case statement (with or without name)
 //TODO: only triggered/delayed and procedural assign statements are supported in the body
 //NOTE: blocks could be used instead, but the parser is relying on ';' which is used inside begin..end and in case body
 string translcase (string str) {
	std::stack<char> paren;   //needed to find the last closing parenthesis of guard expression 
	std::stack<char> curle;   //needed to differentiate ':' from the the ones in expressoin
	
	int i, defaultpos; 
	int endofcase;
	string guard;
	string body;
		
	if (str.find("case")!=std::string::npos) {
		int casestart = str.find("case");
		i = casestart + 4; //char after 'case'
		endofcase = i;
	}
		
	//go to '('
	while (str[i] != '(' && i < str.length())
			i = i + 1;
	
	if (str[i] == '(') {
		paren.push('(');
		i = i + 1;   //points to char after '(' and stack is now non-empty 
	}
	
	//go to char after the last closing parenthesis of the guard expression 
    while (!paren.empty() && i < str.length()){
		if (str[i] == '(')
			paren.push('(');
		if (str[i] == ')')
			paren.pop();
		i = i + 1;  //after exit, i points to the char next to last closing parenthesis of guard 
	}	
	
	guard = str.substr(endofcase, i - endofcase);
	guard = translexp(guard);
	
	defaultpos = str.find("default");
	
	int expbegin = i;
	int stmbegin;
	//translate case body
	while (i < defaultpos){
		if (str[i] == '[')
			curle.push('[');
		if (str[i] == ']')
			curle.pop();
		
		//':' is the one between expression and statement (and not inside the expression)
		if (curle.empty() && str[i] == ':'){
			stmbegin = i + 1;
			string exp = str.substr(expbegin, i - expbegin);
			string texp = translexp(exp);
			
			//move to end of statement 
			while (str[i] != ';' && i < defaultpos)
				i = i + 1;
			
			string stm = str.substr(stmbegin, i - stmbegin);
			string tstm = transltdpastm(stm);
			
			//don't include ',' before first case statement 
			if (body == "")
				body = "(" + texp + "," + tstm + ")";
			else body = body + "," + "(" + texp + "," + tstm + ")";
			
			i = i + 1; //move to start of exp after ';'
			expbegin = i;			
		}
		else i = i + 1;
	}
	
	i = i + 7;  //go to end of 'default'
	//go to ':' after 'default'
	while (str[i] != ':' && i < defaultpos)
		i = i + 1;
	i = i + 1;
	
	int endcasepos = str.find("endcase");
	
	string dstm = str.substr(i, endcasepos - i);
	dstm = removechar(';', dstm);  //remove the ';' at the end of default statement
	string tdstm = transltdpastm(dstm);
	
	return "CASE " + guard + "\n [" + body + "] \n" + "DEFAULT : " + tdstm + "\n" + "ENDCASE";	 
 }
 
 
 //translates if-then-else, while, begin..end, triggered/delayed and procedural assign statements.
 //TODO: currently, only triggered/delayed or procedural assign statements are supported
 //    and nested blocks (e.g., nested if-then-else) are not supported. 
 string translstm (string str) {
	string tstm = str;
		
	if (str.find("if ")!=std::string::npos && str.find(" then ")!=std::string::npos &&
		str.find(" else ")!=std::string::npos) {
		tstm = translite (str);
	}
	else if (str.find("while ")!=std::string::npos) {
		tstm = translwhile (str);
	}
	else if (str.find("begin ")!=std::string::npos && str.find(" end")!=std::string::npos) {
		tstm = translblock (str);
	}
	else if (str.find("case ")!=std::string::npos && str.find(" default ")!=std::string::npos &&
		str.find(" endcase ")!=std::string::npos) {
		tstm = translcase (str);
	}
	//translate triggered, delayed, and procedural assign statements
	else if (str.find("=")!=std::string::npos || str.find("@")!=std::string::npos ||
		   str.find("#")!=std::string::npos) {
		 tstm = transltdpastm(str); 
	}
	else tstm = str; //ignore all other strings/statements (e.g., $finish, disable)	
		
	return tstm;
 }
 