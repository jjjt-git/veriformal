#include <iostream>
#include <sstream> 	//istringstream
#include <stack>
#include <fstream>
#include "basicfuns.h"

//integers are stored as vector (value, length) pair. By default, integer are stored as 16-bit value.
string len = "16";

using namespace std;

 //extract Verilog operator between brackets 
 string veriop(int i, string str){
	string op;
	for (int j = i -1 ; j >= 0; j--){
		if (str[j] == '['){
			op = str.substr(j+1, (i-j)-1);
			return op;
		}
	}
	return op;
 }
 
//translate Verilog expression to Isabelle expression
/* translate
	- names
	- unary, binary, logical operations
	- shifts, bit select, index and part select
*/
string translotherexp(string s)
{		
   std::stack<char> constrs;
   string op;
   
    for (int i = s.length()-1; i >= 0; i--){
        
		//insert all constructors on rhs of an operator till first ')'
        if (s[i] == ']'){
			op = veriop(i, s);
			if (isoperator(i, op)){			
				while(!constrs.empty())
					if (constrs.top() != ')' && constrs.top() != ']') {
						char c = constrs.top();
						s.insert(i+1, 1, ' ');
						s.insert(i+1, 1, c);							
						s = lowercase(i+1, s);
						s.insert(i+1, 1, ' ');
						constrs.pop();
					}
					else break; 
			}
			else if (op == ">>" || op == "<<"){  //do nothing and just 
				i = (i - op.length() - 1);  //take curser to closing bracket '['
			}
			//insert constructor 'p' before partselect name 
			else if (ispartsel(op)){
				i = (i - op.length() - 1);  //take curser to closing bracket '['
				
				//go to right most char of name on left of closing brack '['
				while (!validcharid(s[i]))
					i = i - 1; 			
				
				if(validcharid(s[i])){				
					while (validcharid(s[i]) && i >= 0)
						i = i - 1; 			
					i = i + 1;  			//now the pointer is at first char of part select identifier
				
					s.insert(i, 1, ' ');
					s.insert(i, 1, 'p');				
					s = lowercase(i, s);
				}
			}
			//insert constructor 's' before bit select
			else if (isnumber(op)){
				i = (i - op.length() - 1);  //take curser to closing bracket '['
				
				//go to right most char of name on left of closing brack '['
				while (!validcharid(s[i]))
					i = i - 1; 			
				
				if(validcharid(s[i])){				
					while (validcharid(s[i]) && i >= 0)
						i = i - 1; 			
					i = i + 1;  		//now the pointer is at first char of part select identifier
				
					s.insert(i, 1, ' '); 	//pushes that first chart righ, and insert a space
					s.insert(i, 1, 's');	//then constructor 's'			
					s = lowercase(i, s);	//then Isabelle command to make it small
				}
			} 
			//the expression is part select. translate the expresson between the brackets
			else {
				constrs.push(']');
				i = i - 1;
			}
		}  

		//ticky case - translate the expresson between the brackets
		if (s[i] == '['){
            while(!constrs.empty())
				if (constrs.top() != ']') {
					char c = constrs.top();
					s.insert(i+1, 1, ' ');
					s.insert(i+1, 1, c);
					s = lowercase(i+1, s);
					constrs.pop();
				}
				else { 
					constrs.pop();	 //pop up the corresponding opening ']'
					//move pointer to the last char of identifier on the left of '['
					while (!validcharid(s[i]))
					i = i - 1; 			
				
					//move pointer to the first char of identifier on the left of '['
					if(validcharid(s[i])){				
						while (validcharid(s[i]) && i >= 0)
							i = i - 1; 			
						i = i + 1;  			//now the pointer is at first char of part select identifier
				
						s.insert(i, 1, ' '); 	//pushes that first chart righ, and insert a space
						s.insert(i, 1, 'i');	//then constructor 'i' for index			
						s = lowercase(i, s);	//then Isabelle command to make it small
					}
					break;	//pointer just precedes constructor 'i' of part-select expression 
				}			         
        } 
		
		//insert all constructors down '(' till first ')'
        if (s[i] == '('){
            while(!constrs.empty())
				if (constrs.top() != ')') {
					char c = constrs.top();
					s.insert(i+1, 1, ' ');
					s.insert(i+1, 1, c);
					s = lowercase(i+1, s);
					constrs.pop();
				}
				else { 
					constrs.pop();	 //pop up the corresponding opening ')'
					break;
				}			         
        } 
			
		//populate stack with operators notation (e.g., 'b' for binary) and adjust i according to the
		//length of operator minus 2 brackets
		if (s[i] == ']'){
			op = veriop(i, s);   //string on right side of a closing bracket	
			if (isbinop(op))
				constrs.push('b');
			if (islogop(op))
				constrs.push('l');
			if (isunop(op))
				constrs.push('u');
			i = (i - op.length() - 1);
		}
	
	   // string operators = "+,-,*,/,%,&,|,^,~,>,<,=,!";
		
		//insert opening parenthesis  
		if (s[i] == ')')
			constrs.push(')');
		//store 'n' once for a varilabe name. move pointer to left-most char of variable name. 
		if(validcharid(s[i])){	
				int endoftoken = i;
				
				while (validcharid(s[i]) && i >= 0)
					i = i - 1; 	
				string exp = s.substr(i+1, endoftoken - i);				
				if (isnumber(exp)){
					string vector = "\\<^sub>v(" + exp + "," + len + ")";
					s.replace(i+1, exp.length() - i, vector);
				}
				else 
					constrs.push('n');   
				
				i = i + 1;  
			}
	
    }
	
	//insert all remaining constructors
    while(!constrs.empty()) {
		char c = constrs.top();
		s.insert(0, 1, ' ');
		s.insert(0, 1, c);				
		s = lowercase(0, s);
		constrs.pop();
	}		     
     
   return s;
}


//translates conditional expression (the three parts are translated and constructor 'l' is put on right)
//TODO: nested conditionals are NOT supported. 
string translcondexp (string str){	
	std::stack<char> cond;  	//stack for detecting conditional constructor		
	char prevnotation;			//stores previous conditional notation ':' or '?'	
	int prevnotpos = str.length();   
	bool partselect = false; 	//detects if a ':' is part of conditional and not bit part select
	string translated;
	string exp;	
	
	for (int i = str.length()-1; i >= 0; i--){		
		if (str[i] == ']') 
			partselect = true;
		if (str[i] == '[')
			partselect = false;
						
		if (str[i] == '?' || (str[i] == ':' && !partselect) || i == 0)  {				  
			//translated the expressions in conditional expression
			if (str[i] == ':'){
				exp = str.substr(i+1, prevnotpos - 1);	
				translated = translotherexp(exp);
				str.replace(i+1, exp.length(), translated);
				prevnotpos = i;
			} else if (str[i] == '?'){
				exp = str.substr(i+1, prevnotpos - (i+1));	
				translated = translotherexp(exp);		
				str.replace(i+1, exp.length(), translated);
				prevnotpos = i;
			} else if (i == 0){
				exp = str.substr(0, prevnotpos - 1);	
				translated = translotherexp(exp);
				str.replace(0, exp.length(), translated);
			}
			
									
			//put the constructure 'c' for conditional at the end (right side)
			//NOTE: this in some cases do not put constructor, hence instead "\\<^sub>c" is appended at front when translated string is returned
			while(!cond.empty())
				if (cond.top() != ')') {					
					char c = cond.top();
					if (i == 0) {
						str.insert(i, 1, ' ');
						str.insert(i, 1, 'c');							
						str = lowercase(i, str);
						str.insert(i, 1, ' ');
					} else 
					{							
						str.insert(i+1, 1, ' ');
						str.insert(i+1, 1, 'c');							
						str = lowercase(i+1, str);
						str.insert(i+1, 1, ' ');						
					}
					cond.pop();
				}
				else {cond.pop(); break;}  			
		}	
		
		if (str[i] == ')' || str[i] == '?')
			cond.push(str[i]);
		//erase notations '?' and ':'
		if (str[i] == '?' || str[i] == ':')
			str.replace(i, 1, " "); 
	}	
	return "\\<^sub>c" +str;   //append conditional constructor
}

 //enclose Verilog operators in brackets (e.g., ++ => [++]). 
 string addbrackets (string str){
	string special = "+,-,/,%,*,<,>,=,!,&,|,^,~"; //no spaces 
	bool right = false;
	
	for (int i = str.length()-1; i >= 0; i--){
		//add right bracket
		if(!right & findchar(str[i], special)) {
			 str.insert(i+1, 1, ']');
			 right=true;
		}
		//add left bracket
		if(right & !findchar(str[i], special)) {
			str.insert(i+1, 1, '[');
			 right=false;
		}				
	}	 
	return str;
 }   
 
//translates an expression to Isabelle (VeriFormal) expressions 
string translexp (string str) {
	string translated;
	
	//enclose Verilog operators (except ? and :) in brackets
	string bracketed = addbrackets(str);
			
	if (str.find("?") !=std::string::npos) {
		translated = translcondexp(bracketed);	
	}
	else 
		translated =  translotherexp(bracketed);
	
	return translated;
}

/*
int main(){
	
	string s = "23 - (R1 +2y34)";
	//cout<<"Brackets:"<<addbrackets(s)<<endl;
	
	cout<<"Translated:"<<translexp(s)<<endl;
	
	return 0;	
} 
*/
