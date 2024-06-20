#include <iostream>
#include <sstream> 		//istringstream
#include <stack>
#include <fstream>
#include <string> 		//to_string, stoi
#include <algorithm>    // std::min

#include "basicfuns.h"
#include "flattening.h"
#include "translexp.h"
#include "transldecl.h"
#include "translca.h"
#include "translstm.h"




using namespace std;

bool validtopchar(char c){
	string valid = "abcdefghijklmnopqrstuvwxyz";
	
	for (int i = 0; i <=valid.length(); i++)
		if (c == valid[i])
			return true;	
	return false;	
}


//returns the position (first char position) of nearest keyword 
//used to parse the keyword and its bod (e.g., initial body)
//max is the default maximum (size of string)
//TODO: replace with a function that finds min of n-numbers
int nextkeyword (string str, int max) {	
	int inputpos = max;
	int outputpos = max;
	int inoutpos = max;
	int wirepos = max;
	int regpos = max;
	int assignpos = max;
	int initialpos = max;
	int alwayspos = max;
		
	if (str.find("input ")!=std::string::npos)
		inputpos = str.find("input ");
	if (str.find("output ")!=std::string::npos)
		outputpos = str.find("output ");
	if (str.find("inout ")!=std::string::npos)
		inoutpos = str.find("inout ");
	if (str.find("wire ")!=std::string::npos)
		wirepos = str.find("wire ");
	if (str.find("reg ")!=std::string::npos)
		regpos = str.find("reg ");	
	if (str.find("assign ")!=std::string::npos)
		assignpos = str.find("assign ");
	if (str.find("initial ")!=std::string::npos)
		initialpos = str.find("initial ");	
	if (str.find("always ")!=std::string::npos)
		alwayspos = str.find("always ");
	
	int minofall =  min(inputpos, outputpos);
	minofall = min(minofall, inoutpos);
	minofall = min(minofall, wirepos);
	minofall = min(minofall, regpos);
	minofall = min(minofall, assignpos);
	minofall = min(minofall, initialpos);
	minofall = min(minofall, alwayspos);
	
	return minofall; 
}

//checks if a word is a top type keyword for declaration
bool istype (string str){
	string types = "input,output,inout,wire,reg";
	
	if (types.find(str)!=std::string::npos)
		return true;
	
	return false;	
}
	

//translates the @(), @_ or #_ part after always. The rest of body is translated using
//'translstm' function. The functions 'transltdstm' or 'transltdpastm' can NOT be used, as
//none of them support begin..end blcok, while the above functions have been defined
//to support triggered, delayed, or procedural assign statements inside begin..end block.
//TODO: remove this function, when support for nested statements is added
string translalwbody (string str){
	int i = 0;
	while (str[i] == ' ' && i < str.length())
		i = i + 1;
	
	//case: # 23 _
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
		
		//separate the statement body after #num 
		string stm = str.substr(i, str.length());
				
		//translate the rest of statementent body and place it back into the string
		str.replace(i, stm.length(), translstm(stm));
	}
	
	//case: @(_) _  
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
			//part of statement after @()
			string rhs = str.substr(i+1, str.length() - i);
			
			//separate sensitivity list 
			string sl = lhs.substr(begin, i - begin);
			
			//translate sensitivity list 
			lhs = lhs.replace(begin, sl.length(), translsl(sl));
			
			//translate body after @() and replace it 
			str  = lhs + "\n" + translstm(rhs);
		}
		//case: @identifier _
		else {
			int begin = i;
			while (validcharid(str[i]))
				i = i + 1;
			
			string lhs = str.substr(0, i); 
			string rhs = str.substr(i, str.length() - i);
			
			string sl = lhs.substr(begin, i - begin);
			
			lhs = lhs.replace(begin, sl.length() + 2, "("+translsl(sl)+")");  //enclose in parenthesis
			
			str  = lhs + "\n" + translstm(rhs);
		}
	}
	
	return str;
}

//translates a Verilog module to Isabelle formal model
//assumes, Verilog top statements and comments
//Verilog statements not modelled MUST not be included
//(e.g., $display, ...)
 string translmodule (string str){
	string keyword;
	string translatedmod = " ";
	string topstm;
	string rest = str;
	
	int begofkeyword;
	int endofbody;
	
	//erase comments if any 
	str = erasecomments (str);	
	
	//skip initial spaces
	for (int j = 0; j < str.length(); j++){		
	
		//find position of next Verilog top keyword (e.g., input, initial..)
		rest = str.substr(j, str.length() - j);
		begofkeyword = j + nextkeyword(rest, rest.length());
		j = begofkeyword;		
		
		//go to end of keyword
		while (validtopchar(str[j]) && j < str.length())
			j = j + 1;
		
		//extract keyword 
		keyword = str.substr(begofkeyword, j - begofkeyword);
		
		//translate declarations 
		if (keyword == "input" || keyword == "output" || keyword == "inout" || keyword == "wire" || keyword == "reg") {
			rest = str.substr(j, str.length() - j);
			endofbody = j + nextkeyword(rest, str.length());
			topstm = str.substr(begofkeyword, endofbody - begofkeyword);  //including ';'
			topstm = removechar(';', topstm);  //remove end ';'
			if (translatedmod == " ")
				translatedmod = transldecl(topstm);  //translate declarations
			else 
				translatedmod = translatedmod + ",\n" + transldecl(topstm);  //translate declarations
			j = endofbody - 2;  	//position next keyword - 2. (for loop will increment by 1)
		}		
		//translate continuous assignments 
		else if (keyword == "assign"){
			rest = str.substr(j, str.length() - j);
			endofbody = j + nextkeyword(rest, str.length());
			topstm = str.substr(begofkeyword, endofbody - begofkeyword);  //including ';'
			topstm = removechar(';', topstm); // remove end ';'
			if (translatedmod == " ")
				translatedmod = translca(topstm);  //translate declarations
			else 
				translatedmod = translatedmod + ",\n\n" + translca(topstm);  //translate declarations
			j = endofbody - 2;  //position next keyword - 2. (for loop will increment by 1)
		} 
		//translate initial blcok 
		else if (keyword == "initial"){
			rest = str.substr(j, str.length() - j);
			endofbody = j + nextkeyword(rest, str.length());
			int begofbody = begofkeyword + keyword.length();			
			topstm = str.substr(begofbody, endofbody - begofbody);  //statement after initial/always keyword
			if (translatedmod == " ")
				translatedmod = keyword + "\n " + translstm(topstm);  //translate declarations
			else 
				translatedmod = translatedmod + ",\n\n" + keyword + "\n " + translstm(topstm);  //translate declarations
			j = endofbody - 2;  //position next keyword - 2. (for loop will increment by 1)
		} 
		//translate always block 
		else if (keyword == "always"){
			rest = str.substr(j, str.length() - j);
			endofbody = j + nextkeyword(rest, str.length());
			int begofbody = begofkeyword + keyword.length();			
			topstm = str.substr(begofbody, endofbody - begofbody);  //statement after initial/always keyword
			if (translatedmod == " ")
				translatedmod = keyword + " (" + translalwbody(topstm) + " )";  //translate declarations
			else 
				translatedmod = translatedmod + ",\n\n" + keyword + " (" + translalwbody(topstm) + " )";  //translate declarations
			j = endofbody - 2;  //position next keyword - 2. (for loop will increment by 1)
		} 
		//keep other chars 
		else 
			translatedmod = translatedmod + str[j];
	}
	 
	 return "[" + translatedmod + "]";
 }
 
 /*
 int main(){
	 
	 cout<<"translated module:"<<translmodule("module others; input one; output two; endmodule")<<endl;
	 
	 return 0;
	 
 } */
 