#include <iostream>
#include <sstream> 	//for istringstream
#include <stack>
#include <fstream>

#include "basicfuns.h"
#include "translexp.h"

using namespace std;


//create a file 'names.txt' which store set of identifiers used in the declarations of
//a Verilog module. This list of constructors will be used to define the type 'name' in 'Syntax.thy'
int addidinfile (string str){
	ofstream filehandle;
	
	//read VeriCert data to buffer
	std::ifstream t("names.txt");    
	std::stringstream buffer;
	buffer << t.rdbuf();
	
	//append string "VeriCert output: \n" before data. 
	filehandle.open ("names.txt");
	if (buffer.str() == "")
		filehandle << str;
	else 
		filehandle << buffer.str() + " | " + str;
    filehandle.close();
	
	return 0;
}
//translates declaration
//declarations and net declaration with assignment are supported. For the later case, 
//a delcaration and a continous assignment are created. (e.g. input x = y; as input produces:
//input [0:0] [\<^sub>n x], assign # -1 [\<^sub>n W1] = \<^sub>b  \<^sub>n X [+] \<^sub>n Y )
 string transldecl (string str){
	// str = removechar(';', str);
	//Verilog declaration types 
	string input = "input";
	string output = "output";
	string inout = "inout";
	string wire = "wire";
	string reg = "reg";
				
	string type, width, names;
	string contass = "";
	
	int endoftype = 0;
	int endofwidth = 0;
	int beginofwidth = 0;
	
	//erase extra spaces at the end of declaration (if any)
	for (int i = str.length() - 1; i >= 0; i--){
		if (str[i] != ' ') {
			str = str.substr(0, i + 1);
			break;			
		}
	}
	
	//get the type of declaration and end of the type keyword
	if (str.find(input)!=std::string::npos){
		endoftype = str.find(input) + input.length(); 
		type = input;
	}
	 
	else if (str.find(output)!=std::string::npos) {
		endoftype = str.find(output) + output.length(); 
		type = output;
	}
	
	else if (str.find(inout)!=std::string::npos) {
		endoftype = str.find(inout) + inout.length(); 
		type = inout;
	}
	
	else if (str.find(wire)!=std::string::npos) {
		endoftype = str.find(wire) + wire.length(); 
		type = wire;
	}
	
	else if (str.find(reg)!=std::string::npos) {
		endoftype = str.find(reg) + reg.length(); 
		type = reg;
	}
	
	//skip spaces till first non-space char
	int i = endoftype;
	while(str[i] == ' ' && i < str.length())
	    i = i + 1;
	
	//if vector, find start and end of string [n2:n1]
	//NOTE: it is assumed no parenthsis are used 
	bool scalar = true;
	if (str[i] == '[') {
		scalar = false;
		beginofwidth = i;
		while (str[i] != ']' && i < str.length())				
			i = i + 1;			
		endofwidth = i + 1;			
	} 
	
	//get width (for scalar add "[0:0]") and get identifier 
	if (scalar) {
		width = "[0:0]";
		names = str.substr(endoftype, str.length() - endoftype);
	}
	else {
		width = str.substr(beginofwidth, endofwidth - beginofwidth);	
		names = str.substr(endofwidth, str.length() - endofwidth);
	}

	names = removechar(' ', names); //erase extra spaces at the begining and end
	
	//append lower case Isabelle command followed by name constructur 'n'
	string exp; 
	if (!(names.find("=")!=std::string::npos)) {			//if only declaration (no assignment) 		
		if (names.find(",")!=std::string::npos) {
			istringstream iss(names);
			std::string token;
		
			//split by ','
			while (std::getline(iss, token, ',')) {
				addidinfile(token);  //add identifier to the names (constructors) list
				exp = exp + token + ",";
			}
			exp.erase (exp.length()-1,1);   //erase final ','
		} else {
			exp = names; 
			addidinfile(names);  //add identifier to the names (constructors) list 			
		}
	}
	else {
		string rhs = names.substr(names.find("=")+1, names.length() - names.find("="));
		//cout <<"rhs:"<<rhs<<endl;
		exp = "\\<^sub>n" + names.substr(0, names.find("="));   //it will always be a single name
	    contass = ", \nassign # -1 [" + exp + "] = " + translexp(rhs);		
	}
	
	//cout<<"exp:"<<exp<<","<<endl;
	
	//combine the three parts together
	exp = "[" + exp + "]";  
	str = type + " " + width + " " + exp;
	str = str + contass;  //add the extra continous assignment (if any was created above)
	
	return str;
}
