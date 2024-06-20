#include <iostream>
#include <sstream>
#include <string>
//#include <list>
//#include <stack>
#include "translexp.h"
#include "basicfuns.h"


using namespace std;


 //translate assignment without delay (of the form {x, y} = exp)
 string wfassign (string str){
	string lhs, rhs;
	
	str = removechar('{', str);
	str = removechar('}', str);
	str = removechar(' ', str);	 
	
	//separate lhs and rhs 
	lhs = str.substr(0,str.find_first_of("="));
	rhs = str.substr(str.find_first_of("=") + 1);
		
	//reverse lhs side string and enclose in[] 
	lhs = reversewords(lhs);
	
	rhs = translexp(rhs);

	return lhs + "=" + rhs;
 }
 
 
 
//translate string to Isabelle assign statement
 string translca (string str) {
	string assignment;
	int endofassign = 0;
	int beginofdelay = 0;
	int endofdelay = 0;	
	
	//get the type of declaration and end of the type keyword
	if (str.find("assign")!=std::string::npos){
		endofassign = str.find("assign") + 6; 
	}
	
	//skip spaces till first non-space char
	int i = endofassign;
	while(str[i] == ' ' && i < str.length())
	    i = i + 1;
	
	//find delay # _
	//NOTE: it is assumed no parenthsis are used 
	string delay = "# -1 ";  //default (no) delay (# -1)
	if (str[i] == '#') {
		beginofdelay = i;
		i = i + 1;    
		//skip spaces (go to next non-space char)
		while(str[i] == ' ' && i < str.length())
			i = i + 1;
	
		//got to end of number
		while (isdigit(str[i]) && i < str.length())				
			i = i + 1;			
		i = i + 1;
		delay = str.substr(beginofdelay, i - beginofdelay);
		assignment = str.substr(i, str.length() - 1);
	}
	else   
		assignment = str.substr(endofassign, str.length() - endofassign);
	
	//translate the assignment part
	str = wfassign(assignment);

	return "assign " + delay + str;
 }
