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

//#include "translmodule.h"
//this was added to re-use functions 'validtopchar' and 'nextkeyword', 
//however, compiler was complain, hence were redefined in this file below)



using namespace std;

string getgenvar (string str) {
	int genvarpos;
	int endofgenvarstm;
	string genvar;
	

    //erase comments if any 
	str = erasecomments (str);	

	if (str.find("genvar")!=std::string::npos) {
		genvarpos = str.find("genvar");

		
		//separate the rest of code after 'genvar' 
		string rest = str.substr(genvarpos+6); //get from 'genvar' to the end
		
		//get end of genvar statement (position of semicolon)
		if (rest.find(";")!=std::string::npos)
			endofgenvarstm = rest.find_first_of(";");
		
		//get the 'genvar' value
		genvar = rest.substr(1, endofgenvarstm-1); 
		
		return genvar;
	}
	 
 return "\n No genvar found! \n"; 
 }
 
 
//Gets the maximum limit of genvar value used in generate 'for' loop.
//NOTE: currently supports only number (and not variable as value)
int findgenvarvalue (string genstm) {
	string value = " ";
	string keyword = " ";
	int ltpos = 0;
	int semicolpos = 0; 
	
	for (int i=0; i<genstm.length(); i++) {
		if (validcharid(genstm[i])) {
			keyword = keyword + genstm[i];
			continue;
		}
		else if (isverkeyword (keyword) & keyword == " for") {
				for(int j=i; j<genstm.length(); j++) {
					if (genstm[j] == '<') {
						ltpos = j;
							for(int k=j; k<genstm.length(); k++) {
								if (genstm[k] == ';') {
									semicolpos = k;
									break;
								}
							}					
					}				
				}				
			break;		
		}				
		else keyword = " ";
	}
		
	value = genstm.substr(ltpos+1, semicolpos-ltpos-1);
	
	return strtoint(value);
}

//get code between 'begin' and 'end' in generate statement
string getgenbody (string str) {
	int beginpos = 0;
	int endofbegin = 0;
	string body;
	
	if (str.find("begin")!=std::string::npos) {
		beginpos = str.find("begin");
		endofbegin=beginpos+5;
	}
	 
	body = str.substr(endofbegin, str.length()-endofbegin-4); //get code between begin and end
	return body;
}

string repeatgenbody (string str, string genvar, int genvarvalue) {
	string identifier = " ";
	string temp;
	string code = " ";
	
	for (int j=0; j<genvarvalue; j++) {
		temp = " ";	
		for (int i=0; i<str.length(); i++) {
			if (validcharid(str[i])) {
				identifier = identifier + str[i];
			} //'identifier' is either an identifier, number or keyword
			else { 
				identifier = removechar(' ', identifier);  //remove the initial ' '
				if (identifier == genvar)    			//replace 'genvar' with loop value (ith occurence)
					temp = temp+inttostr(j) + str[i];				
				else if (isverkeyword (identifier) | isnumber(identifier) | isverilogid(identifier))  //keep keyword, number, variables
					temp = temp + identifier + str[i];				
				else temp = temp + str[i]; 				//keep all other characters (e.g., special characters)
				
			    identifier = " ";
			}
		}		
		code = code + "\n" + temp;
	}
	
	return code+"\n";	
}


//repeat a declaration with array to sequence of variables
//repeats 'input [3:0] bus[2:0]' three times as 'input [3:0] bus0, input [3:0] bus1, ...'
//returns statement without array unchanged. 
string repeatdeclaration (string str) {
	string identifier = " ";
	string temp;
	string code = str;
	string widthstr = " ";
	int width=0;
	int start, end, endofid;
	
		for (int i=0; i<str.length(); i++) {
			if (validcharid(str[i])) {
				identifier = identifier + str[i];
			} //'identifier' is either an identifier, number or keyword
			else { 
				identifier = removechar(' ', identifier);  //remove the initial ' ' in initialized 'identifier'
				if (isverilogid(identifier) & !isverkeyword(identifier))  {//if identifier 
					endofid = i - 1; //go back to end of the identifier
						
					//cout<<"\nID:"<<identifier<<":"<<i<<":"<<str[i]<<":"<<str;	
					
					while(str[i] == ' ') //skip spaces after the identifier-if any
						i++;
					if (str[i] == '[') {
						code = " ";
						i = i + 1; //move to char next to [
						start = i;
						while(str[i] != ':') // come to : inside brackets
							i++;
						end = i-1;
						temp = str.substr(0, endofid+1); //get the declaration till end of identifier
						widthstr = str.substr(start, end-start+1);
						width = strtoint(widthstr);	 //get width of the array	
						//cout<<"\nWidth: "<<widthstr<<"\n";
						//repeat top statement with array
						for(int j=0; j<=width; j++) {
							code = code + "\n"+ temp + inttostr(j)+";";							
						}
					}
				}
				identifier = " ";
			}
		}	
		
		return code;
}

//translate arrays to list of variables
string transformarrays (string str) {
	string identifier = " ";
	string temp;
	string code = " ";
	int width=0;
	int start, end;
	string top;
	string repeated;
	
		for (int i=0; i<str.length(); i++) {
			if (validcharid(str[i])) {
				identifier = identifier + str[i];
			} //'identifier' is either an identifier, number or keyword
			else { 
				identifier = removechar(' ', identifier);  //remove the initial ' ' in initialized 'identifier'
				//if declaration keyword found, extract declaration
				if (identifier == "input" | identifier == "output" | identifier == "wire" | identifier == "reg")  { 
					start = i-identifier.length();  //go to start of keyword
					while(str[i] != ';') //go to end of statement ;
						i++;
					end = i;
					top = str.substr(start, end-start+1);
					repeated = repeatdeclaration(top);
					code = code.substr(0, code.length()-identifier.length());  //remove repetition. get the letters of keyword added by 'code = code + str[i]'
					code = code + repeated + "\n";  //top statements, with arrayed statement repeated. 
					identifier = " "; //prepare for next search
					i = i + 1; //skip the end semicolon
				}
			}
			code = code + str[i]; //non-declaration top statements are unchanged. 
		}
	return code;
}
 
 //gets sequence of all array identifiers indexed by 'genvar' in the generate statement
string getgenindexedids (string str, string genvar, int genvarvalue) {	
	string identifier = " ";
	string temp;
	string code = " ";
	string previd = " ";
	
	for (int j=0; j<genvarvalue; j++) {
		for (int i=0; i<str.length(); i++) {
			if (validcharid(str[i])) {
				identifier = identifier + str[i];
			} //'identifier' is either an identifier, number or keyword
			else { 
				identifier = removechar(' ', identifier);  //remove the initial ' '
				if (identifier == genvar & str[i] == ']')  {   //if genvar is an index, put value of index, enclose in brackets and add to the sequence. 
					temp = temp + "," + previd+"["+inttostr(j) + str[i];
				} 
				else {
					previd = identifier;  
				}
				identifier = " ";
			}
		}			
	}	
	return temp.substr(1,temp.length());  //remove the initial ','
}

//gets a list of array variables, separated by comma
string getarrayids (string module) {
	string identifier = " ";
	string arrayids = " ";
	bool typedetected = false;
	
	for (int i=0; i<module.length(); i++) {
			if (validcharid(module[i])) {
				identifier = identifier + module[i];
			} //'identifier' is either an identifier, number or keyword
			else { 
				identifier = removechar(' ', identifier);  //remove the initial ' ' in initialized 'identifier'
				if (typedetected & isverilogid(identifier) & identifier.length()>0) {		//if inside a declaration and identifier found AFTER input type.
					while(module[i] == ' ') //skip spaces after the identifier-if any
						i++;
					if (module[i] == '[')   //if a bracket is found, the identifier is an array identifier. 
						arrayids = arrayids + ',' + identifier;					
					typedetected = false;
				}
				
				if (identifier == "input" | identifier == "output" | identifier == "wire" | identifier == "reg")  //if type keyword
					typedetected = true;
				
				identifier = " "; //prepare for next keyword or identifier				
			}
	}	
	
	if (arrayids.length() <= 2)
		return " ";
	else
		return arrayids.substr(2, arrayids.length()-2); //remove the initial space and comma	
}

string translindexids(string module, string arrayids, string indexedids) {

	int prevpos=0;
	int curpos=indexedids.length();
	int openbracket = 0;
	string indexedid;
	string renamedid;
	string identifier = " ";
			
	for(int i=0; i<indexedids.length(); i++) {
		if(indexedids[i] == ',' | i==indexedids.length()-1) {
			if (i<indexedids.length()-1)  //to capture the last indexed id.
				curpos=i;
			
			indexedid = indexedids.substr(prevpos, curpos-prevpos);
			if (indexedid.find("[")!=std::string::npos) {
				openbracket = indexedid.find("[");
				
				identifier = indexedid.substr(0, openbracket);
		
				renamedid = removechar ('[', indexedid);
				renamedid = removechar (']', renamedid);
				//replace only array variables (if the identifier exists in the list of array identifiers)
				if (arrayids.find(identifier)!=std::string::npos)
					module = replacesubstr (module, indexedid, renamedid);
			
			}
			
			prevpos=i+1;		
		}
	}
	
	return module;
}

//Get first line (module declaration) of module
string getmodulefirstline(string module) {
	
	int modulepos;
	string firstline = " ";
	
	if (module.find("module")!=std::string::npos) {
		modulepos = module.find("module");
	
		firstline = module.substr(modulepos, module.find_first_of(";") -modulepos);
	}
	return firstline;
}




//translate generate statement, remove genvar, translate vector to list of variables
string translgenerate (string str) {
	string genvar; 
	string genbody;
	string module = str;
	string generatestm;
	string repeated;
	string genindexedvar;	//indexed variables in generated statement, with brackets
	string arrayids;        //indexed identifiers, taken from declarations
	string generate;
	int genvarvalue = 0;
	int generatepos;
	int endgenpos;
	
	
	//cout<<"\nArary ids:" <<getarrayids (module);
	arrayids = getarrayids (module);
	//cout<<"\n array ids: "<<arrayids;
	 
	//if generate statement exists, start transform arrays (if any) to variables	
	if (module.find("genvar")!=std::string::npos | module.find("generate")!=std::string::npos) 
		module = transformarrays (module);	
		
	//look for generate statement and translate it (if any)
	if (module.find("generate")!=std::string::npos) {
		generatepos = module.find("generate");
				
		if (module.find("endgenerate")!=std::string::npos)
			endgenpos = module.find("endgenerate");
		
		generatestm = module.substr(generatepos+9, (endgenpos-generatepos-9));	 //1-get generate statement without 'generate' and 'endgenerated' keywords
		generate = module.substr(generatepos, endgenpos-generatepos+11);  		 //2-get generated statement with 'generate' and 'endgenerated' keywords
	    genvarvalue = findgenvarvalue (generatestm);							 //3-get generate variable maximum limit value in loop
	    genbody = getgenbody (generatestm);										 //4-get generated body (statement after for loop)
		genvar = getgenvar (module);											 //5-get generate variable
	    repeated = repeatgenbody (genbody, genvar, genvarvalue);				 //6-repeat generated body (got in 4) as many times as max limit (got in 3)
		module = replacesubstr (module, generate, repeated);					 //7-replace generate (got in 2) with repeated coded (got in 6)
		module = replacesubstr (module, "genvar "+genvar+";", " ");				 //8-remove 'genvar variable;' statement
		genindexedvar = getgenindexedids (genbody, genvar, genvarvalue);		 //9-get indexed variables
		module = translindexids(module, arrayids, genindexedvar);				 //10-replace indexed variables (replace test[2] with test2)
	}
	
    //cout<<"\nMODULE: "<<module <<"\n\n";
		
	return module;
}