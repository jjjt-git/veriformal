 #include <iostream>
#include <sstream> 	//istringstream
#include <fstream>

#include "basicfuns.h"

 
///////////////////////////////////////////////////////////////////////////////////////

 //return list of identifiers (separated by ',') of type 'input' in a module body 
 //TODO: input declarations with cont assignment in same line is currently not supported in an 
 //instantiated module;
 string inputports(string str){
	//Verilog declaration types 
	string input = "input";				
	string rest, names;
	string ports = "";
	
	rest = str;
	
	int beginofnames = 0;	
	
	int i = 0;
	while(i < str.length()) {
		
		//get the list of identifiers with type 'input'		
		if (rest.find("input")!=std::string::npos) {
			i = i + rest.find("input") + 5;  //move to the char after next 'input'
			
			//skip spaces till first non-space char
			while(str[i] == ' ' && i < str.length())
				i = i + 1;
	
			//skip width (if any) and spaces before first identifier
			if (str[i] == '[') {
				while (str[i] != ']' && i < str.length())				
					i = i + 1;	
				i = i + 1; //char next to ']'
				//skip spaces (if any) after ']'
				while(str[i] == ' ' && i < str.length())
					i = i + 1;		
			}
	
			beginofnames = i;
	
			//go to next ';' (end of declaration)
			while(str[i] != ';' && i < str.length())
				i = i + 1;	
	
			//get names in a single declaration
			names = str.substr(beginofnames, i - beginofnames);
			names = removechar(' ', names);  //remove spaces (e.g., those before and after an identifier)
			i = i + 1;  //char after ';'
			rest = str.substr(i, str.length() - i);  //search the rest of body
				
			//split names in the declaration (if more than one identifiers in one declaration)
			if (names.find(",")!=std::string::npos) {
				istringstream iss(names);
				std::string token;
	
				//split by ','
				while (std::getline(iss, token, ','))
					if (ports == "")
						ports = token;
					else ports = ports + "," + token;
			}
			else ports = ports + "," + names;
		}
		else return ports;
	}
		
	return ports;	
 }
 
 
 //checks if a port is of type input (is in a list of ports, separated by ',')
 bool isinputport (string port, string inputs){	
	//find if port has been defined with 'input' type
	if (inputs.find(",")!=std::string::npos) {
		istringstream iss(inputs);
		std::string token;
	
		//split by ','
		while (std::getline(iss, token, ','))
			if (port == token)
				return true;
	}
	else if (port == inputs)  //just one identifier in inputs
		return true; 
	else return false;
	
	return false;
 }
 
 //create a continuous assignment for each input port (from input port in parent module to corresponding 
 //input port in instantiated module)
 string connectinputs (string sports, string dports, string topmodule){
	string sourceports [20] = {};
	string destports [20] = {};
	string inputs = inputports(topmodule);
	
	string contassigns;
	int i;
	
	i = 0;
	sports = removechar(' ', sports);  //erase spaces
	//store source (caller) ports in a string array
	if (sports.find(",")!=std::string::npos) {
		istringstream iss(sports);
		std::string token;
	
		//split by ','
		while (std::getline(iss, token, ',')){
			sourceports[i++] = token;
		}
	}
	else sourceports[i] = sports;
	
	i = 0;
	dports = removechar(' ', dports);  //erase spaces
	//store destination (callee) ports in a string array
	if (dports.find(",")!=std::string::npos) {
		istringstream iss(dports);
		std::string token;
	
		//split by ','
		while (std::getline(iss, token, ',')){
			destports[i++] = token;
		}
	}
	else destports[i] = dports;
	
	//create list of continuous assigns for each input port (assignment to instantiated module port)
	i = 0;
	while (sourceports[i] != ""){
		if (isinputport(sourceports[i], inputs)) 
			contassigns = contassigns + "assign " + destports[i] + " = " + sourceports[i] + "; ";
		i = i + 1;
	}
	//cout<<"Input connecting assignments: "<<contassigns<<endl;	
	
	return contassigns;	 
 }
 
 //create a continuous assignment for each output port (from instantiated NON-input to corresponding 
 //input port in parent module NON-input port). In an instantiated module, it can change identifiers
 //of type, both, input and NON-input. 
 string connectoutputs (string sports, string dports, string topmodule){
	string sourceports [20] = {};
	string destports [20] = {};
	string inputs = inputports(topmodule);
	
	string contassigns;
	int i;
	
	i = 0;
	sports = removechar(' ', sports);  //erase spaces
	//store source (caller) ports in a string array
	if (sports.find(",")!=std::string::npos) {
		istringstream iss(sports);
		std::string token;
	
		//split by ','
		while (std::getline(iss, token, ',')){
			sourceports[i++] = token;
		}
	}
	else sourceports[i] = sports;
	
	i = 0;
	dports = removechar(' ', dports);  //erase spaces
	//store destination (callee) ports in a string array
	if (dports.find(",")!=std::string::npos) {
		istringstream iss(dports);
		std::string token;
	
		//split by ','
		while (std::getline(iss, token, ',')){
			destports[i++] = token;
		}
	}
	else destports[i] = dports;
	
	//create list of continuous assigns for each NON-input port (assignment to top module port)
	i = 0;
	while (sourceports[i] != ""){
		if (!(isinputport(sourceports[i], inputs))) 
			contassigns = contassigns + "assign " + sourceports[i] + " = " + destports[i] + "; ";
		i = i + 1;
	}
	
	return contassigns;	 
 }
 
 
 //get input text file, and erase newline chars '\n'
 //all the functions assume, there is no '\n'
 //NOTE: the comments must be erased before calling this function, as the 'erasecomments' 
 //function is relying on end of line char 
 string formatinput (string input){
	string result;
	std::ifstream t(input.c_str());    
	string token;
	while (t >> token)
		result = result + " " + token;
	return result;
 }

 
 //get module ports 
 string getports (string str){
	 int modulepos;
	 int openpos , closepos;
	 string ports = "";
	 string firstline = "";	 
	 
	if (str.find("module")!=std::string::npos) {
		modulepos = str.find("module");
	
		firstline = str.substr(modulepos, str.find_first_of(";") -modulepos);
	
		if (firstline.find("(")!=std::string::npos) {
			openpos = firstline.find("(");
			if (firstline.find(")")!=std::string::npos) 
				closepos = firstline.find(")");
		
			ports = firstline.substr(openpos+1, closepos-openpos-1);
		}
	}
	
	return ports;	 
 }
 
 string gettoplist (string str){
	int firstlineend ;
	int endmodpos;
	string toplist = str;
	
	if (str.find("module")!=std::string::npos && str.find(";")!=std::string::npos) {
		firstlineend = str.find_first_of(";");
	
		if (str.find("endmodule")!=std::string::npos)
			endmodpos = str.find("endmodule");
	
		toplist = str.substr(firstlineend+1, endmodpos-firstlineend-1);
	}
	
	return toplist;
 } 
 
//flattening: gets a module (without '\n' chars) and replaces module instantiation with continuous assigns for
//each input + top list (body) of instantiated module + continuous assigns for each output in the ports 
 string flattening (string str){
	string topmodule = str;	
	string calleports;
	string callerports;
	string calletoplist;
	string submodid; 	
	string flattened;
	
	int submodidend;
	int endofports;
	int idend;
	
	int instanceend; 	//end of module instance line
	int instancebeg;	//begin of module instance line
	
	int size = str.length() - 1;
	//tokenize module instantiation line, into
	//ports, modinstid, submodid 	
	string locports; 
	for (int i = size; i>=0; i--) {
		if (str[i] == ';'){
			instanceend = i; 
			int j = i - 1;
			while (str[j] == ' ')
				j = j - 1;
			
			if (str[j] == ')') {
				j = j - 1;
				endofports = j;
				while (str[j] != '(')
					j = j - 1;
				
				//TODO: a further check to verify each of the local port (string) is of type net (to roll out any other string)
				locports = str.substr(j+1, endofports - j);
				
				j = j - 1;
				//skip spaces on left of '('
				while (str[j] == ' ')
					j = j - 1;
				
				//skip instance name
				while(validcharid(str[j]))
					j = j - 1;
				
				//skip spaces on the left of instance name
				while (str[j] == ' ')
					j = j - 1;
				submodidend = j;
				
				//go to end of instantiated module name 
				while(validcharid(str[j]))
					j = j - 1;
				
				instancebeg = j + 1; 
				submodid = str.substr(j+1, submodidend - j);
		
				i = j - 1;  //i points to left of instantiation (if there would be one, otheriwse, it would be at left of ')')			
			
				//Check if the line (ended with ';') was a module instantiation, and if yes:
				//create list of cont assigns for inputs (to inputs of the callee input ports)
				//get and formate the body of the instantiated module
				//create list of cont assigns for outputs (to outputs of the caller output ports)
				//combine the above three parts and replace the module instantiated line with this.
				bool modexists = false;
				ifstream ifile((submodid+".v").c_str());
				if (ifile) 
					modexists = true;

				if (submodid != "module" && modexists) {	
					//erase comments from submodule 
					erasecommentsfile((submodid+".v").c_str());		
					//get the contents of instantiated module and remove end of line char '\n' 
					string submodule = formatinput((submodid+".v").c_str());
							
					//get ports of instantiated module 
					calleports = getports(submodule); 
		
					//get body (top list) of instantiated module
					calletoplist = gettoplist(submodule);
		
					flattened = connectinputs (locports, calleports, topmodule) + " " + calletoplist + " " +  connectoutputs (locports, calleports, topmodule);		
				
					str.replace(instancebeg, instanceend - instancebeg + 1, flattened);
				}
			}			
		}
	}	
	
	return str;
 }
 
 /*
 int main(){
	 
	 cout<<"Flattened:"<<flattening ("module other; input one; output two; assign two = one; endmodule")<<endl;
	 
	 return 0;
 } */