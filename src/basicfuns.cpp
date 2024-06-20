#include <iostream>
#include <sstream> 	//istringstream
#include <stack>
#include <fstream>

using namespace std;

//replaces a sub-string. replace strold with strnew in str (e.g., replaces all 'true' with '1'
 string replacesubstr (string str, string strold, string strnew) {
	string replaced = " ";
	int loc = 0;
	
	while (loc < str.length()) {
		int oldloc = loc;
		loc = str.find(strold, loc);
		if (loc != string::npos) {
			replaced = replaced + str.substr(oldloc, loc-oldloc) + strnew;
			//replaced.append(str.substr(oldloc, loc-oldloc)).append(strnew);
			loc = loc+strold.length();	
		}
		else 
		replaced = replaced + str.substr(oldloc, str.length()-oldloc);
	}
	return replaced;
 }

//NOTE: built-in functions 'to_string', 'stoi' could be used but that is supported only in C++11
//converts int to string
 string inttostr (int n){
	stringstream ss;
	ss << n;
	return ss.str();
 }
 
//converts string to int
 int strtoint(string str){
	istringstream buffer(str);
	int value;
	buffer >> value; 
	return value;
 }
 
 
 //check if a char is in valid Verilog identifer characters
//NOTE: escaped char in Verilog identifier should be avoided.  
bool validcharid(char c){
	string valid = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789_$";
	
	for (int i = 0; i <=valid.length(); i++)
		if (c == valid[i])
			return true;	
	return false;	
}


//Checks if a 'word' is a Verilog keyword (used for finding an identifier)
bool isverkeyword (string word){
	string keywords = "input,output,inout,wire,reg, assign, genvar, generate, endgenerate, begin, end, for, while";
	
	if (keywords.find(word)!=std::string::npos)
		return true;
	
	return false;	
}


//remove all occurrences of a char
 string removechar(char ch, string str){
	string temp;
	int size = str.length();
	
	//ignore the last null char
	for(int j = 0; j<size; j++)
    {				
		if (str[j] != ch)
			temp = temp + str[j];
	}	
	return temp;
 }
 
//Checks if a string is a number (spaces are removed)
bool isnumber (string str){
 	string digits = "0123456789";
	bool number = true;
	
	//remove spaces at begining and end (removes spaces in the middle too. Verilog compiler will not allow them anyway)
	str = removechar (' ', str);
	
	for (int i = 0; i < str.length() & number; i++)
		for (int j = 0; j < 10; j++){
				if (str[i] == digits[j]){
					number = true;
					break;
				} else number = false;
		}
		
	return number;
}

//returns the next (first) Verilog identifier in a string. 
//NOTE: it returns invalid identifiers (e.g., 0temp) as well. 
string getnextidentifier (string str) {
	string identifier = " ";
	
	for (int i=0; i<str.length(); i++) {
		if (validcharid(str[i])) {
			identifier = identifier + str[i];
			continue;
		}
		else if (!isverkeyword (identifier) & !isnumber(identifier)) {
					return identifier;
		}	
		else identifier = " ";
	}
	
	return " ";
}


//remove all spaces, and then reverse words of a sentence by delimiter ',', and
//make list and preced each word lower case command and constructor 'n' for names.
// makes lhs of tuples on the lhs Verilog assignemnt
 string reversewords (string str){
	string word; //= "\<^sub>n";
	string revwords;
	
	str = removechar (' ', str);
	
	for (int i = 0; i < str.length(); i++){
		if (str[i] != ',')
			word = word + str[i];
		else{
			revwords = "\\<^sub>n " + word + "," + revwords;	
			word = "";
		}
	}
	
	revwords = "\\<^sub>n " + word + "," + revwords;
	revwords.erase (revwords.length()-1,1);  
	revwords = "[" + revwords + "]";
	
	return revwords;
 }
 
//a string between parenthesis is part-select if there are natural numbers on right and left of ':'
bool ispartsel (string str){
	int colonpos = 0;
	for (int i = str.length() - 1; i >= 0 ; i--){
		if (str[i] == ':'){
			colonpos = i;
			break;
		}
	}
	
	return (colonpos != 0 && isnumber (str.substr(0, colonpos - 1)) && isnumber (str.substr(colonpos+1, str.length() - colonpos)));
}


//create Isabelle lower case character 
string lowercase(int i, string str){
	str.insert(i, 1, '>');	
	str.insert(i, 1, 'b');
	str.insert(i, 1, 'u');
	str.insert(i, 1, 's');
	str.insert(i, 1, '^');
	str.insert(i, 1, '<');			
	str.insert(i, 1, '\\');	
	return str;
}

 //is an operator in binary operators?
 bool isbinop (string op){
	string binops = "+,-,*,/,%,&,|,^,&,|,^,~^,+++";
	
	std::istringstream ss(binops);
	std::string token;
    
	while(std::getline(ss, token, ',')) {
		if (token == op)	
			return true;
	} 
	
	return false;
 }
 
 //is an operator in binary operators?
 bool islogop (string op){
	string logops = ">,<,<=,>=,==,!=,&&,||";
	
	std::istringstream ss(logops);
	std::string token;
    
	while(std::getline(ss, token, ',')) {
		if (token == op)	
			return true;
	} 
	
	return false;
 }
 
 //is an operator in unary operators?
 bool isunop (string op){
	string unops = "++,--,!,~";
	
	std::istringstream ss(unops);
	std::string token;
    
	while(std::getline(ss, token, ',')) {
		if (token == op)	
			return true;
	} 
	
	return false;
 }
 
//finds if [..] encloses bit part select (_[_:_]) or operator (e.g., +, &, >...)
bool isoperator(int i, string s){
	string op = s; //veriop(i, s);   //string on right side of a closing brackets
	return (isunop(op) || isbinop(op) || islogop(op) || op == ">>" || op == "<<");
}
 
 //finds a char in string
 bool findchar (char c, string str){
	for(int i = 0; i < str.length(); i++)
		if(str[i] == c)
			return true;
	return false;
 }
 
 //find if a char is a digit
 bool isdigit(char c){
	string digits = "0123456789";
	
	int i = 0;
	while (i < 10){
		if(c == digits[i])
			return true;
		i = i + 1;
	}

	return false;	
 }
 
  //erase comments (text after // and between /* */)
 string erasecomments (string str){
	string nocomments;	
	int i = 0;
	
	while (i < str.length()){
		
		//skip string after '//' till end of line
		if (str[i] == '/' && str[i+1] == '/'){
			//skip chars after // till end of line
			while (str[i] != '\n' && i < str.length())
				i = i + 1;
			i = i + 1;  //char after '\n' 
		}
		
		//skip string between /* and */
		if (str[i] == '/' && str[i+1] == '*'){
			i = i + 2;
			//skip chars between /* and */
			while (str[i] != '*' && str[i+1] != '/' && i < str.length())
				i = i + 1;
			i = i + 2;			//char after */ 
		}
		
		//add the rest of characters
		nocomments = nocomments + str[i];
		
		i = i + 1;
	}
	 
	return nocomments;
 }

//erase comments from the file 'input.txt'
 int erasecommentsfile(string input){
	 ofstream filehandle;
	 
	//read input 'input.v' file to a buffer
	std::ifstream t(input.c_str());    
	std::stringstream buffer;
	buffer << t.rdbuf();
	string text = buffer.str();
	
	//erase comments and write it back to the file 'input.v'
	text = erasecomments(text);
	filehandle.open (input.c_str());
    filehandle<<text;
    filehandle.close();
	
	return 0;
 }
 
 //replace ''' (comma) in string with a char
 string replacechar (char oldchar, char newchar, string fun) {
	for (int i=0; i < fun.length(); i++) 
		if(fun[i] == oldchar) {
			fun[i] = newchar;
		}
	
	return fun;
   }
   

bool isverilogid (string str) {
	bool isid = true;
	
	for(int i=0; i<str.length(); i++) {
		if(isdigit(str[0]) | !validcharid(str[i]))
			return false;		
	}

	return isid;
}

//searches str in list (list of words, separated by comma)
bool strlfind (string str, string strlist){
	int start = 0;
	int end = strlist.length() - 1;
	string word;
	
	for(int i=0; i<strlist.length(); i++){
		if(strlist[i] == ',' | i == strlist.length()-1) {
			word = strlist.substr(start, i-start);
			//cout<<"\nWord:"<<word<<"="<<str<<":\n";
			if (word == str)
				return true;
			start = i+1;
		}	
	}
	
	return false;

}

 //get list of all identifiers in Verilog module
string translverilogids (string module) {
    string identifier = " ";
	string names = " ";
	
	for (int i=0; i<module.length(); i++) {
			if (validcharid(module[i])) {
				identifier = identifier + module[i];
			} //'identifier' is either an identifier, number or keyword
			else { 
				identifier = removechar(' ', identifier);  //remove the initial ' ' in initialized 'identifier'
				if (isverilogid(identifier) & !isverkeyword(identifier)) {		//if identifier found
				    //if (!(names.find(identifier)!=std::string::npos)) 
					//cout<<"\nidentifier: "<<identifier;
					//cout<<"\nNames: "<<names;
					//cout<<"\nFound:"<<strlfind("temp4", names);
					
					bool found = strlfind (identifier, names);
					if (!found)
						names = names+","+identifier;
					
					//cout<<"\nFOUND:"<<found<<":"<<identifier<<":\nNames:"<<names<<":";
				}
				identifier = " ";
			}
    }
	
	if(names.length()>2)
		names = names.substr(2,names.length()-2);  //remove the intial space and comma 
		
	//read VeriCert data to buffer
	std::ifstream t("Syntax.thy");    
	std::stringstream buffer;
	buffer << t.rdbuf();
	
	string file = buffer.str();
	names = replacesubstr (names, ",", " | ");
	
	int startnames = 0;
	int endnames = 0;
	string namelist = "\n";
	
	//file = replacesubstr (file, "datatype name", "datatype name = "+ names);
		
	if (file.find("(*Begin name list*)")!=std::string::npos)
		startnames = file.find("(*Begin name list*)");
	if (file.find("(*End name list*)")!=std::string::npos)
		endnames = file.find("(*End name list*)");
	namelist = file.substr(startnames+20, endnames-startnames-20);
	file = replacesubstr (file, namelist, "datatype name = "+ names+"\n");
	//cout<<"\nNames list:"<<namelist<<":\n";
	
	//cout<<"\nSyntax file: "<<file;
	
	//append string "VeriCert output: \n" before data. 
	ofstream filehandle;
	filehandle.open ("Syntax.thy");
	filehandle << file;
    filehandle.close();
	
	
	
	return names; 
   }